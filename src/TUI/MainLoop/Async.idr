-- BSD 3-Clause License
--
-- Copyright (c) 2023, Brandon Lewis
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are met:
--
-- 1. Redistributions of source code must retain the above copyright notice, this
--    list of conditions and the following disclaimer.
--
-- 2. Redistributions in binary form must reproduce the above copyright notice,
--    this list of conditions and the following disclaimer in the documentation
--    and/or other materials provided with the distribution.
--
-- 3. Neither the name of the copyright holder nor the names of its
--    contributors may be used to endorse or promote products derived from
--    this software without specific prior written permission.
--
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
-- AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
-- IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
-- DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
-- FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
-- DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
-- SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
-- CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
-- OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
-- OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

module TUI.MainLoop.Async


import Data.ByteString
import Data.IORef
import Data.String
import public IO.Async
import public IO.Async.Channel
import IO.Async.File
import public IO.Async.Loop.Posix
import public IO.Async.Loop.Poller
import IO.Async.Loop.Epoll
import IO.Async.Posix
import IO.Async.Signal
import TUI.DFA
import TUI.Event
import TUI.Key
import TUI.MainLoop
import TUI.Painting
import TUI.UTF8
import System
import System.File.Error
import System.File.Process
import System.File.Virtual
import System.Posix.File


%default total


||| This is the type expected by `handle`.
public export
0 ErrorHandler : Type -> Type -> Type
ErrorHandler ret err = err -> Async Poll [] ret

||| Handle an error by logging it.
export
logError : Interpolation err => ErrorHandler () err
logError err = stderrLn "Unhandled error: \{err}"

||| A more convenient wrapper around handler, with explicit error list.
|||
||| `handle` doesn't work well with inline do blocks, because idris
||| can't always infer the error type.
export
handling
  :  (errs : List Type)
  -> All (ErrorHandler ret) errs
  -> Async Poll errs ret
  -> Async Poll []   ret
handling errs handlers computation  = handle handlers computation

||| A producer of events.
|||
||| This is an asynchronous computation which should post events to
||| the given event queue, which is an async `Channel`.
|||
||| While Async itself supports arbitrary errors, EventSource's should handle
||| errors internally in one of the following ways:
||| - log the error
||| - treat recoverable errors as an event, posting to the event queue.
||| - signal an unrecoverable error by closing the channel.
public export
record EventSource (evts : List Type) where
  constructor On
  thread : Channel (HSum evts) -> Async Poll [] ()

||| An event source which decodes key presses from the controlling TTY.
export covering
stdin : Has Key evts => EventSource evts
stdin = On $ go (ansiDecoder . utf8Decoder)
where
  ||| Try to read a single byte from stdin.
  |||
  ||| Generally this will work. It may return Nothing if an IO error
  ||| occurs, or if we don't get a byte back.
  getByte : Async Poll [Errno] (Maybe Bits8)
  getByte = do
    byte <- readnb Stdin ByteString 1
    case unpack byte of
      [byte] => pure $ Just byte
      _      => pure Nothing

  ||| Process bytes from stdin, stream key events into the event queue.
  |||
  ||| Stdin is read byte-by-byte, and sent through the ansi
  ||| decoder. If a key is decoded, it is sent to the event queue.
  loop : Automaton Bits8 Key -> Channel (HSum evts) -> Async Poll [Errno] ()
  loop decoder chan = case !getByte of
    Nothing => loop decoder chan
    Just byte => case next byte decoder of
      Discard => loop decoder chan
      Advance next Nothing => loop next chan
      Advance next (Just key) => do
        Sent <- send chan $ inject key | _ => pure ()
        loop next chan
      Accept Nothing => loop (reset decoder) chan
      Accept (Just key) => do
        Sent <- send chan $ inject key | _ => pure ()
        loop (reset decoder) chan
      Reject err => do
        -- XXX: how do we want to handle this?
        loop (reset decoder) chan

  ||| Put stdin in raw-mode, ensuring proper cleanup. Then enter mainloop.
  go : Automaton Bits8 Key -> Channel (HSum evts) -> Async Poll [] ()
  go decoder chan = handling [Errno] [logError] $ use1 rawMode $ \_=> do
    loop decoder chan

||| I had to split this out in order to get it to typecheck properly.
|||
||| The whole UI runs in an async fiber.
|||
||| This function should not be called in a tight loop. It's expensive
||| to set up the async mainloop.
|||
||| Any errors that are unhandled in the application shoudl implement
||| `Interpolation` so that they can be automatically logged.
covering
run
  :  {0 stateT, valueT : Type}
  -> {0 evts : List Type}
  -> (sources : List (EventSource evts))
  -> Event.Handler stateT valueT (HSum evts)
  -> (render : stateT -> Context ())
  -> stateT
  -> IO (Maybe valueT)
run srcs onEvent render state = do
  -- we need a mutable ref to store the return value,
  -- as there's no entry point for fibers that return a value.
  ret <- IORef.newIORef Nothing
  -- enter async mainloop, handling errno by logging.
  epollApp $ handling [Errno] [logError] $ do
    events  <- channel 1
    sources <- start $ race () $ spawn events <$> srcs
    loop ret state events
    cancel sources
    close events
  readIORef ret
where
  ||| The main rendering loop.
  loop
    : IORef.IORef (Maybe valueT)
    -> stateT
    -> Channel (HSum evts)
    -> Async Poll es ()
  loop ret state chan = do
    beginSyncUpdate
    clearScreen
    present (!screen).size $ do
      moveTo origin
      render state
    endSyncUpdate
    -- xxx: may need to upstream nonblocking version of this to async.
    fflush stdout
    case !(receive chan) of
      Just event => case !(liftIO $ onEvent event state) of
        Left  next => loop ret next chan
        Right res  => writeIORef ret res
      Nothing => loop ret state chan

  ||| helper function to spawn each input source.
  spawn
    :  Channel (HSum evts)
    -> (src : EventSource evts)
    -> Async Poll [] ()
  spawn chan src = src.thread chan

||| A MainLoop instance based on `async-epoll`.
|||
||| It consumes events from multiple fibers, which are written to an
||| async channel. The rendering thread reads from this channel,
||| updating the UI in response.
export
record AsyncMain (events : List Type) where
  constructor MkAsyncMain
  sources    : List (EventSource events)

||| Construct an async mainloop with the given event sources.
covering export
asyncMain
  :  Has Key evts
  => List (EventSource evts)
  -> AsyncMain evts
asyncMain sources = MkAsyncMain (stdin :: sources)

||| Implement MainLoop for AsyncMain.
export covering
{evts : List Type} -> MainLoop (AsyncMain evts) (HSum evts) where
  runRaw self onEvent render init = do
    putStrLn ""
    altScreen True
    cursor False
    saveCursor
    ret <- run self.sources onEvent render init
    cleanup
    pure ret
  where
    ||| restore terminal state as best we can
    cleanup : IO Builtin.Unit
    cleanup = do
      clearScreen
      restoreCursor
      cursor True
      altScreen False

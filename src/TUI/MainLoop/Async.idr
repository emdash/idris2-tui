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
import IO.Async.Channel
import IO.Async.File
import IO.Async.Loop.Posix
import IO.Async.Loop.Poller
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


||| An async producer of events.
public export
record EventSource (evts : List Type) where
  constructor On
  thread : Channel (HSum evts) -> Async Poll [Errno] ()

||| An event source which decodes key presses from the controlling TTY.
covering
stdin : Has Key evts => EventSource evts
stdin = On $ go (ansiDecoder . utf8Decoder)
where
  ||| Helper function to unpack a singleton ByteString.
  getByte : ByteString -> Maybe Bits8
  getByte bs = case unpack bs of
    [byte] => Just byte
    _ => Nothing

  ||| Process bytes from stdin, stream key events into the event queue.
  |||
  ||| Stdin is read byte-by-byte, and sent through the ansi
  ||| decoder. If a key is decoded, it is sent to the event queue.
  go : Automaton Bits8 Key -> Channel (HSum evts) -> Async Poll [Errno] ()
  go decoder chan = do
    byte <- readnb Stdin ByteString 1
    case getByte byte of
      Nothing => go decoder chan
      Just byte => case next byte decoder of
        Discard => go decoder chan
        Advance next Nothing => go next chan
        Advance next (Just key) => do
          Sent <- send chan $ inject key | _ => pure ()
          go next chan
        Accept Nothing => go (reset decoder) chan
        Accept (Just key) => do
          Sent <- send chan $ inject key | _ => pure ()
          go (reset decoder) chan
        Reject err => do
          -- XXX: how do I log errors?
          -- Sent <- send chan err | _ => pure ()
          go (reset decoder) chan

||| A counter event source.
|||
||| It will count down from `n`, injecting the count event. This is
||| mainly used for testing the implementation.
countSeconds : Has Nat evts => Nat -> EventSource evts
countSeconds n = On $ go n
where
  go : Nat -> Channel (HSum evts) -> Async Poll errs ()
  go 0 chan = close chan
  go n@(S k) chan = do
    Sent <- send chan $ inject n | _ => pure ()
    sleep 1.s
    go k chan

||| Try to handle an event using one of the given handlers.
|||
||| The event must be covered by one of the handlers in the list.
export
handleEvent
  :  {0 stateT, valueT : Type}
  -> HSum evts
  -> stateT
  -> All (Event.Handler stateT valueT) evts
  -> Async Poll es (Result stateT valueT)
handleEvent (Here  x)  state (h :: hs) = pure $ h x state
handleEvent (There xs) state (h :: hs) = handleEvent xs state hs


||| I had to split this out in order to get it to typecheck properly.
|||
||| The whole UI runs in an async fiber.
|||
||| This function should not be called in a tight loop. It's expensive
||| to set up the async mainloop.
covering
run
  :  {0 stateT, valueT : Type}
  -> {0 evts : List Type}
  -> List (EventSource evts)
  -> Event.Handler stateT valueT (HSum evts)
  -> (render : stateT -> Context ())
  -> stateT
  -> IO (Maybe valueT)
run srcs onEvent render state = do
  -- we need a mutable ref to store the return value,
  -- as there's no entry point for fibers that return a value.
  ret <- IORef.newIORef Nothing
  epollApp $ handle [\e => stderrLn "Error \{e}"] (go ret)
  readIORef ret
where
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
    -> Async Poll [Errno] ()
  spawn chan src = src.thread chan

  ||| Create the channel, spawn the input fibers, and begin the mainloop.
  go : IORef.IORef (Maybe valueT) -> Async Poll [Errno] ()
  go ret = use1 rawMode $ \_ => do
    events  <- channel 1
    sources <- start (race () $ (spawn events <$> srcs))
    loop ret state events

||| A MainLoop instance based on `async-epoll`.
|||
||| It consumes events from multiple fibers, which are written to an
||| async channel. The rendering thread reads from this channel,
||| updating the UI in response.
export
record AsyncMain (events : List Type) where
  constructor MkAsyncMain
  sources : List (EventSource events)

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

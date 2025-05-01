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
import System.File
import System.File.Error
import System.File.Process
import System.File.Virtual
import System.Posix.File


%default total


||| Tell TUI how to write to the console in an async context.
ConsoleOutput (Async Poll [Errno]) where
  writeStdout = fwritenb Stdout
  perror      = fwritenb Stderr . (++ "\n")

||| Tell TUI how to write to the context in plain IO.
ConsoleOutput IO where
  writeStdout = stdout
  perror      = stderrLn

||| This is the type expected by `handle`.
public export
0 ErrorHandler : Type -> Type -> Type
ErrorHandler ret err = err -> Async Poll [] ret

||| Called within an event source to post to an event queue.
public export
0 PostEventFn : List Type -> Type
PostEventFn evts = HSum evts -> Async Poll [] ()

||| A producer of events.
|||
||| This is an asynchronous computation which should post events to
||| the given event queue, which is an async `Channel`.
|||
||| While Async itself supports arbitrary errors, EventSource's should handle
||| errors internally in one of the following ways:
||| - log the error
||| - treat recoverable errors as an event, posting to the event queue.
||| - signal an unrecoverable error by returning.
public export
0 EventSource : List Type -> Type
EventSource evts = PostEventFn evts -> Async Poll [] ()

||| Handle an error by logging it.
export
logError : Interpolation err => ErrorHandler () err
logError err = File.stderrLn "Unhandled error: \{err}"

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

||| An event source which decodes key presses from the controlling TTY.
export covering
keyboard : Has Key evts => EventSource evts
keyboard = go (ansiDecoder . utf8Decoder)
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
  loop : Automaton Bits8 Key -> PostEventFn evts -> Async Poll [Errno] ()
  loop decoder post = case !getByte of
    Nothing => loop decoder post
    Just byte => case next byte decoder of
      Discard => loop decoder post
      Advance next Nothing => loop next post
      Advance next (Just key) => do
        weakenErrors $ post $ inject key
        loop next post
      Accept Nothing => loop (reset decoder) post
      Accept (Just key) => do
        weakenErrors $ post $ inject key
        loop (reset decoder) post
      Reject err => do
        -- XXX: how do we want to handle this?
        loop (reset decoder) post

  ||| Put stdin in raw-mode, ensuring proper cleanup. Then enter mainloop.
  go : Automaton Bits8 Key -> PostEventFn evts -> Async Poll [] ()
  go decoder post = handling [Errno] [logError] $ use1 rawMode $ \_=> do
    loop decoder post

||| Like epollApp, but we also allow handling of SIGWINCH.
covering
epollRun : Async Poll [] () -> IO ()
epollRun prog = do
  n <- asyncThreads
  app n [SIGINT, SIGWINCH] epollPoller cprog
where
  cprog : Async Poll [] ()
  cprog = race () [prog, dropErrs {es = [Errno]} $ onSignal SIGINT $ pure ()]

||| I had to split this out in order to get it to typecheck properly.
|||
||| The whole UI runs in an async fiber.
|||
||| This function should not be called in a tight loop. It's expensive
||| to set up the async mainloop.
|||
||| Note: parseq is used, because event sources all have the same
||| type. Some of the behavior of parseq might be undesirable,
||| however, it's a bit awkward to call `par` on a homogeneous list.
covering
run
  :  {0 stateT, valueT : Type}
  -> {0 evts : List Type}
  -> (sources : List (EventSource evts))
  -> Event.Handler stateT valueT (HSum evts)
  -> (render : Rect -> stateT -> Context ())
  -> stateT
  -> IO (Maybe valueT)
run srcs onEvent render state = do
  -- we need a mutable ref to store the return value,
  -- as there's no entry point for fibers that return a value.
  ret    <- IORef.newIORef Nothing
  window <- screen
  -- enter async mainloop, handling errno by logging.
  epollRun $ handling [Errno] [logError] $ do
    events   <- channel 10
    -- see note about parseq, above.
    sources  <- start $ parseq $ spawn events <$> srcs
    sigwinch <- start $ winch_watch events
    loop ret window state events
    cancel sources
    cancel sigwinch
    close events
  readIORef ret
where
  postEvent : Channel (Either Rect (HSum evts)) -> PostEventFn evts
  postEvent chan event = do
    case !(send chan $ Right event) of
      Sent => pure ()
      _    => pure ()

  ||| Watch for sigwinch, updating the window size when it is received.
  |||
  ||| This avoids having to issue the ioctl before every frame, as is
  ||| done in the non-async mainloop.
  winch_watch : Channel (Either Rect (HSum evts)) -> Async Poll [Errno] ()
  winch_watch chan = do
    ignore $ awaitSignals [SIGWINCH]
    Sent <- send chan $ Left !screen | _ => pure ()
    winch_watch chan

  ||| The main rendering loop.
  loop
    :  IORef.IORef (Maybe valueT)
    -> Rect
    -> stateT
    -> Channel (Either Rect (HSum evts))
    -> Async Poll [Errno] ()
  loop ret window state chan = do
    beginSyncUpdate
    clearScreen
    present window.size $ do
      moveTo origin
      render window state
    endSyncUpdate
    -- xxx: may need a nonblocking version of this in async.
    --
    -- note: it seems to work without this line, but I will leave it in here
    -- as a breadcrumb in case issues with this crop up in the future.
    --
    -- fflush stdout
    case !(receive chan) of
      Nothing            => pure ()
      Just (Left window) => loop ret window state chan
      Just (Right event) => case !(liftIO $ onEvent event state) of
        Left  next => loop ret window next chan
        Right res  => writeIORef ret res

  ||| helper function to spawn each input source.
  spawn
    :  Channel (Either Rect (HSum evts))
    -> (src : EventSource evts)
    -> Async Poll [] ()
  spawn chan src = src $ postEvent chan

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
|||
||| The `keyboard` handler will be automatically added, so do not add
||| it explicitly.
covering export
asyncMain
  :  Has Key evts
  => List (EventSource evts)
  -> AsyncMain evts
asyncMain sources = MkAsyncMain (keyboard :: sources)

||| Implement MainLoop for AsyncMain.
export covering
{evts : List Type} -> MainLoop (AsyncMain evts) (HSum evts) where
  runRaw self onEvent render init = do
    -- XXX: this shouldn't be necessary, but the async raw mode
    -- idiom isn't working. We'll leave it like this for now.
    Right _ <- enableRawMode | _ => die "Couldn't set raw mode on stdin!"
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
      -- XXX: this shouldn't be necessary, but the async raw mode
      -- idiom isn't working. We'll leave it like this for now.
      resetRawMode

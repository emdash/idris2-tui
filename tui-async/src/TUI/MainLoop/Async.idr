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

||| A fallible async computation within an application.
public export
0 Throws : List Type -> Type -> Type
Throws errs retT = Async Poll errs retT

||| An infallible async computation within an application.
public export
0 NoExcept : Type -> Type
NoExcept retT = Throws [] retT

||| Handle an exception within an async computation.
public export
0 Catch : Type -> Type -> Type
Catch retT errorT = errorT -> NoExcept retT

||| Try to perform a computation, handling all errors to produce a pure result.
|||
||| This is intended to be used with a matching where clause, like so:
|||
|||    try [onErrno] $ do
|||       ...
|||    where
|||      onErrno : Catch () Errno
|||      onErrno errno = ...
|||
||| ...which starts to feels like exceptions.
export
try : All (Catch retT) es -> Throws es retT -> NoExcept retT
try handlers fallible = handle handlers fallible

||| The opaque type of the event queue.
|||
||| This is an async `Channel`, but we hide the true type here to
||| minimize breaking changes as things evolve, and provide a simpler,
||| safer API.
|||
||| Exposing the channel allows external event sources to shut down
||| the entire app by closing the channel.
export
0 EventQueue : List Type -> Type
-- the Left constructor of the either is used internally to respond to
-- SIGWINCH. The right constructor is for events.
EventQueue tys = Channel (Either Rect (HSum tys))

||| Post an event to an event queue.
|||
||| This is intended to be called by custom event sources within an
||| application.
export
putEvent
  :  {0 eventT : Type}
  -> {0 evts   : List Type}
  -> Has eventT evts
  => EventQueue evts
  -> eventT
  -> NoExcept ()
putEvent queue event = case !(send queue $ Right $ inject event) of
  _ => pure ()

||| Used internally to post window sizes to the event queue.
putWin : EventQueue _ -> Rect -> NoExcept ()
putWin queue rect = case !(send queue $ Left rect) of
  _ => pure ()

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
EventSource evts = EventQueue evts -> NoExcept ()

||| A more convenient wrapper around `handle`, with explicit error
||| list.
|||
||| `handle` doesn't work well with inline do blocks, because idris
||| can't always infer the error type.
export
handling
  :  (errs : List Type)
  -> All (Catch retT) errs
  -> Throws errs retT
  -> NoExcept retT
handling errs handlers computation  = handle handlers computation

||| The keyboard event source.
|||
||| Stdin must already be placed in raw mode, or this will not work
||| correctly.
export covering
keyboard : Has Key evts => EventSource evts
keyboard queue = try [onErrno] $ do
  loop (ansiDecoder . utf8Decoder)
where
  ||| Try to read a single byte from stdin.
  |||
  ||| Generally this will work. It may return Nothing if an IO error
  ||| occurs, or if we don't get a byte back.
  getByte : Throws [Errno] (Maybe Bits8)
  getByte = do
    byte <- readnb Stdin ByteString 1
    case unpack byte of
      [byte] => pure $ Just byte
      _      => pure Nothing

  ||| Process bytes from stdin, stream key events into the event queue.
  |||
  ||| Stdin is read byte-by-byte, and sent through the ansi
  ||| decoder. If a key is decoded, it is sent to the event queue.
  loop : Automaton Bits8 Key -> Throws [Errno] ()
  loop decoder = case !getByte of
    Nothing => loop decoder
    Just byte => case next byte decoder of
      Discard => loop decoder
      Advance next Nothing => loop next
      Advance next (Just key) => do
        weakenErrors $ putEvent queue key
        loop next
      Accept Nothing => loop (reset decoder)
      Accept (Just key) => do
        weakenErrors $ putEvent queue key
        loop (reset decoder)
      Reject err => do
        -- XXX: how do we want to handle this?
        loop (reset decoder)

  ||| Handle errors reading from stdin.
  onErrno : Catch () Errno
  onErrno err = File.stderrLn "Error reading from stdin: \{err}"

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
  epollApp {sigs = [SIGINT, SIGWINCH]} $ try [onErrno] $ do
    events   <- channel 10
    -- see note about parseq, above.
    sources  <- start $ parseq $ spawn events <$> (sigwinch :: srcs)
    loop ret window state events
    cancel sources
    close events
  readIORef ret
where
  onErrno : Catch () Errno
  onErrno err = File.stderrLn "Unhandled IO error, exiting: \{err}"

  ||| Watch for sigwinch, updating the window size when it is received.
  |||
  ||| This avoids having to issue the ioctl before every frame, as is
  ||| done in the non-async mainloop.
  sigwinch : EventQueue _ -> NoExcept ()
  sigwinch events = try [onErrno] loop
    where
      loop : Throws [Errno] ()
      loop = do
        ignore $ awaitSignals [SIGWINCH]
        weakenErrors $ putWin events !screen
        loop

      onErrno : Catch () Errno
      onErrno err = File.stderrLn "Error awaiting SIGWINCH"

  ||| spawn an input source as an async fiber.
  |||
  ||| since these are just functions of the event queue, it's
  ||| basically a flipped `apply`.
  spawn
    :  EventQueue evts
    -> (src : EventSource evts)
    -> NoExcept ()
  spawn chan src = src chan

  ||| The main rendering loop.
  loop
    :  IORef.IORef (Maybe valueT)
    -> Rect
    -> stateT
    -> EventQueue evts
    -> Throws [Errno] ()
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
  -- XXX: how to make sure we don't get a second instance of
  -- `keyboard`?
  -- note: there's nothing intrinsically wrong with having multiple
  -- `Key` input sources. e.g. we might have a second keyboard-like
  -- input device, such as a serial barcode scanner, and we might not
  -- bother to distinguish between them.
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

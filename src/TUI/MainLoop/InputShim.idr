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

||| This mainloop mainloop stack reads line-separated JSON records
||| from stdin.
|||
||| Use this with an external program to drive the UI for testing,
||| debugging, or other exotic uses. See `input-shim.py` and `run.sh`
||| for an example.
|||
||| The other advantage to this MainLoop is that it only depends on base.
module TUI.MainLoop.InputShim


import Data.IORef
import Data.List
import Data.List.Quantifiers
import Data.List.Quantifiers.Extra
import System.File.Process
import System.File.ReadWrite
import System.File.Virtual
import TUI.DFA
import TUI.Event
import TUI.Key
import TUI.MainLoop
import TUI.Painting


%default total


ConsoleOutput IO where
  writeStdout = Prelude.IO.putStr
  perror      = ignore . (fPutStrLn stderr)


||| Decodes the given event type from Stdin.
|||
||| The tag identifies the event type, whose contents are then decoded
||| from JSON. The resulting Idris value is then passed to a decoder
||| state machine.
export
record EventSource eventT where
  constructor On
  0 RawEventT : Type
  tag         : String
  {auto impl  : FromJSON RawEventT}
  decoder     : IORef $ Automaton RawEventT eventT

||| A MainLoop which receive events as a stream of JSON records on STDIN.
|||
||| An external process is responsible for collecting events and
||| passing them to the application. See `input-shim.py` for an example.
|||
||| This MainLoop instance is useful for testing and debugging.
|||
||| XXX: this code is a bit more general than necessary at the
||| moment. It looks as if it supports multiple distinct event types,
||| however, it doesn't.
export
record InputShim (events : List Type) where
  constructor MkInputShim
  sources : All EventSource events

||| Construct an EventSource for an event that must be further decoded.
export
decoded
  :  {0 rawEventT, eventT : Type}
  -> FromJSON rawEventT
  => String
  -> (decoder : Automaton rawEventT eventT)
  -> IO (EventSource eventT)
decoded tag decoder = pure $ On {
  RawEventT = rawEventT,
  tag       = tag,
  decoder   = !(newIORef decoder)
}

||| Construct an event source for an event that can be used directly.
export
raw
  :  {0 eventT : Type}
  -> FromJSON eventT
  => String
  -> IO (EventSource eventT)
raw tag = decoded tag identity

||| An event source which decodes raw `Char`s into `Key` values.
export
onAnsiKey : IO (EventSource Key)
onAnsiKey = decoded "Stdin" ansiDecoder

||| Add an event source to an InputShim mainloop.
export
(.addEvent)
  :  {0 events : List Type}
  -> InputShim events
  -> EventSource eventT
  -> InputShim (eventT :: events)
(.addEvent) self source = {sources $= (source ::)} self

||| A MainLoop which handles only ANSI key sequences.
|||
||| You must use at least this value as your initial mainloop. You can
||| add custom events to it via (.addEvent) defined above.
export
inputShim : IO (InputShim [Key])
inputShim = pure $ MkInputShim [!onAnsiKey]

||| Decode the top-level record in the given JSON.
|||
||| XXX: Probably the JSON package can work with HSum more directly,
||| but I didn't want to go down that rabbit hole, so I wrote it
||| manually.
match : FromJSON a => String -> JSON -> Either String a
match expected (JObject [
  ("tag", JString got),
  ("contents", (JArray [rest]))
]) =
  if expected == got
  then case fromJSON rest of
    Left err => Left $ show err
    Right v  => Right v
  else Left "Incorrect tag"
match _ _ = Left "Wrong shape"

||| Try each handler in succession until one decodes an event.
|||
||| Returns the event as an HSum over all the event sources.
export
decodeNext
  :  String
  -> All EventSource events
  -> IO $ Either String (HSum events)
decodeNext e sources = case parseJSON Virtual e of
    Left  err    => pure $ Left "Parse Error: \{show err}"
    Right parsed => loop parsed sources
where
  loop
    : JSON
    -> All EventSource a
    -> IO (Either String (HSum a))
  loop parsed []        = pure $ Left "Unhandled event: \{e}"
  loop parsed (x :: xs) = case match @{x.impl} x.tag parsed of
      Left  err => pure $ There <$> !(loop parsed xs)
      Right evt => case next evt !(readIORef x.decoder) of
        Discard  => pure $ Left "Event discarded."
        Advance state output => do
          writeIORef x.decoder state
          case output of
            Nothing     => pure $ Left "No event decoded."
            Just event  => pure $ Right $ inject event
        Accept y => pure $ Left $ "Toplevel event decoder in final state!"
        Reject err => pure $ Left "Decode error: \{err}"

export covering
{events : List Type} -> MainLoop (InputShim events) (HSum events) where
  runRaw self onEvent render init = do
    -- input-shim.py must put the terminal in raw mode
    putStrLn ""
    altScreen True
    cursor False
    saveCursor
    ret <- loop self.sources init
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

    ||| The actual main loop
    loop : All EventSource events -> stateT -> IO (Maybe valueT)
    loop sources state = do
      beginSyncUpdate
      clearScreen
      window <- screen
      present window.size $ do
        -- all drawing operations now live in the `Context` monad,
        -- so they must be nested under the `present` IO action.
        moveTo origin
        render window state
      endSyncUpdate
      fflush stdout
      next <- getLine
      case !(decodeNext next self.sources) of
        Right event => case !(onEvent event state) of
          Left  next => loop sources next
          Right res  => pure res
        Left err     => do
          perror $ show err
          loop sources state


||| Special case for a singleton set of events.
export covering
{eventT : Type} -> MainLoop (InputShim [eventT]) eventT where
  runRaw self handler render init = runRaw self (union [handler]) render init

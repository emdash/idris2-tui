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


import Data.Bits
import Data.ByteString
import Data.Nat
import Data.SnocList
import Data.String
import Data.Vect
import IO.Async.File
import IO.Async.Loop.Posix
import IO.Async.Loop.Poller
import IO.Async.Loop.Epoll
import IO.Async.Channel
import IO.Async.Posix
import IO.Async.Signal
import TUI.DFA
import TUI.Event
import System
import System.File.Error
import System.Posix.File


%default total


mask : Num a => Neg a => Bits a => Index {a = a} -> a
mask bits = (bit bits) - 1

(.maskHigh) : Num a => Neg a => Bits a => a -> Index {a = a} -> a
(.maskHigh) x bits = shiftR (x .&. (complement $ mask bits)) bits

(.maskLow) : Num a => Neg a => Bits a => a -> Index {a = a} -> a
(.maskLow) x bits = x .&. (mask bits)

(.split) : Num a => Neg a => Bits a => a -> Index {a = a} -> (a, a)
(.split) x bits = (x.maskHigh bits, x.maskLow bits)

(.shiftIn) : Num a => Neg a => Bits a => Bits b => Cast b a => a -> Index {a = a} -> b -> a
(.shiftIn) x n bits = (shiftL x n) .|. ((cast bits).maskLow n)


||| A byte in a UTF-8 Sequence
|||
||| A unicode byte is either valid 7-bit ascii, a multi-byte sequence
||| introducer, a continuation byte, or one of several known invalid
||| bit patterns.
|||
||| A multi-byte sequence can be 2 to 4 bytes long, including the introducer.
data UTF8Byte : Type where
  ||| A valid ascii byte.
  Ascii        : Bits8 -> UTF8Byte
  ||| Start of multi-byte sequence, including the first bits of the codepoint.
  |||
  ||| @k indicates the remaining bytes to decode
  SeqIntro     : (k: Nat) -> (0 _ : LTE (S k) 3) -> Bits8 -> UTF8Byte
  ||| A continuation byte, with the next 6 bits of the codepoint.
  Continuation : Bits8 -> UTF8Byte
  ||| Any of several invalid bit-patterns.
  InvalidByte  : Bits8 -> UTF8Byte

||| UTF8 Decoder State.
data UTF8State : Type where
  ||| The start state of the decoder.
  Default : UTF8State
  ||| A partially-decoded multi-byte character
  ByteSeq : (len : Nat)
         -> (0 _ : LTE len 3)
         -> (n : Fin len)
         -> Int
         -> UTF8State

seqIntro
  :  (len : Nat)
  -> {auto 0 _ : LTE len 3}
  -> {auto 0 _ : IsSucc len}
  -> Bits8
  -> UTF8Byte
seqIntro (S k) @{ltelen} @{succlen} b = SeqIntro k ltelen b

seqStart
  :  (len : Nat)
  -> {auto 0 _ : IsSucc len}
  -> {auto 0 _ : LTE len 3}
  -> Bits8
  -> UTF8State
seqStart len@(S k) @{isSucc} @{bounded} b = ByteSeq len (bounded) last (cast b)


classify : Bits8 -> UTF8Byte
classify byte = case byte.split 7 of
  (0b0, char) => Ascii char
  _ => case byte.split 6 of
   (0b10, rest) => Continuation rest
   _ => case byte.split 5 of
     (0b110, rest) => seqIntro 1 rest
     _ => case byte.split 4 of
       (0b1110, rest) => seqIntro 2 rest
       _ => case byte.split 3 of
         (0b11110, rest) => seqIntro 3 rest
         _ => InvalidByte byte

transition : TransitionFn UTF8State UTF8Byte Char
transition (Ascii b) Default = Accept $ Just $ chr $ cast b
transition (SeqIntro k _ b) Default = Advance (seqStart (S k) b) $ Nothing
transition (Continuation b) (ByteSeq l p n c) = case n of
  FZ   => Accept $ Just $ chr $ cast (c.shiftIn 6 b)
  FS n => Advance (ByteSeq l p (weaken n) (c.shiftIn 6 b)) Nothing
transition _                 _       = Reject "Invalid Byte Sequence"

unicodeDecoder : Automaton Bits8 Char
unicodeDecoder = loop $ 
automaton Default decode
  where
    decode : TransitionFn UTF8State Bits8 Char
    decode byte state = transition (classify byte) state

testByteSeqs : List (List Bits8)
testByteSeqs = [
  [97],
  [199, 164],
  [225, 184, 146],
  [226, 147, 128],
  [227, 130, 128],
  [240, 159, 156, 184]
]

{-
testChars : List (Maybe Char)
testChars = [
  Just $ 'a',
  Just $ chr 0x01e4,
  Just $ chr 0x1e12,
  Just $ chr 0x24c0,
  Just $ chr 0x3080,
  Just $ chr 0x1F738
]

countSeconds : Nat -> Channel String -> Async Poll es ()
countSeconds 0 chan = do
  _ <- send chan "Timer Expired"
  close chan
countSeconds (S k) chan = do
  Sent <- send chan "\{show $ S k} s left" | _ => pure ()
  sleep 1.s
  countSeconds k chan

covering
stdin : Has Errno es => Channel String -> Async Poll es ()
stdin chan = do
  bytes <- readnb Stdin ByteString 4
  resp <- case decodeUTF8 $ unpack bytes of
    Nothing => send chan $ "Invalid byte sequence \{show bytes}"
    Just char => send chan $ singleton char
  case resp of
    Sent => stdin chan
    _ => pure ()

covering
mainloop : Channel String -> Async Poll es ()
mainloop chan = do
  Just msg <- receive chan | _ => pure ()
  stdoutLn $ show msg
  mainloop chan

export covering
main : IO ()
main = epollApp $ handle [\e => stderrLn "Error \{e}"] run
where
  run : Async Poll [Errno] ()
  run = use1 rawMode $ \_ => do
    chan <- channel 1
    race () [
      stdin chan,
      countSeconds 10 chan,
      guarantee (mainloop chan) $ do
        stderrLn "timer exited"
        mainloop chan
    ]

{-

import TUI.DFA
import TUI.Event
import TUI.Key
import TUI.MainLoop
import TUI.Painting

%default total


{-
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

||| A MainLoop which handles only Ansi keys
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

||| Try to handle an event using one of the given handlers.
|||
||| The event must be covered by one of the handlers in the list.
export
handleEvent
  :  {0 stateT, valueT : Type}
  -> HSum events
  -> stateT
  -> All (Handler stateT valueT) events
  -> Result stateT valueT
handleEvent (Here  x)  state (h :: hs) = h x state
handleEvent (There xs) state (h :: hs) = handleEvent xs state hs

export covering
MainLoop (InputShim [Key]) where
  runRaw self onKey render init = do
    -- input-shim.py must put the terminal in raw mode
    putStrLn ""
    altScreen True
    cursor False
    saveCursor
    ret <- loop [onKey] init
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
    loop : All (Handler stateT valueT) [Key] -> stateT -> IO (Maybe valueT)
    loop handlers state = do
      beginSyncUpdate
      clearScreen
      present (!screen).size $ do
        -- all drawing operations now live in the `Context` monad,
        -- so they must be nested under the `present` IO action.
        moveTo origin
        render state
      endSyncUpdate
      fflush stdout
      next <- getLine
      case !(decodeNext next self.sources) of
        Right event => case !(handleEvent event state handlers) of
          Left  next => loop handlers next
          Right res  => pure res
        Left err     => do
          ignore $ fPutStrLn stderr $ show err
          loop handlers state

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
import Data.String
import IO.Async.File
import IO.Async.Loop.Posix
import IO.Async.Loop.Poller
import IO.Async.Loop.Epoll
import IO.Async.Channel
import IO.Async.Posix
import IO.Async.Signal
import TUI.DFA
import TUI.Event
import TUI.Key
import TUI.MainLoop
import TUI.Painting
import System
import System.File.Error
import System.Posix.File


%default total


||| Generate a mask with the first `n` bits set.
maskLow : Num a => Neg a => Bits a => Index {a = a} -> a
maskLow bits = (bit bits) - 1

||| Get the right bits from x, splitting at the given bit index.
(.splitRight) : Num a => Neg a => Bits a => a -> Index {a = a} -> a
(.splitRight) x bits = x .&. (maskLow bits)

||| Get the left bits from x, splitting at the given bit index.
(.splitLeft) : Num a => Neg a => Bits a => a -> Index {a = a} -> a
(.splitLeft) x bits = shiftR (x .&. (complement $ maskLow bits)) bits

||| Split x into two bit patterns at the given bit index.
(.split) : Num a => Neg a => Bits a => a -> Index {a = a} -> (a, a)
(.split) x bits = (x.splitLeft bits, x.splitRight bits)

||| Shift `n` bits from `src` into `x` from the right.
(.shiftIn) : Num a => Neg a => Bits a => Bits b => Cast b a => a -> Index {a = a} -> b -> a
(.shiftIn) x n src = (shiftL x n) .|. ((cast src).splitRight n)


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

||| Helper to construct a sequence intro byte.
|||
||| The required proofs are captured by proof search.
seqIntro
  :  (len : Nat)
  -> {auto 0 _ : LTE len 3}
  -> {auto 0 _ : IsSucc len}
  -> Bits8
  -> UTF8Byte
seqIntro (S k) @{ltelen} @{succlen} b = SeqIntro k ltelen b

||| Helper to construct a sequence start decoder state.
|||
||| The required proofs are captured by proof search.
seqStart
  :  (len : Nat)
  -> {auto 0 _ : IsSucc len}
  -> {auto 0 _ : LTE len 3}
  -> Bits8
  -> UTF8State
seqStart len@(S k) @{isSucc} @{bounded} b = ByteSeq len (bounded) last (cast b)

||| UTF8 Decoder
export
utf8Decoder : Automaton Bits8 Char
utf8Decoder = loop $ automaton Default transition
where
  ||| Classify a byte according to the UTF8 standard.
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

  ||| Errors in the input stream will be replaced with this codepoint.
  replace : Maybe Char
  replace = Just $ chr 0xFFFD

  ||| UTF8 Decoder Transition function
  |||
  ||| XXX: this treats a sequence like E1 A0 20 as a single error.
  transition : TransitionFn UTF8State Bits8 Char
  transition byte state with (classify byte) | (state)
    _ | (InvalidByte b)  | _       = Accept replace
    _ | (Ascii b)        | Default = Accept $ Just $ chr $ cast b
    _ | (SeqIntro k _ b) | Default = Advance (seqStart (S k) b) $ Nothing
    _ | (Continuation b) | (ByteSeq l p n c) = case n of
      FZ   => Accept $ Just $ chr $ cast (c.shiftIn 6 b)
      FS n => Advance (ByteSeq l p (weaken n) (c.shiftIn 6 b)) Nothing
    _ | _                |  _ = Accept replace


||| XXX: keep these here until I get around to writing proper test cases.
testByteSeqs : List (List Bits8)
testByteSeqs = [
  [97],                  -- "a"
  [199, 164],            -- "\484"
  [225, 184, 146],
  [226, 147, 128],
  [227, 130, 128],
  [240, 159, 156, 184],
  [240, 159, 97, 184],
  [97, 184],
  [0xE1, 0xA0, 0x20] -- xxx: failing, treats as single error.
  -- xxx: need *many* more test cases.
]

||| XXX: keep this around until I get around to writing proper test cases.
testChars : List (Maybe Char)
testChars = [
  Just $ 'a',
  Just $ chr 0x01e4,
  Just $ chr 0x1e12,
  Just $ chr 0x24c0,
  Just $ chr 0x3080,
  Just $ chr 0x1F738
]

record EventSource (evts : List Type) where
  constructor On
  eventT : Type
  thread : Channel (HSum evts) -> Async Poll [Errno] ()

covering
stdin : Has Key evts => EventSource evts
stdin = On Key $ go (ansiDecoder . utf8Decoder)
where
  getByte : ByteString -> Maybe Bits8
  getByte bs = case unpack bs of
    [byte] => Just byte
    _ => Nothing

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

countSeconds : Has Nat evts => Nat -> EventSource evts
countSeconds n = On Nat $ go n
where
  go : Nat -> Channel (HSum evts) -> Async Poll errs ()
  go 0 chan = close chan
  go n@(S k) chan = do
    Sent <- send chan $ inject n | _ => pure ()
    sleep 1.s
    go k chan

covering
run : All Show evts => List (EventSource evts) -> IO ()
run srcs = epollApp $ handle [\e => stderrLn "Error \{e}"] go
where
  render : Channel (HSum evts) -> Async Poll es ()
  render chan = do
    Just msg <- receive chan | _ => pure ()
    stdoutLn $ show msg
    render chan

  spawn
    :  Channel (HSum evts)
    -> (src : EventSource evts)
    -> Async Poll [Errno] ()
  spawn chan src = src.thread chan

  renderThread : Channel (HSum evts) -> Async Poll [Errno] ()
  renderThread chan = guarantee (render chan) $ do
    stderrLn "timer exited"
    render chan

  go : Async Poll [Errno] ()
  go = use1 rawMode $ \_ => do
    chan <- channel 1
    race () (render chan :: (spawn chan <$> srcs))

export covering
main : IO ()
main = run sources
  where
    sources : List (EventSource [Key, Nat])
    sources = [stdin, countSeconds 10]

{-
export
record AsyncMain (errs : List Type) (events : List Type) where
  constructor MkAsyncMain
  sources : List (EventSource errs events)

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
MainLoop (AsyncMain [Errno] [Key]) where
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

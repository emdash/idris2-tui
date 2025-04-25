||| A constant-space UTF8 decoder implemented as a DFA.
module TUI.UTF8


import Data.Bits
import TUI.DFA


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
  ||| the issue is that this version of DFA can't easily emit multiple
  ||| output values for a single input token, and can't backtrack.
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

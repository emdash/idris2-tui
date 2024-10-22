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

||| A Numeric Input Widget
module TUI.Component.Numeric


import Data.Fin
import Data.String
import Data.SnocList
import TUI.Component
import TUI.Component.Editor
import TUI.Util


%default total


||| The set of symbols we accept.
export
data Input
  = Digit (Fin 10)
  | Dot
  | Minus

||| A sequence of digits representing a valid positive number.
data Digits
  = Integral (SnocList (Fin 10))
  | Decimal  (SnocList (Fin 10)) (SnocList (Fin 10))


||| A component for numeric input:
|||
||| Ignores non-numeric keypresses, and cannot hold a non-numeric
||| value.
|||
||| Other features include:
||| - press `-` at any time to swap sign.
||| - dot ignored after first press.
||| - backspace clears whole field.
||| - TBD: increment / decrement actions.
export
record Numeric a where
  constructor N
  digits : Digits
  sign   : Bool

||| Convert a character to a digit for event handling.
charToDigit : Char -> Maybe (Fin 10)
charToDigit char = integerToFin (cast $ ord char - ord '0') 10

||| Convert a digit to a character.
digitToChar : Fin 10 -> Char
digitToChar d = cast $ (ord '0') + cast (finToNat d)

||| Insert a single digit value.
insertDigits : Fin 10 -> Digits -> Digits
insertDigits d (Integral ds)  = Integral (ds :< d)
insertDigits d (Decimal i ds) = Decimal  i (ds :< d)

||| An empty digits value.
export empty : Digits ; empty = Integral [<]

||| Convert a digit string to a string
digitsToString : Digits -> String
digitsToString self = case self of
  Integral   ds => impl ds
  Decimal  i ds => "\{impl i}.\{impl ds}"
  where
    impl : SnocList (Fin 10) -> String
    impl [<] = "0"
    impl xs  = kcap $ digitToChar <$> xs

||| Get the width of the entire control, including symbols and padding.
export
width : Digits -> Nat
width (Integral  ds)    = 3 + length ds
width (Decimal   is ds) = max 6 (3 + length is + 1 + length ds)

||| Insert a single digit.
export
insert : Input -> Numeric a -> Numeric a
insert (Digit d) self = { digits $= insertDigits d } self
insert Dot       self = case self.digits of
  Integral ds   => { digits := Decimal ds [<] } self
  Decimal  _  _ => self
insert Minus     self = { sign $= not } self

||| Clear the input field.
export
clear : Numeric a -> Numeric a
clear = { digits := empty }

||| Toggle the sign of the input
export
negate : Numeric a -> Numeric a
negate = { sign $= not }

||| Get a string representation of the component.
export
toString : Numeric a -> String
toString self = if self.sign
  then "-\{digitsToString self.digits}"
  else " \{digitsToString self.digits}"

||| Generic paint function for all variants of numeric widget.
paintNumeric : Char -> State -> Rect -> Numeric a -> Context ()
paintNumeric symbol state window self = do
  showCharAt window.nw symbol
  case state of
      Focused => reverseVideo
      _       => pure ()
  showTextAt (window.nw + MkArea 2 0) (toString self)
  sgr [Reset]

||| Interface for supported numeric types.
export
interface Show a => Supported a where
  (.value)    : Numeric a -> Maybe a
  symbol      : Char
  charToInput : Char -> Maybe Input
  zero        : a

export
Supported Nat where
  (.value)       = parsePositive . toString
  symbol         = cast 0x2115
  charToInput c  = Digit <$> charToDigit c
  zero           = 0

export
Supported Integer where
  (.value)        = parseInteger . toString
  symbol          = cast 0x2124
  charToInput '-' = Just Minus
  charToInput c   = Digit <$> charToDigit c
  zero            = 0

export
Supported Double where
  (.value)        = parseDouble . toString
  symbol          = cast 0x211d
  charToInput '-' = Just Minus
  charToInput '.' = Just Dot
  charToInput c   = Digit <$> charToDigit c
  zero            = 0

||| Handle a supported keypress.
handleChar : Supported a => Char -> Numeric a -> IO $ Response (Numeric a) a
handleChar char self = case charToInput {a = a} char of
  Nothing => ignore
  Just i  => update $ insert i self


||| Create a numeric widget from a number value.
export
new : Supported a => Numeric a
new = N {
  digits   = empty, -- xxx: decode
  sign     = False
}

export
fromValue : Supported a => a -> Numeric a
fromValue v = fromString new $ unpack $ show v
  where
    fromString : Numeric a -> List Char -> Numeric a
    fromString self [] = self
    fromString self (x :: xs) = case charToInput {a = a} x of
      Nothing => fromString self xs
      Just i => insert i $ fromString self xs

||| Implement Model for supported number types.
export
Supported a => View (Numeric a) where
  size self = MkArea (width self.digits) 1
  paint state window self = paintNumeric (symbol {a = a}) state window self

||| Implement Model for supported number types.
export
handle : Supported a => Component.Handler (Numeric a) a Key
handle (Alpha char) self = handleChar char self
handle Delete       self = update $ clear self
handle Left         self = exit
handle Enter        self = exitWith self.value
handle Escape       self = exit
handle _            self = ignore

export
numeric : Supported a => a -> Component a
numeric value = component (Numeric.fromValue value) handle (.value)

export
%hint
editableImpl : Show a => Supported a => Editable a
editableImpl = MkEditable @{show} {
  fromValue = numeric,
  blank     = numeric zero
}

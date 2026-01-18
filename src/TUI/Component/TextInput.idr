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

||| A Component for editing short, single-line strings of text.
module TUI.Component.TextInput


import Data.String
import TUI.Component
import TUI.Component.Editor
import TUI.Util
import TUI.Zipper.List


%default total


||| An Editable String View.
export
record TextInput where
  constructor TI
  chars     : Zipper Char

||| Construct an empty text input
export
empty : TextInput
empty = TI empty

||| Construct a text input from a string.
export
fromString : String -> TextInput
fromString s = TI $ fromList $ unpack s

||| get the string value from the text input.
export
toString : TextInput -> String
toString self = pack $ toList self.chars

export
delete : TextInput -> TextInput
delete = {chars $= delete}

export
goLeft : TextInput -> TextInput
goLeft = {chars $= goLeft}

export
goRight : TextInput -> TextInput
goRight = {chars $= goRight}

export
insert : Char -> TextInput -> TextInput
insert c = {chars $= insert c}

||| Implement View for TextInput
export
View TextInput where
  -- Size is the sum of left and right halves
  size self = MkArea (length self.chars + 1) 1

  -- when un-focused, just show the string value.
  paint Normal rect self = do
    showTextAt rect.nw (toString self)
  -- when disabled, show a faint string
  paint Disabled rect self = do
    sgr [SetStyle Faint]
    showTextAt rect.nw (toString self)
    sgr [Reset]
  -- when focused, show the cursor position in the string.
  paint Focused rect self = do
    showTextAt rect.nw $ kcap $ self.chars.left
    sgr [SetReversed True]
    putStr $ case self.chars.right of
      [] => " "
      x :: _ => singleton x
    sgr [SetReversed False]
    putStr $ pack $ tail self.chars.right

||| Implement Component for TextInput.
export
onKey : Single.Handler TextInput String Key
onKey Left      self = update $ goLeft self
onKey Right     self = update $ goRight self
onKey Delete    self = update $ delete self
onKey (Alpha c) self = update $ insert c self
onKey Enter     self = yield $ toString self
onKey Escape    self = exit
onKey _         self = ignore

export
textInput
  :  {0 events : List Type}
  -> Has Key events
  => String
  -> Component (HSum events) String
textInput string = component (fromString string) (only onKey) (Just . toString)

||| Make `String` `Editable` via `TextInput`
export
{0 events : List Type} -> Has Key events => Editable events String where
  fromValue = textInput {events}
  blank     = textInput {events} ""

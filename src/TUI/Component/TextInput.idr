||| Minimalist terminal UI Framework
|||
||| A Component for editing text.
module TUI.Component.TextInput


import Data.String
import TUI.Component
import TUI.Component.Editor
import Util
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
delete : TextInput -> Update TextInput
delete = {chars $= delete}

export
goLeft : TextInput -> Update TextInput
goLeft = {chars $= goLeft}

export
goRight : TextInput -> Update TextInput
goRight = {chars $= goRight}

export
insert : Char -> TextInput -> Update TextInput
insert c = {chars $= insert c}

||| Implement View for TextInput
export
View TextInput where
  -- Size is the sum of left and right halves
  size self = MkArea (length self.chars) 1

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
    reverseVideo
    cheat $ putStr $ case self.chars.right of
      [] => " "
      x :: _ => singleton x
    unreverseVideo
    cheat $ putStr $ pack $ tail self.chars.right

||| Implement Component for TextInput.
export
Controller TextInput String where
  handle Left      self = Do $ goLeft self
  handle Right     self = Do $ goRight self
  handle Delete    self = Do $ delete self
  handle (Alpha c) self = Do $ insert c self
  handle Enter     self = Yield $ Just $ toString self
  handle Escape    self = Yield Nothing
  handle _         self = Ignore

||| Make `String` `Editable` via `TextInput`
export
Editable String TextInput where
  fromValue = TextInput.fromString
  toValue   = Just . TextInput.toString
  blank     = TextInput.empty

||| Minimalist terminal UI Framework
|||
||| An Editable String View
module TUI.Component.TextInput


import Data.String
import TUI.Component
import Util
import Zipper


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

namespace Model

  public export
  data Action
    = Delete
    | GoLeft
    | GoRight
    | Insert Char

  export
  Model TextInput (Maybe String) Model.Action where
    update Delete     self = Left $ { chars $= delete  } self
    update GoLeft     self = Left $ { chars $= goLeft  } self
    update GoRight    self = Left $ { chars $= goRight } self
    update (Insert c) self = Left $ { chars $= insert c} self

namespace View

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
      moveTo rect.nw
      putStr $ kcap $ self.chars.left
      reverseVideo
      putStr $ case self.chars.right of
        [] => " "
        x :: _ => singleton x
      unreverseVideo
      putStr $ pack $ tail self.chars.right

namespace Controller

  ||| This controller implements basic single-line text input.
  Controller TextInput (Response (Maybe String) Model.Action) where
        -- map keys to their obvious functions.
    handle Left      self = Do GoLeft
    handle Right     self = Do GoRight
    handle Delete    self = Do Delete
    handle (Alpha c) self = Do $ Insert c
    handle Enter     self = Yield $ Just $ toString self
    handle Escape    self = Yield Nothing
    handle _         self = Ignore
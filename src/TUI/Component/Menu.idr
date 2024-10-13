||| A family of components for selecting from a list.
module TUI.Component.Menu


import Data.Fin
import Data.List
import Data.Nat
import TUI.Component
import TUI.Layout
import TUI.Painting
import TUI.View
import Util


%default total


||| Represents an exclusive choice
export
record Exclusive itemT where
  constructor MkChoice
  choices       : List itemT
  choice        : Fin (length choices)

||| Get the selected value.
export
(.selected) : Exclusive itemT -> itemT
(.selected) self = index' self.choices self.choice

||| Select the next item.
export
prev : Exclusive itemT -> Exclusive itemT
prev = { choice $= predS }

||| Select the previous item.
export
next : Exclusive itemT -> Exclusive itemT
next = { choice $= finS }

||| Select the given index.
export
choose
  :  (self : Exclusive itemT)
  -> Fin (length self.choices)
  -> Exclusive itemT
choose self c = { choice := c } self

||| Show the most appropriate indicator for the current choice.
|||
||| - 0     : down arrow
||| - last  : the up arrow
||| - other : the up-down arrow.
arrowForIndex : {k : Nat} -> (Fin k) -> String
arrowForIndex FZ     = arrow Down
arrowForIndex (FS n) = if FS n == last
  then arrow Up
  else arrow UpDown

namespace Spinner

  export
  View itemT => View (Exclusive itemT) where
    size self =
      let sizes   := View.size <$> self.choices
          content := foldl Area.union (MkArea 0 0) sizes
      in (MkArea 2 0) + content

    paint state window self = do
      withState state $ showTextAt window.nw (arrowForIndex self.choice)
      paint state (window.shiftRight 2) self.selected

  export
  handle : Handler (Exclusive itemT) itemT
  handle Up     self = update $ prev self
  handle Down   self = update $ next self
  handle Left   self = exit
  handle Escape self = exit
  handle Enter  self = yield self.selected
  handle _      _    = ignore

  export
  new
    :  (choices    : List itemT)
    -> {auto 0 prf : IsJust (natToFin 0 (length choices))}
    -> Exclusive itemT
  new choices = MkChoice choices $ fromJust $ natToFin 0 (length choices)

  export
  spinner
    :  View itemT
    => (choices    : List itemT)
    -> {auto 0 prf : IsJust (natToFin 0 (length choices))}
    -> Component itemT
  spinner {itemT} choices = active (new choices) handle

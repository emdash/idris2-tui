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

||| An editable table of items
|||
module TUI.Component.Table


import Data.String
import Data.Vect
import Data.Vect.Quantifiers
import TUI.Component
import TUI.Component.Box
import TUI.Component.FocusRing
import TUI.Component.VList
import TUI.Layout
import TUI.Util

-- keep this?
import TUI.Component.TextInput
import TUI.Component.Numeric


%default total


||| A visually-aligned 2D grid of rows and columns.
export
record Table {0 events : List Type} (tys : Vect k Type) where
  constructor MkTable
  headers : Vect k String
  rows    : Zipper (All (Component (HSum events)) tys)
  column  : Fin k

export
0 (.Selected)
  :  {0 events : List Type}
  -> {k    : Nat}
  -> {tys  : Vect k Type}
  -> (self : Table tys)
  -> Type
(.Selected) {tys} self = Component (HSum events)  (index self.column tys)

||| Get the selected value.
export
(.selected)
  :  {0 events : List Type}
  -> {k    : Nat}
  -> {tys  : Vect k Type}
  -> (self : Table {events} tys)
  -> Maybe (self.Selected {events})
(.selected) self = case cursor self.rows of
  Nothing => Nothing
  Just row => Just $ get self.column row

export
goLeft
  :  {0 events : List Type}
  -> {k : Nat}
  -> {tys : Vect (S k) Type}
  -> Table {events} tys
  -> Table {events} tys
goLeft = {column $= predS}

export
goRight
  :  {0 events : List Type}
  -> {k : Nat}
  -> {tys : Vect (S k) Type}
  -> Table {events} tys
  -> Table {events} tys
goRight = {column $= finS}

export
goUp
  :  {0 events : List Type}
  -> {k : Nat}
  -> {tys : Vect (S k) Type}
  -> Table {events} tys
  -> Table {events} tys
goUp = {rows $= goLeft}

export
goDown
  :  {0 events : List Type}
  -> {k : Nat}
  -> {tys : Vect (S k) Type}
  -> Table {events} tys
  -> Table {events} tys
goDown = {rows $= goRight}

export
next
  :  {0 events : List Type}
  -> {k : Nat}
  -> {tys : Vect (S k) Type}
  -> Table {events} tys
  -> Table {events} tys
next self = case (self.column == last) of
  True  => goRight $ goDown self
  False => goRight self

export
prev
  :  {0 events : List Type}
  -> {k : Nat}
  -> {tys : Vect (S k) Type}
  -> Table {events} tys
  -> Table {events} tys
prev self = case self.column of
  FZ => goLeft $ goDown self
  _  => goLeft self

export
insert
  :  All (Component (HSum events)) tys
  -> Table {events} tys
  -> Table {events} tys
insert row = {rows $= insert row}

export
(.values) : Table tys -> List (All Maybe tys)
(.values) self = mapProperty (.value) <$> toList self.rows

||| Calculate the column widths across all rows.
export
tabulate
  :  {k : Nat}
  -> {tys : Vect k Type}
  -> List (All (Component _) tys)
  -> Vect k Nat
tabulate rows = foldl colWidths (replicate k 0) rows
  where
    colWidths : Vect k Nat -> All (Component _) tys -> Vect k Nat
    colWidths accum components =
      zipWith max accum $ forget $ mapProperty (width . size) components

||| This implementation tries to align columns horizontally.
|||
||| Rows height can vary, and is the maximum height of any column in
||| that row.
|||
||| XXX: this is so ugly.
export
{k : Nat} -> {tys : Vect k Type} -> View (Table tys) where
  size self =
    let items := Zipper.List.toList self.rows
        cols  := tabulate items
        w     := foldl (+) 0 cols
        h     := foldl (+) 2 $ rowHeight <$> items
    in MkArea w h
  where
    rowHeight : All (Component _) tys -> Nat
    rowHeight row = reduceAll max (height . size) 0 row

  paint state window self = do
    let (left, cursor, right) = decompose self.rows
    let cols = tabulate $ toList self.rows
    window <- paintHeaders Normal window cols self.headers
    window <- packTop Normal window HRule
    window <- case (left, cursor) of
      ([],  Nothing) => packTop state window (box (MkArea window.width 1) ' ')
      _              => pure window
    window <- paintRows (demoteFocused state) window cols left
    window <- case cursor of
      Just cursor => do
        ignore $ paintRow state window cols cursor
        pure $ snd $ window.splitTop 1
      Nothing => pure window
    sgr [Reset]
    ignore $ paintRows (demoteFocused state) window cols right
  where
    rowHeight : All (Component _) tys -> Nat
    rowHeight row = reduceAll max (height . size) 0 row

    paintHeaders
      :  State
      -> Rect
      -> Vect k Nat
      -> Vect k String
      -> Context Rect
    paintHeaders state window cols labels = do
      let (top, bottom) = window.splitTop 1
      distributeHorizontal cols labels window
      pure bottom

    paintRow
      : {default 0 i : Nat}
      -> State
      -> Rect
      -> Vect j Nat
      -> {ts : Vect j Type}
      -> All (Component _) ts
      -> Context Rect
    paintRow state window [] [] = pure window
    paintRow {i} state window (c :: cs) (col :: cols) = do
      let (l, r) = window.splitLeft (c + 1)
      paint (if (i == finToNat self.column) then state else demoteFocused state) l col
      paintRow {i = S i} state r cs cols

    paintRows
      :  State
      -> Rect
      -> Vect k Nat
      -> List (All (Component _) tys)
      -> Context Rect
    paintRows state window cols [] = pure window
    paintRows state window cols (row :: rows) = do
      let (top, bottom) = window.splitTop (rowHeight row)
      ignore $ paintRow state top cols row
      paintRows state bottom cols rows

||| Update the selected component as appopriate.
|||
||| If the selected component yields a value, focus advances to the
||| next element.
|||
||| If the selected component exits, then the focus ring exits.
export
handleSelected
  :  {0 events : List Type}
  -> {k   : Nat}
  -> {tys : Vect (S k) Type}
  -> Component.Handler (Table {events} tys) (List (All Maybe tys)) (HSum events)
handleSelected event self = case self.selected of
  Nothing => ignore
  Just s  => handleResponse !(handle event s)
where
  updateSelected : (self.Selected {events}) -> Zipper (All (Component (HSum events)) tys)
  updateSelected item = case cursor self.rows of
    Nothing => self.rows
    Just _ => update (replaceAt self.column item) self.rows

  onMerge : (Maybe a -> self.Selected {events}) -> Maybe a -> Table {events} tys
  onMerge merge result = {rows := updateSelected (merge result)} self

  handleResponse
    :  Response (HSum events) (self.Selected {events}) (index self.column tys)
    -> IO (Response (HSum events) (Table {events} tys) (List (All Maybe tys)))
  handleResponse (Continue x) = update $ {rows := (updateSelected !x)} self
  handleResponse (Yield _   ) = update $ next self
  handleResponse (Push x f  ) = push x $ onMerge f

||| Construct a table component
export
table
  :  {0 events : List Type}
  -> {k        : Nat}
  -> {tys      : Vect (S k) Type}
  -> (labels   : Vect (S k) String)
  -> (rows     : List (All (Component (HSum events)) tys))
  -> (handler  : Component.Handler (Table {events} tys) (List (All Maybe tys)) (HSum events))
  -> Component (HSum events) (List (All Maybe tys))
table labels rows handler = component {
  state = MkTable labels (fromList rows) 0,
  handler = handler,
  get = Just . (.values)
}

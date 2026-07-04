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


module TUI.Component.FocusRing


import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers
import Data.SortedSet
import TUI.Component
import TUI.Layout
import TUI.View
import TUI.Util


%default total


||| A component that manages a heterogenous list of Components.
|||
||| Exactly one subcomponent has focus at any given time.
|||
||| This component is used to build forms and other multi-valued
||| components.
public export
record FocusRing {0 events : List Type} (tys : Vect k Type) where
  constructor MkFocusRing
  items     : All (Component (HSum events)) tys
  selection : Fin k

||| Get the type of the selection.
export
0 (.Selected)
  :  {0 events : List Type}
  -> {k    : Nat}
  -> {tys  : Vect k Type}
  -> (self : FocusRing {events} tys)
  -> Type
(.Selected) {tys} self = Component (HSum events) (index self.selection tys)

||| Get the selected value.
export
(.selected)
  :  {k    : Nat}
  -> {tys  : Vect k Type}
  -> (self : FocusRing tys)
  -> self.Selected
(.selected) self = get self.selection self.items

||| Select the next item.
export
prev
  :  {0 events : List Type}
  -> {k    : Nat}
  -> {tys  : Vect k Type}
  -> (self : FocusRing {events} tys)
  -> FocusRing {events} tys
prev = {selection $= predS}

||| Select the previous item.
export
next
  :  {0 events : List Type}
  -> {k    : Nat}
  -> {tys  : Vect k Type}
  -> (self : FocusRing {events} tys)
  -> FocusRing {events} tys
next = {selection $= finS}

||| Select the given index.
export
choose
  :  {0 events : List Type}
  -> {k      : Nat}
  -> {tys    : Vect k Type}
  -> (choice : Fin k)
  -> (self   : FocusRing {events} tys)
  -> FocusRing {events} tys
choose c = {selection := c}

||| Get the current values for each component.
export
(.values)
  :  {k    : Nat}
  -> {tys  : Vect k Type}
  -> (self : FocusRing tys)
  -> All Maybe tys
(.values) self = mapProperty (.value) self.items

||| Route event to the selected component.
|||
||| This function is provided so it cab be used from custom key
||| handlers.
|||
||| If the selected component `Continue`s, or `Pushes`, this we simply
||| update the selected component as appopriate.
|||
||| If the selected component yields a value, then the focusRing will
||| yield all its component values. This is probably not the behavior
||| you want, but you can customize it via `map` (or `<$>`).
|||
||| If the selected component exits, then the focus ring exits.
export
handleSelected
  :  {0 events : List Type}
  -> {k   : Nat}
  -> {tys : Vect k Type}
  -> Component.Handler (FocusRing {events} tys) (All Maybe tys) (HSum events)
handleSelected event self = case handle event self.selected of
  Continue x => Continue $ (\x => {items := updateSelected x} self) <$> x
  Yield v    => yield self.values
  Push x f   => push x $ onMerge f
where
  updateSelected : self.Selected -> All (Component (HSum events)) tys
  updateSelected item = replaceAt self.selection item self.items

  onMerge : (Maybe a -> self.Selected) -> Maybe a -> FocusRing {events} tys
  onMerge merge result = {items := updateSelected (merge result)} self


namespace Views

  export
  implementation [vertical]
       {k : Nat}
    -> {tys : Vect (S k) Type}
    -> View (FocusRing tys)
  where
    size self = reduceAll hunion size (MkArea 0 0) self.items
    paint state window self = do
      ignore $ recurse 0 window self.items
    where
      recurse : Fin (S k) -> Rect -> Data.Vect.Quantifiers.All.All (Component e) a -> Context Rect
      recurse i window []        = pure $ window
      recurse i window (x :: xs) = recurse (finS i) !(packTop focus window x) xs
      where
        focus : State
        focus = case state of
          Focused => if i == self.selection then Focused else Normal
          other   => other

  export
  implementation [horizontal]
       {k : Nat}
    -> {tys : Vect (S k) Type}
    -> View (FocusRing tys)
  where
    size self = reduceAll vunion size (MkArea 0 0) self.items
    paint state window self = do
      ignore $ recurse 0 window self.items
    where
      recurse : Fin (S k) -> Rect -> Data.Vect.Quantifiers.All.All (Component e) a -> Context Rect
      recurse i window []        = pure $ window
      recurse i window (x :: xs) = recurse (finS i) !(packLeft focus window x) xs
      where
        focus : State
        focus = case state of
          Focused => if i == self.selection then Focused else Normal
          other   => other

||| Construct a new concrete FocusRing
export
new
  :  {0 events : List Type}
  -> {k   : Nat}
  -> {tys : Vect k Type}
  -> All (Component (HSum events)) tys
  -> Fin k
  -> FocusRing {events} tys
new components choice = MkFocusRing components choice

||| Construct a generic FocusRing with a custom key handler.
|||
||| The principle degree of freedom is the yield value (`valueT`),
||| which can be transformed via `map` (or `<$>`) on an aribtrary
||| component. Use that if you want to, e.g. construct a record value
||| from the component fields.
|||
||| Navigation is determined by the custom `onKey` function. This
||| function should call `handleSelected` to delegate events to the
||| selected component.
|||
||| @k         Length of the type list.
||| @tys       The list of yield types indexing this container.
||| @items     The subcomponents, in order.
||| @selection The subcomponent which has focus.
||| @onKey     (Optional: a custom key handler).
||| @vimpl     : View (FocusRing tys))
export
focusRing
  :  {0 events : List Type}
  -> {k         : Nat}
  -> {tys       : Vect k Type}
  -> (vimpl     : View (FocusRing {events} tys))
  => (items     : All (Component (HSum events)) tys)
  -> (selection : Fin k)
  -> (onKey     : Component.Handler (FocusRing {events} tys) (All Maybe tys) (HSum events))
  -> Component (HSum events) (All Maybe tys)
focusRing {vimpl} items selection onKey = component @{vimpl} {
  state   = new items selection,
  handler = onKey,
  get     = Just . (.values)
}

||| Construct a FocusRing component that renders vertically.
|||
||| The principle degree of freedom is the yield value (`valueT`),
||| which can be transformed via `map` (or `<$>`) on an aribtrary
||| component. Use that if you want to, e.g. construct a record value
||| from the component fields.
|||
||| Navigation is determined by the custom `onKey` function. This
||| function should call `handleSelected` to delegate events to the
||| selected component.
|||
||| @k         Length of the type list.
||| @tys       The list of yield types indexing this container.
||| @items     The subcomponents, in order.
||| @selection The subcomponent which has focus.
||| @onKey     (Optional: a custom key handler).
export
vertical
  :  {0 events  : List Type}
  -> {k         : Nat}
  -> {tys       : Vect (S k) Type}
  -> (items     : All (Component (HSum events)) tys)
  -> (selection : Fin (S k))
  -> (onKey     : Component.Handler (FocusRing {events} tys) (All Maybe tys) (HSum events))
  -> Component (HSum events) (All Maybe tys)
vertical = focusRing @{vertical}

||| Construct a FocusRing component that renders horizontally.
|||
||| The principle degree of freedom is the yield value (`valueT`),
||| which can be transformed via `map` (or `<$>`) on an aribtrary
||| component. Use that if you want to, e.g. construct a record value
||| from the component fields.
|||
||| Navigation is determined by the custom `onKey` function. This
||| function should call `handleSelected` to delegate events to the
||| selected component.
|||
||| @k         Length of the type list.
||| @tys       The list of yield types indexing this container.
||| @items     The subcomponents, in order.
||| @selection The subcomponent which has focus.
||| @onKey     (Optional: a custom key handler).
export
horizontal
  :  {0 events  : List Type}
  -> {k         : Nat}
  -> {tys       : Vect (S k) Type}
  -> (items     : All (Component (HSum events)) tys)
  -> (selection : Fin (S k))
  -> (onKey     : Component.Handler (FocusRing {events} tys) (All Maybe tys) (HSum events))
  -> Component (HSum events) (All Maybe tys)
horizontal = focusRing @{horizontal}

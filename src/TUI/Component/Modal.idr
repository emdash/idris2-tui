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

||| This module contains machinery to support the `Push` response, and
||| modal behavior in total code.
module TUI.Component.Modal


import TUI.Component
import TUI.Painting
import TUI.Layout
import Data.List
import Data.List.Quantifiers


%default total


||| A heterogenous stack of Components.
|||
||| @top  The top type of the stack
||| @root The root type of the stack.
|||
||| Note: This was a tricky data-strcuture to get right. One key
||| detail is that the top of the stack is a function which returns a
||| component. The other key detail is the `top` index, which allows
||| the type checker to recognize the empty stack at the type level.
|||
||| I've tried other variatons on this idea, and this seems to be the
||| best.
public export
data Stack : Type -> (top : Type) -> (root : Type) -> Type where
  Nil  : Stack e root root
  ||| @merge Function to merge top of the stack with the element beneath.
  (::) : (merge : Maybe top -> Component e a) -> Stack e a root -> Stack e top root

||| A context for modal interaction.
|||
||| @rootT Type of the value yielded by context.
|||
||| A component manages a stack of components, routing events to the
||| topmost component.
|||
||| When the top component responds with `Yield`, it is removed from
||| the stack, and the yielded value merged into the next stack
||| element, if any exists. If the stack is empty, then the `Modal`
||| itself yields the root value.
|||
||| Note: this type is needed to hide the `top` index on the stack,
||| otherwise we could just use `Stack` itself as a component.
public export
record Modal eventT rootT where
  constructor M
  component : Component eventT topT
  stack : Stack eventT topT rootT

-- we can use `(.topT)` instead, which reads better anyway. `topT`
-- just ends up shadowing useful type arguments. I wish for some
-- better control over record elaboration in future versions of Idris.
--
-- the other way to handle this is to disable unbound implicits, but
-- this then requires explicit quantification, which is overkill here.
%hide Modal.topT

||| Remove the top component from the modal stack.
|||
||| @self   The current modal context.
||| @result The value to merge or yield.
pop
  :  (self : Modal eventT rootT)
  -> (result : Maybe self.topT)
  -> Either (Modal eventT rootT) (Maybe rootT)
pop (M top [])               result = Right result
pop (M top (merge :: tail))  result = Left $ M (merge result) tail

||| Push a component into the Modal context, with the merge function.
push
  :  Component eventT topT
  -> (self : Modal eventT rootT)
  -> (Maybe topT -> Component eventT self.topT)
  -> Modal eventT rootT
push top self merge = M top (merge :: self.stack)

||| Construct a new modal context with the given component.
|||
||| You shouldn't need to call this. It is used by `runComponent` in
||| the `MainLoop` to wrap the root component.
export
root : Component eventT rootT -> Modal eventT rootT
root component = M component []

||| This is the top-level event handler for a modal context.
|||
||| You should not normally need to call this: it is called by
||| `runComponent` in MainLoop.
export
handle : Event.Handler (Modal eventT rootT) rootT eventT
handle event self = case !(handle event self.component) of
  Continue state => update $ {component := !state} self
  Yield result   => doPop $ result
  Push top merge => update $ push top self merge
where
  doPop : IO (Maybe self.topT) -> Result (Modal eventT rootT) rootT
  doPop result = case pop self !result of
    Left  state  => update state
    Right result => exitWith result

||| This is the default view implementation for Modal.
|||
||| It paints only the top-most component into the given window.
export
[topmost] View (Modal _ t) where
  size self = size self.component
  paint state window self = paint state window self.component

||| This view nests modals visually using `inset`.
|||
||| The root component gets the full window. Modals are inset inside
||| inside the parent like popup dialogs.
|||
||| To use this, pass `@{inset}` in your call to `runComponent`,
||| `runView`, `paint`, `component`, etc.
export
[inset] View (Modal _ t) where
  size self = union (size self.component) (sizeStack self.stack)
    where
      sizeStack : Stack _ _ _ -> Area
      sizeStack [] = empty
      sizeStack (merge :: xs) = union (size $ merge Nothing) (sizeStack xs)

  paint state window self = case self of
    (M component []) => paint state window component
    (M component stack) => do
      window <- paintStack window stack
      fill ' ' window
      paint state window component
      border (grow window)
  where
    paintStack : Rect -> Stack _ _ _ -> Context Rect
    paintStack window [] = pure window
    paintStack window [merge] = do
      paint Disabled window (merge Nothing)
      pure (inset window (MkArea 3 3))
    paintStack window (merge :: ys) = do
      window <- paintStack window ys
      fill ' ' window
      paint Disabled window (merge Nothing)
      sgr [SetStyle Faint]
      border (grow window)
      sgr [Reset]
      pure (inset window (MkArea 3 3))

||| Centers modals within the parent viewport at their requested size.
|||
||| The root component gets the full window.
|||
||| To use this, pass `@{inset}` in your call to `runComponent`,
||| `runView`, `paint`, `component`, etc.
export
[centered] View (Modal _ t) where
  size self = union (size self.component) (sizeStack self.stack)
    where
      sizeStack : Stack _ _ _ -> Area
      sizeStack [] = empty
      sizeStack (merge :: xs) = union (size $ merge Nothing) (sizeStack xs)

  paint state window self = case self of
    (M component []) => paint state window component
    (M component stack) => do
      paintStack window stack
      let modal = (size component).centerIn window
      fill ' ' modal
      paint state modal component
      border (grow modal)
  where
    paintStack : Rect -> Stack _ _ _ -> Context ()
    paintStack window [] = pure ()
    paintStack window [merge] = do
      paint Disabled window (merge Nothing)
    paintStack window (merge :: ys) = do
      paintStack window ys
      let view = (merge Nothing)
      let modal = (size view).centerIn window
      fill ' ' modal
      paint Disabled modal view
      border (grow modal)

||| This view stacks modals vertically, from the top.
|||
||| To use this, pass `@{fromTop}` in your call to `runComponent`,
||| `runView`, `paint`, `component`, etc.
export
[fromTop] View (Modal _ t) where
  size self = union (size self.component) (sizeStack self.stack)
    where
      sizeStack : Stack _ _ _ -> Area
      sizeStack [] = empty
      sizeStack (merge :: xs) = hunion (size $ merge Nothing) (sizeStack xs)

  paint state window self = case self of
    (M component []) => paint state window component
    (M component stack) => do
      window <- paintStack window stack
      window <- packTop state window HRule
      paint state window component
  where
    paintStack : Rect -> Stack _ _ _ -> Context Rect
    paintStack window [] = pure window
    paintStack window [merge] = do
      packTop Disabled window (merge Nothing)
    paintStack window (merge :: ys) = do
      window <- paintStack window ys
      window <- packTop Disabled window HRule
      packTop Disabled window (merge Nothing)

||| This view stacks modals horizontally, from the left.
|||
||| To use this, pass `@{fromLeft}` in your call to `runComponent`,
||| `runView`, `paint`, `component`, etc.
export
[fromLeft] View (Modal _ t) where
  size self = union (size self.component) (sizeStack self.stack)
    where
      sizeStack : Stack _ _ _ -> Area
      sizeStack [] = empty
      sizeStack (merge :: xs) = vunion (size $ merge Nothing) (sizeStack xs)

  paint state window self = case self of
    (M component []) => paint state window component
    (M component stack) => do
      window <- paintStack window stack
      window <- packLeft state window VRule
      ignore $ packLeft state window component
  where
    paintStack : Rect -> Stack _ _ _ -> Context Rect
    paintStack window [] = pure window
    paintStack window [merge] = do
      packLeft Disabled window (merge Nothing)
    paintStack window (merge :: ys) = do
      window <- paintStack window ys
      window <- packLeft Disabled window VRule
      packLeft Disabled window (merge Nothing)

||| The default view should be the inset view.
export %hint
defaultView : View (Modal eventT t)
defaultView = inset

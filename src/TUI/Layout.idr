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

||| This module contains code for arranging views on the screen.
|||
||| For the moment, this just contains a few useful routines. But I
||| can imagine this expanding over time.
module TUI.Layout


import Data.Vect
import Data.Vect.Quantifiers
import TUI.Painting
import TUI.Geometry
import TUI.View


%default total


||| A function which paints a view, returning the remaining area.
public export
0 PackFn : Type -> Type
PackFn v = State -> Rect -> v -> Context Rect

||| Paint the given view into the top of the given window.
|||
||| Return the remaning space in the window.
export
packTop : View v => PackFn v
packTop state window self = do
  let split = (size self).height
  let (top, bottom) = window.splitTop split
  paint state top self
  pure bottom

||| Paint the given view into the bottom of the given window.
|||
||| Return the remaning space in the window.
export
packBottom : View v => PackFn v
packBottom state window self = do
  let split = (size self).height
  let (top, bottom) = window.splitBottom split
  paint state bottom self
  pure top

||| Paint the given view into the left of the given window.
|||
||| Return the remaning space in the window.
export
packLeft : View v => PackFn v
packLeft state window self = do
  let split = (size self).width
  let (left, right) = window.splitLeft split
  paint state left self
  pure right

||| Paint the given view into the right of the given window.
|||
||| Return the remaning space in the window.
export
packRight : View v => PackFn v
packRight state window self = do
  let split = (size self).width
  let (left, right) = window.splitRight split
  paint state right self
  pure left

namespace Foldable

  public export
  0 LayoutFn : Type -> (Type -> Type) -> Type
  LayoutFn v t = State -> Rect -> t v -> Context Rect

  ||| Paint the given list of views, laying them out vertically within
  ||| `window`.
  export
  paintWith : View v => Foldable t => PackFn v -> LayoutFn v t
  paintWith pack state window self = foldl draw1 (pure window) self
    where
      draw1 : Context Rect -> v -> Context Rect
      draw1 window self = pack state !window self
  
  export  
  sizeWith 
    : View v 
    => Foldable t 
    => Functor t 
    => (Area -> Area -> Area) 
    -> t v 
    -> Area
  sizeWith sz self = foldl sz (MkArea 0 0) (size <$> self)

  ||| Convenience function for automatic vertical layout
  export
  paintVertical : View v => Foldable t => LayoutFn v t
  paintVertical = paintWith packTop

  ||| Convenience function for automatic horizontal layout
  export
  paintHorizontal : View v => Foldable t => LayoutFn v t
  paintHorizontal = paintWith packLeft

  ||| Size the given list of views, laying them out vertically within.
  export
  sizeVertical : View v => Foldable t => t v -> Area
  sizeVertical self = foldl (flip $ hunion . size) (MkArea 0 0) self

  ||| Size the given list of views, laying them out horizontally within.
  export
  sizeHorizontal : View v => Foldable t => t v -> Area
  sizeHorizontal self = foldl (flip $ vunion . size) (MkArea 0 0) self

||| A concrete view type for horizontal and vertical separators.
public export
data Rule = HRule | VRule

||| View implementation for these visual separators.
|||
||| Use these with `pack*` for easy layout.
export
View Rule where
  size HRule = MkArea 0 1
  size VRule = MkArea 1 0

  paint _ window HRule = hline window.nw window.hspan
  paint _ window VRule = vline window.nw window.vspan

||| Distribute views horizontally according to the cell widths.
export
distributeHorizontal
  :  View itemT
  => {k       : Nat}
  -> (columns : Vect k Nat)
  -> (views   : Vect k itemT)
  -> (window  : Rect)
  -> Context ()
distributeHorizontal [] [] window = pure ()
distributeHorizontal (c :: cs) (view :: views) window = do
  let (left, right) = window.splitLeft (c + 1)
  paint Normal left view
  distributeHorizontal cs views right

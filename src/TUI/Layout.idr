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

import TUI.Painting
import TUI.Geometry
import TUI.View


%default total


||| Size the given list of views, laying them out vertically within.
export
sizeVertical : View itemT => List itemT -> Area
sizeVertical self = foldl (flip $ hunion . size) (MkArea 0 0) self

||| Paint the given view into the top of the given window.
|||
||| Return the remaning space in the window.
export
packTop : View v => State -> Rect -> v -> Context Rect
packTop state window self = do
  let split = (size self).height
  let (top, bottom) = window.splitTop split
  paint state top self
  pure bottom

||| Paint the given view into the bottom of the given window.
|||
||| Return the remaning space in the window.
export
packBottom : View v => State -> Rect -> v -> Context Rect
packBottom state window self = do
  let split = (size self).height
  let (top, bottom) = window.splitBottom split
  paint state bottom self
  pure top

||| Paint the given view into the left of the given window.
|||
||| Return the remaning space in the window.
export
packLeft : View v => State -> Rect -> v -> Context Rect
packLeft state window self = do
  let split = (size self).width
  let (left, right) = window.splitLeft split
  paint state left self
  pure right

||| Paint the given view into the right of the given window.
|||
||| Return the remaning space in the window.
export
packRight : View v => State -> Rect -> v -> Context Rect
packRight state window self = do
  let split = (size self).width
  let (left, right) = window.splitRight split
  paint state right self
  pure left


||| Paint the given list of views, laying them out vertically within
||| `window`.
export
paintVertical
  : View v
  => (state   : State)
  -> (window  : Rect)
  -> (self    : List v)
  -> Context Rect
paintVertical state window [] = pure window
paintVertical state window (x :: xs) = paintVertical state !(packTop state window x) xs

||| Size the given list of views, laying them out horizontally within.
export
sizeHorizontal : View itemT => List itemT -> Area
sizeHorizontal self = foldl (flip $ vunion . size) (MkArea 0 0) self

||| Paint the given list of views, laying them out vertically within
||| `window`.
export
paintHorizontal
  : View v
  => (state   : State)
  -> (window  : Rect)
  -> (self    : List v)
  -> Context Rect
paintHorizontal state window [] = pure window
paintHorizontal state window (x :: xs) = paintHorizontal state !(packLeft state window x) xs

||| A concrete view type for horizontal and vertical separators.
public export
data Rule = HRule | VRule

||| View implementation for rules
export
View Rule where
  size HRule = MkArea 0 1
  size VRule = MkArea 1 0

  paint _ window HRule = hline window.nw window.size.width
  paint _ window VRule = vline window.nw window.size.height

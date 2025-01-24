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

||| A `View` can render itself in ANSI-compatible output. Think of it
||| like an enhanced version of `Show`, that knows about ANSI escape
||| sequences, and keeps track of drawing state so you don't have to.
|||
||| You can implement `View` on your own types to use them with this
||| library.
module TUI.View


import public TUI.Painting


%default total


namespace State
  ||| The high-level drawing state for views.
  |||
  ||| This is used by the `paint` method to provide appropriate
  ||| feedback.
  public export
  data State = Normal | Focused | Disabled

  ||| Demote the `Focused` state to the `Normal` state.
  |||
  ||| This is useful for rendering unfocused sibling components within
  ||| a container.
  public export
  demoteFocused : State -> State
  demoteFocused Focused = Normal
  demoteFocused x       = x

  ||| Default styles for rendering text
  export
  styleForState : State -> Context ()
  styleForState Normal   = sgr [Reset]
  styleForState Focused  = sgr [SetReversed True]
  styleForState Disabled = sgr [SetStyle Faint]

  ||| Paint with the appropriate style for the given state.
  |||
  ||| Completely resets the graphics context after painting.
  export
  withState : State -> Context () -> Context ()
  withState state wrapped = do
    styleForState state
    wrapped
    sgr [Reset]

||| A View can paint itself to the screen in 2D.
|||
||| - It knows its minimum size.
||| - It knows how to style itself for each draw state.
||| - It knows how to paint itself within a given window.
public export
interface View selfT where
  constructor MkView
  ||| Calculate the minimum area for this view.
  size  : selfT -> Area

  ||| Draw the view into the given screen rectangle.
  paint : State -> Rect -> selfT -> Context ()

||| Implement `View` for `()` as a no-op
export
View () where
  size  _     = MkArea 0 0
  paint _ _ _ = pure ()

export
View String where
  size self = MkArea (length self) 1
  paint state window self = withState state $ showTextAt window.nw self

||| Any type implementing `Show` can be painted
|||
||| Unfortunately, this implementation will often 'win' when you don't
||| want it to, so it remains a named impl.
|||
||| Pass `@{show}` to functions expecting a `View` to use this
||| implementation.
export
[show]
Show a => View a where
  size s = MkArea (length (show s)) 1
  paint state r s = withState state $ showTextAt r.nw (show s)

||| Implement View for `maybe` of any view.
|||
||| If `Just`, then we paint the given subview. Otherwise it behaves
||| as if it were not present.
export
View v => View (Maybe v) where
  size (Just self) = size self
  size Nothing     = MkArea 0 0

  paint state window (Just self) = paint state window self
  paint _    _       Nothing     = pure ()

||| Implement view for Either.
|||
||| Simply delegates to whichever variant is present.
export
View v1 => View v2 => View (Either v1 v2) where
  size (Left self)  = size self
  size (Right self) = size self

  paint state window (Left self)  = paint state window self
  paint state window (Right self) = paint state window self

||| An `Area` can be used as a blank view, or spacer, of fixed size.
|||
||| This is useful with functions like `packTop and `paintVertical`.
export
View Area where
  size = id
  paint _ _ _ = pure ()

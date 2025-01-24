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


||| A box that knows how to draw itself
module TUI.Component.Box


import TUI.Component
import TUI.Geometry
import TUI.Painting
import TUI.View


||| A styled rectangle.
export
record Box where
  constructor MkBox
  size  : Area
  char  : Char
  attrs : List SGR

||| Create a styled rectangle.
|||
||| Default attrs are empty. You can override attrs by passing `{attrs
||| = ...}`
export
box
  :  (size : Area)
  -> (char : Char)
  -> {default [] attrs : List SGR}
  -> Box
box size char {attrs} = MkBox size char attrs


export
View Box where
  size self = self.size
  paint state window self = do
    case state of
      Focused => do
        sgr $ SetReversed True :: self.attrs
      _ => sgr self.attrs
    fill self.char window


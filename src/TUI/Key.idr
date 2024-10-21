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

||| This module implements decoding of ANSI escpe sequences for cursor
||| keys.
|||
||| For now, only a small portion of legacy ANSI key sequences are
||| supported. The goal is to expand this to support progressive
||| enhancement towards the modern iTerm2-style escape sequences.
module TUI.Key


import Derive.Prelude
import JSON.Derive
import TUI.Event
import TUI.DFA


%default total
%language ElabReflection


||| Abstract key value, decoded from ANSI escape sequence.
|||
||| Right now we support only the bare minimum required for basic
||| UI. In particular, we have no support for modifier or function
||| keys.
public export
data Key
  = Alpha Char
  | Left
  | Right
  | Up
  | Down
  | Delete
  | Enter
  | Tab
  | Escape
%runElab derive "Key" [Ord, Eq, Show, FromJSON]

||| The state machine for escape sequence decoding.
|||
||| XXX: After heavy refactoring, this type has become isomorphic to
||| Maybe (SnocList Char).
data EscState
  = HaveEsc (SnocList Char)
  | Default
%runElab derive "EscState" [Show]

||| Capture char into escape buffer.
escape : Char -> EscState -> Transition EscState Key
escape c (HaveEsc e) = Advance (HaveEsc (e :< c)) Nothing
escape c Default     = Advance (HaveEsc [< c])    Nothing

||| Emit the given key and reset state.
emit : Key -> Transition EscState Key
emit key = Advance Default (Just key)

reset : Transition EscState Key
reset = Advance Default Nothing

||| A machine which decodes (some) legacy-style ANSI sequences.
export
ansiDecoder : Automaton Char Key
ansiDecoder = automaton Default decode
  where
    ||| Decide what to do for the given character.
    |||
    ||| This is just a quick-and-dirty MVP. No attempt to decode
    ||| modifiers.
    |||
    ||| The eventual goal is to use the code in `TUI/DFA.idr` to make
    ||| implementing the full spec more manageable. For now, this
    ||| simple approach based on pattern gets the job done.
    decode : TransitionFn EscState Char Key
    -- multi-char sequences in this clause
    decode c self@(HaveEsc esc) = case esc :< c of
      [<]                  => escape c self
      [< '\ESC']           => escape c self
      [< '\ESC', '\ESC']   => emit Escape
      [< '\ESC', '[']      => escape c self
      [< '\ESC', '[', 'C'] => emit Right
      [< '\ESC', '[', 'D'] => emit Left
      [< '\ESC', '[', 'A'] => emit Up
      [< '\ESC', '[', 'B'] => emit Down
      _                    => reset
    -- single-char matches below here
    decode '\ESC' self = escape '\ESC' self
    decode '\DEL' self = emit Delete
    decode '\n'   self = emit Enter
    decode '\t'   self = emit Tab
    decode c      self = emit (Alpha c)

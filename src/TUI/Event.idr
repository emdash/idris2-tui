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

||| This module provides partial support for decoding ansi input
||| escape sequences into high-level keys.
|||
||| There are libraries that do this, but not ones written in
||| Idris. This seems like territory for which Idris is well-suited,
||| and I don't feel like getting into Idris FFI right now.
|||
||| At present, only a few core sequences are decoded that should work
||| anywhere. In the future, I will expand this to cover iTerm2-style
||| extensions supported by contemporary terminals, but this will
||| require support for feature detection.
module TUI.Event


import Data.IORef
import public JSON
import JSON.Derive
import TUI.DFA


%default total
%language ElabReflection


namespace Result
  ||| A function to update state in response to an event.
  public export
  0 Result : Type -> Type -> Type
  Result stateT valueT = IO (Either stateT (Maybe valueT))

  export
  ignore : {auto self : stateT} -> Result stateT _
  ignore {self} = pure $ Left self

  export
  exitWith : Maybe valueT -> Result _ valueT
  exitWith result = pure $ Right result

  export
  exit : Result _ _
  exit = exitWith Nothing

  export
  yield : valueT -> Result _ valueT
  yield v = exitWith $ Just v

  export
  update : stateT -> Result stateT _
  update next = pure $ Left next

  export
  run : IO stateT -> Result stateT _
  run next = pure $ Left !next

||| A function to update application state in response to an event.
public export
0 Handler : Type -> Type -> Type -> Type
Handler stateT valueT eventT = eventT -> stateT -> Result stateT valueT

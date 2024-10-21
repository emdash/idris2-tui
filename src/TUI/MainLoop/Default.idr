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

||| Choose at runtime which mainloop to run based on environment variable.
module TUI.MainLoop.Default


import System
import TUI.Event
import TUI.Key
import TUI.MainLoop
import TUI.MainLoop.InputShim
import TUI.MainLoop.Base
import TUI.Painting


%default total


||| Chooses which mainloop to run based on env var.
export
0 Default : Type
Default = Either (InputShim [Key]) Base

||| Construct a mainloop based the IDRIS_TUI_MAINLOOP envvar
export covering
getDefault : IO Default
getDefault = do
  case !(getEnv "IDRIS_TUI_MAINLOOP") of
    Nothing           => pure $ Right base
    Just "base"       => pure $ Right base
    Just "input-shim" => pure $ Left !inputShim
    Just wtf          => die
      "Invalid MainLoop: \{show wtf}: give one of \"base\" or \"input\""

export covering
MainLoop Default where
  runRaw (Left b) = runRaw b
  runRaw (Right is) = runRaw is

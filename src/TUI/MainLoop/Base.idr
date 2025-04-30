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

||| This pure idris mainloop depends only on the code found in Base.
|||
||| Use this mainloop for stand-alone executables that don't need to
||| handle anything other than keyboard events.
module TUI.MainLoop.Base


import Data.IORef
import System
import System.File
import System.Concurrency
import TUI.DFA
import TUI.Event
import TUI.Key
import TUI.MainLoop
import TUI.Painting


%default total

ConsoleOutput IO where
  writeStdout = Prelude.IO.putStr
  perror      = ignore . (fPutStrLn stderr)


-- namespace used to make type of `Base` opaque within remainder of this file.
namespace Base
  ||| A mainloop which depends only on base.
  export
  0 Base : Type
  Base = ()

  ||| Create a new base mainloop.
  export
  base : Base
  base = ()


export covering
MainLoop Base (HSum [Key]) where
  runRaw self onKey render init = do
    Right _ <- enableRawMode
            | Left _ => die "Couldn't put terminal in raw mode."
    putStrLn ""
    altScreen True
    cursor False
    saveCursor
    ret <- loop ansiDecoder init
    cleanup
    pure ret
  where
    cleanup : IO Builtin.Unit
    cleanup = do
      clearScreen
      restoreCursor
      cursor True
      altScreen False
      resetRawMode

    ||| The actual main loop
    loop : Automaton Char Key -> stateT -> IO (Maybe valueT)
    loop decoder state = do
      beginSyncUpdate
      clearScreen
      window <- screen
      present window.size $ do
        -- all drawing operations now live in the `Context` monad,
        -- so they must be nested under the `present` IO action.
        moveTo origin
        render window state
      endSyncUpdate
      case next !getChar decoder of
        Discard => loop decoder state
        Advance decoder Nothing => loop decoder state
        Advance decoder (Just key) => case !(onKey (inject key) state) of
          Left  state => loop decoder state
          Right value => pure $ value
        Accept state => assert_total $ idris_crash "ANSI decoder in final state!"
        Reject str => do
          perror "ANSI Decode Error: \{str}"
          loop (reset decoder) state

||| Special case for a singleton set of events
export covering
MainLoop Base Key where
  runRaw self handler render init = runRaw self wrapped render init
    where
      wrapped : HSum [Key] -> stateT -> Result stateT valueT
      wrapped key state = handler (project1 key) state

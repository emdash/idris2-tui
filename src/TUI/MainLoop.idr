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

||| Entry point for running TUI applications.
|||
||| The code in this file takes care of initializing and restoring
||| terminal state, and then begins running the desired top-level
||| code.

module TUI.MainLoop


import TUI.View
import TUI.Event
import TUI.Key
import TUI.Painting
import TUI.Component
import TUI.Component.Modal
import Data.List.Quantifiers


%default total


||| Abstracts over different types of event loops supported by this
||| library.
|||
||| A mainloop must:
|||
||| - Initialize the terminal
||| - Receive events
||| - Pass events to the appropriate handlers
||| - Update the application state
||| - Render the application state to the screen via the given callback.
||| - Clean up the terminal on exit
interface MainLoop a e where
  ||| Initialize the terminal, then enter the main loop.
  |||
  ||| @ mainloop A mainloop instance
  ||| @ handlers A list of handlers covering each event source.
  ||| @ render   A function to render the current state to the screen.
  ||| @ init     The initial application state.
  |||
  ||| This is the lowest-level entry point.
  runRaw
    :  (mainloop : a)
    -> (onEvent  : Event.Handler stateT valueT e)
    -> (render   : Rect -> stateT -> Context ())
    -> (init     : stateT)
    -> IO (Maybe valueT)

||| Like runRaw, but for `stateT` which implement `View`.
|||
||| Accordingly, it drops the `render` parameter.
export covering
runView
  :  View stateT
  => MainLoop ml e
  => (mainloop : ml)
  -> (onEvent : Event.Handler stateT valueT e)
  -> stateT
  -> IO (Maybe valueT)
runView mainloop onEvent init = runRaw {
  mainloop = mainloop,
  onEvent  = onEvent,
  render   = View.paint Focused,
  init     = init
}

||| Like runView, but for `Component`.
export covering
runComponent
  :  (vimpl : View (Modal eventT valueT))
  => MainLoop ml eventT
  => (mainloop : ml)
  -> (self : Component eventT valueT)
  -> IO (Maybe valueT)
runComponent mainloop self = runView @{vimpl} mainloop handle (root self)

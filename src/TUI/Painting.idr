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

||| Immediate-mode TUI graphics.
|||
||| These routines are slightly higher-level than that provided by
||| `Control.ANSI`. In particular, we use types from `TUI.Geometry`.
|||
||| These routines operate on an opaque `Context` which theoretically
||| tracks the draw state, allowing for scope-based mangement of draw
||| state (position, color, font, style, etc). In practice everything
||| is written directly to stdout. Baby steps.
|||
||| I would like to support client code which looks like:
|||
||| ```idris
||| withSGR [Reverse] $ do
|||    window <- packTop state window self.label
|||    withClip window $ do
|||      withTransform self.scrollPos $ \window => do
|||        ignore $ paintVertical state window self.items
|||      ...
||| ```
|||
||| In certain situations, the rightward drift is a small price to pay
||| for clear scoping of draw operations.
|||
||| There is no support for *clipping*, and so there's no support for
||| scrolling. It's still early days.
module TUI.Painting


import public Control.ANSI
import Data.String
import System
import public TUI.Geometry


%default total


namespace Context
  ||| A context for drawing to the terminal.
  |||
  ||| For now this is a simple wrapper around IO, which affords the
  ||| freedom to do something different later if need be.
  export
  record Context a where
    constructor C
    action : IO a

  ||| Context is just a wrapper around IO.
  |||
  ||| This escape hatch is to cover the cases we don't handle yet, in
  ||| a way that's easy to grep for.
  |||
  ||| The eventual goal is to remove all uses of this function, making
  ||| Context completely self-contained.
  export
  cheat : IO a -> Context a
  cheat a = C a

  ||| Paint the context to stdout.
  export
  present : Context a -> IO a
  present (C a) = a

  -- Make Context work with `do` notation --

  export
  Functor Context where
    map f (C x) = C [| f x |]

  export
  Applicative Context where
    pure a = C $ pure a
    (C f) <*> (C x) = C (f <*> x)

  export
  Monad Context where
    (C x) >>= f = C $ x >>= (.action) . f

||| Move the cursor to the given point
export
moveTo : Pos -> Context ()
moveTo pos = cheat $ putStr $ cursorMove pos.y pos.x

||| Draw text at the given point
export
showTextAt : Pos -> String -> Context ()
showTextAt pos x = do
  moveTo pos
  cheat $ putStr x

||| Draw a single character at the given point.
export
showCharAt : Pos -> Char -> Context ()
showCharAt pos x = showTextAt pos (singleton x)

||| Undoes the above
export
unreverseVideo : Context ()
unreverseVideo = cheat $ putStr "\ESC[27m"

||| This attribute isn't part of the ANSI library in contrib, but is
||| arguably more useful than setting explicit colors.
export
reverseVideo : Context ()
reverseVideo = cheat $ putStr "\ESC[7m"

||| effectful version for setting arbitrary SGR attributes
export
sgr : List SGR -> Context ()
sgr = cheat . putStr . escapeSGR


||| Definitions for box-drawing symbols
namespace Box

  ||| Symbolic type for box drawing characters
  public export
  data Symbol
    = NW
    | NE
    | SW
    | SE
    | H
    | V

  ||| Draw the corresponding box character
  export
  putAt : Pos -> Symbol -> Context ()
  putAt pos NW = showCharAt pos $ cast 0x250C
  putAt pos NE = showCharAt pos $ cast 0x2510
  putAt pos SW = showCharAt pos $ cast 0x2514
  putAt pos SE = showCharAt pos $ cast 0x2518
  putAt pos H  = showCharAt pos $ cast 0x2500
  putAt pos V  = showCharAt pos $ cast 0x2502

  ||| Draw a horizontal line
  export
  hline : Pos -> Nat -> Context ()
  hline pos@(MkPos x y) width = do
    putAt pos H
    case width of
      Z   => pure ()
      S n => hline (MkPos (S x) y) n

  ||| Draw a vertical line
  export
  vline : Pos -> Nat -> Context ()
  vline pos@(MkPos x y) height = do
    putAt pos V
    case height of
      Z   => pure ()
      S n => vline (MkPos x (S y)) n

  ||| Fill a rectangle with the given character
  export
  fill : Char -> Rect -> Context ()
  fill c box = loop box.height box.nw
    where
      loop : Nat -> Pos -> Context ()
      loop Z _ = pure ()
      loop i@(S n) pos = do
        showTextAt pos $ replicate box.width c
        loop n $ pos.shiftDown 1

  ||| Draw a box around the given rectangle
  |||
  ||| Use with `shrink` or `inset` to layout contents within the frame.
  export
  box : Rect -> Context ()
  box r = do
    -- draw the lines at full size
    hline r.nw r.hspan
    hline r.sw r.hspan
    vline r.nw r.vspan
    vline r.ne r.vspan
    -- paint over with the corners
    putAt r.nw NW
    putAt r.ne NE
    putAt r.sw SW
    putAt r.se SE


||| Definitions for unicode arrows.
namespace Arrow

  ||| Symbolic names for different types of arrows
  public export
  data Direction
    = Up
    | Down
    | UpDown
    -- TBD: Left, Right, LeftRight, etc.

  -- TBD: Double-struck, skinny, etc.

  ||| Draw the specified arrow at the current cursor position.
  export
  arrow : Direction -> String
  arrow Up     = "⬆"
  arrow Down   = "⬇"
  arrow UpDown = "⬍"


||| Provides control over terminal modes, like cursor visibility, alt
||| screen mode, and synchronous update mode.
|||
||| As these are only intended to be used from MainLoop
||| implementations, they are `IO` actions, rather than context
||| actions.
namespace VTerm

  ||| Clear the contents of the screen.
  export
  clearScreen : IO ()
  clearScreen = putStr $ eraseScreen All

  ||| Switch into or out of the alternate screen buffer
  export
  altScreen : Bool -> IO ()
  altScreen True  = putStr $ "\ESC[?1049h"
  altScreen False = putStr $ "\ESC[?1049l"

  ||| Show or hide cursor
  export
  cursor : Bool -> IO ()
  cursor True  = putStr "\ESC[?25h"
  cursor False = putStr "\ESC[?25l"

  ||| Tell the terminal to save its state.
  export
  saveCursor : IO ()
  saveCursor = putStr "\ESC7"

  ||| Tell the terminal to restore its state.
  export
  restoreCursor : IO ()
  restoreCursor = putStr "\ESC8"

  ||| synchronous update Supported by iTerm2 and other fancy terminals
  export
  beginSyncUpdate : IO ()
  beginSyncUpdate = putStrLn "\ESC[?2026h"

  ||| synchronous update supported by iTerm2 and other fancy terminals
  export
  endSyncUpdate : IO ()
  endSyncUpdate = putStrLn "\ESC[?2026l"

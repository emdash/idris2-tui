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
||| `Text.ANSI`. In particular, we use types from `TUI.Geometry`.
|||
||| These routines operate on an opaque `Context` which theoretically
||| tracks the draw state, allowing for scope-based mangement of draw
||| state (position, color, font, style, etc). In practice everything
||| is written (almost) directly to stdout.
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
||| For now, you're responsible for keeping track of terminal
||| attributes.
|||
||| Everything in this file, but clipping in particular, relies on
||| synchronized updates to avoid crazy flicker and other strange
||| artifacts.
module TUI.Painting


import public Text.ANSI
import Data.String
import public TUI.Geometry


%default total

||| Distinguish Display Coordinates from Logical Coordinates.
|||
||| Geometry uses signed positions to allow calculating with negative
||| positions. This is needed to allow scolling content past the edge of the
||| screen.
|||
||| However, Actual terminals do not work with negative indices. This enforces
||| that cordinates are clamped to the actual display geometry prior to output.
-- public export
-- record Pos where
--   constructor MkPos
--   x : Nat
--   y : Nat


||| Abstract over writing to the console.
|||
||| This is needed because Async needs non-blocking IO, but those
||| functions aren't available in the Base mainloop.
public export
interface Monad io => ConsoleOutput io where
  writeStdout : String -> io ()
  perror      : String -> io ()

||| A terminal image is just a giant string, and the terminal is
||| responsible for drawing it.
|||
||| We try not to make too many assumptions about how the terminal
||| does this, as it can vary. But, in general, concatenating two
||| strings will combine the two images (though not perhaps in the way
||| you expect).
|||
||| As an optimization, we represent lists of string fragments, which
||| we merge with `fastConcat` prior to rendering.
0 Image : Type
Image = SnocList String

||| Represent the regions to mask off from the clipped image plane.
0 ClipMask : Type
ClipMask = List Rect

||| True for cells chich should *not* be erased during clipping.
(.contains) : ClipMask -> Pos -> Bool
(.contains) mask pos = Prelude.any (flip (.contains) $ pos) mask

||| A context for drawing to the terminal.
|||
||| The context provides two drawing layers. `content` is the top-most
||| layer, and is always drawn completely, and always drawn last. The
||| `masked` layer is used to implement clipped drawing, as its name
||| would suggest, and is actually drawn first so that it can be
||| masked off.
export
record Context a where
  constructor C
  masked  : Image
  mask    : ClipMask
  content : Image
  value   : a

||| Write the given unescaped string to the context.
export
putStr : String -> Context ()
putStr string = C [<] [] [< string] ()

||| Write the given unescaped character to the context.
export
putChar : Char -> Context ()
putChar c = putStr $ singleton c

||| Erase the the masked area of the screen.
|||
||| This naive algorithm should be optimized later if need be.
clearMasked : Area -> ClipMask -> String
clearMasked _      []   = ""
clearMasked window mask =
  fastConcat $
    escapeSGR [Reset] :: -- reset all character attributes.
    blanks ++
    [eraseScreen End]
    -- ^ in case our window is smaller than the true screen size
    -- (e.g. because we don't handle SIGWINCH), clear any contents from
    -- the clip region that happen to lie outside the screen bounds.

  where
    -- write a blank character to any cell that is masked off.  we have
    -- to do this without the benefit of any abstractions defined here,
    -- since this runs in IO
    --
    -- this could be optimized to look for runs of blank space, and
    -- issue screen clear operations instead, but we'll wait until this
    -- is proven to be a bottleneck.
    blanks : List String
    blanks = do
      i <- [1 .. window.width]
      j <- [1 .. window.height]
      case mask.contains $ MkPos (natToInteger i) (natToInteger j) of
        True  => []
        False => [cursorMove i j, " "]

||| Paint the context to stdout.
export
present : ConsoleOutput io => Area -> Context a -> io a
present screen (C masked mask content value) = do
  writeStdout $ fastConcat $ toList masked
  writeStdout $ clearMasked screen mask
  writeStdout $ fastConcat $ toList content
  pure value

||| This is the internal clipping function which merely shifts the
||| image to the clipping layer. It does not clear the contents of the
||| clipping rectangle. Client code should use `clip` instead, and so
||| this function is deliberately private.
clip_ : Rect -> Context a -> Context a
clip_ r (C masked mask ops v) = C (masked ++ ops) (r :: mask) [<] v

-------------------------------------------------------------------------------
-- Make Context work with `do` notation
-------------------------------------------------------------------------------

||| Applies `f` to the value.
export
Functor Context where
  map f = {value $= f}

||| Sequencing two contexts combines their image layers and masks.
export
Applicative Context where
  pure x = C [<] [] [<] x
  f <*> (C masked mask content value) = C {
    -- Hopefully, this is the right order in which to concatenate the
    -- image layers. The mask is a set union, so the order doesn't
    -- matter.
    masked  = masked  ++ f.masked,
    mask    = mask    ++ f.mask,
    content = content ++ f.content,
    value   = f.value value
  }

||| Bind for Context merges the image layers and masks.
export
Monad Context where
  (C masked mask content value) >>= f =
    let next = f value
    in C {
    -- Hopefully, this is the right order in which to concatenate the
    -- image layers. The mask is a set union, so the order doesn't
    -- matter.
      masked  = masked  ++ next.masked,
      mask    = mask    ++ next.mask,
      content = content ++ next.content,
      value   = next.value
    }

-------------------------------------------------------------------------------
-- Drawing Routines which operate on the Context
-------------------------------------------------------------------------------

||| Debug printf for paint operations
export
debug : Show a => String -> a -> Context a
debug pf x = do
  -- cheat $ ignore $ fPutStrLn stderr $ "\{pf}: \{show x}"
  pure x

||| Move the cursor to the given point
export
moveTo : Pos -> Context ()
moveTo pos = putStr $ cursorMove (integerToNat pos.y) (integerToNat pos.x)

||| Draw text at the given point
export
showTextAt : Pos -> String -> Context ()
showTextAt pos x = do
  moveTo pos
  putStr x

||| Draw a single character at the given point.
export
showCharAt : Pos -> Char -> Context ()
showCharAt pos x = showTextAt pos (singleton x)

||| effectful version for setting arbitrary SGR attributes
export
sgr : List SGR -> Context ()
sgr = putStr . escapeSGR


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
      S n => hline (MkPos (x + 1) y) n

  ||| Draw a vertical line
  export
  vline : Pos -> Nat -> Context ()
  vline pos@(MkPos x y) height = do
    putAt pos V
    case height of
      Z   => pure ()
      S n => vline (MkPos x (y + 1)) n

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
  border : Rect -> Context ()
  border r = do
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

  ||| Draw the given context, but clipped to `window`.
  |||
  ||| This will:
  ||| - erase the `window` in the clipping area,
  ||| - add the `window` to the clipping mask,
  ||| - paint the original context into the clipping layer.
  export
  clip : Rect -> Context a -> Context a
  clip window ctx = clip_ window $ do
    fill ' ' window
    ctx

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
||| implementations, they are generic io actions, rather than context
||| actions.
namespace VTerm

  ||| Clear the contents of the screen.
  export %inline
  clearScreen : ConsoleOutput io => io ()
  clearScreen = writeStdout $ eraseScreen All

  ||| Switch into or out of the alternate screen buffer
  export %inline
  altScreen : ConsoleOutput io => Bool -> io ()
  altScreen True  = writeStdout $ "\ESC[?1049h"
  altScreen False = writeStdout $ "\ESC[?1049l"

  ||| Show or hide cursor
  export %inline
  cursor : ConsoleOutput io => Bool -> io ()
  cursor True  = writeStdout "\ESC[?25h"
  cursor False = writeStdout "\ESC[?25l"

  ||| Tell the terminal to save its state.
  export %inline
  saveCursor : ConsoleOutput io => io ()
  saveCursor = writeStdout "\ESC7"

  ||| Tell the terminal to restore its state.
  export %inline
  restoreCursor : ConsoleOutput io => io ()
  restoreCursor = writeStdout "\ESC8"

  ||| synchronous update Supported by iTerm2 and other fancy terminals
  export %inline
  beginSyncUpdate : ConsoleOutput io => io ()
  beginSyncUpdate = writeStdout "\ESC[?2026h"

  ||| synchronous update supported by iTerm2 and other fancy terminals
  export %inline
  endSyncUpdate : ConsoleOutput io => io ()
  endSyncUpdate = writeStdout "\ESC[?2026l"

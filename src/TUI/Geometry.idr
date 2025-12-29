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

||| Text-centric versions of geometric notions like Pos, Area, and
||| Rect.
module TUI.Geometry


import Data.Bits
import Derive.Prelude
import System
import TUI.Util
import TUI.Prim


%language ElabReflection
%default total


||| The location of a character cell on the screen.
public export
record Pos where
  constructor MkPos
  x : Integer
  y : Integer
%runElab derive "Pos" [Eq, Ord, Show]

||| The dimensions of a screen view
public export
record Area where
  constructor MkArea
  width : Nat
  height : Nat
%runElab derive "Area" [Eq, Ord, Show]

||| A rectangular screen region.
|||
||| This is a useful concept for layout. We can abstractly refer to
||| the different corners of the box.
public export
record Rect where
  constructor MkRect
  pos  : Pos
  size : Area
%runElab derive "Rect" [Eq, Ord, Show]


namespace Pos

  ||| Top-left screen corner
  public export
  origin : Pos
  origin = MkPos 1 1

  public export
  (.shiftRight) : Pos -> Nat -> Pos
  (.shiftRight) self offset = { x $= (+ (natToInteger offset)) } self

  public export
  (.shiftLeft) : Pos -> Nat -> Pos
  (.shiftLeft) self offset = { x $= ((flip (-)) (natToInteger offset)) } self

  public export
  (.shiftDown) : Pos -> Nat -> Pos
  (.shiftDown) self offset = { y $= (+ (natToInteger offset)) } self

  public export
  (.shiftUp) : Pos -> Nat -> Pos
  (.shiftUp) self offset = { y $= ((flip (-)) (natToInteger offset)) } self

namespace OverloadsPosAreaPos
  ||| Adding a point to an area returns a new point.
  public export
  (+) : Pos -> Area -> Pos
  (+) (MkPos x y) (MkArea w h) = MkPos (x + natToInteger w) (y + natToInteger h)

  public export
  (-) : Pos -> Area -> Pos
  a - v = MkPos (a.x - natToInteger v.width) (a.y - natToInteger v.height)

namespace OverloadsPosPosArea
  public export
  (-) : Pos -> Pos -> Area
  (-) a b = MkArea (a.x `diff` b.x) (a.y `diff` b.y)

namespace OverloadsIntegerPosPos
  public export
  (*) : Integer -> Pos -> Pos
  scalar * pos = MkPos (scalar * pos.x) (scalar * pos.y)

namespace OverloadsPosIntegerPos
  public export
  (*) : Pos -> Integer -> Pos
  pos * scalar = MkPos (scalar * pos.x) (scalar * pos.y)

namespace OverloadsNatAreaArea
  public export
  (*) : Nat -> Area -> Area
  scalar * area = MkArea (scalar * area.width) (scalar * area.height)

namespace OverloadsAreaNatArea
  public export
  (*) : Area -> Nat -> Area
  area * scalar = MkArea (scalar * area.width) (scalar * area.height)

||| A width and height without a location.
namespace Area
  ||| An empty area
  export
  empty : Area
  empty = MkArea 0 0

  ||| An area 1 row x 1 column
  export
  unit : Area
  unit = MkArea 1 1

  ||| Combine two areas to yield an area that contains both
  export
  union : Area -> Area -> Area
  union a b = MkArea (max a.width b.width) (max a.height b.height)

  ||| Pack areas vertically
  export
  hunion : Area -> Area -> Area
  hunion a b = MkArea (max a.width b.width) (a.height + b.height)

  ||| Pack areas horizontally
  export
  vunion : Area -> Area -> Area
  vunion a b = MkArea (a.width + b.width) (max a.height b.height)

  export
  (+) : Area -> Area -> Area
  a + b = MkArea (a.width + b.width) (a.height + b.height)

  export
  (-) : Area -> Area -> Area
  a - b = MkArea {
    width = (a.width `diff` b.width),
    height = (a.height `diff` b.height)
  }

  export
  (/) : Area -> Nat -> Area
  a / b = MkArea {
    width = (a.width `div` b),
    height = (a.height `div` b)
  }

||| Associated definitiosn for `Rect`.
namespace Rect
  ||| The width of a rectangle in columns
  export
  (.width) : Rect -> Nat
  (.width) self = self.size.width

  ||| The number of columns to span
  export
  (.hspan) : Rect -> Nat
  (.hspan) self = self.width `minus` 1

  ||| The height of a rectangle in rows
  export
  (.height) : Rect -> Nat
  (.height) self = self.size.height

  ||| The number of rows to span
  export
  (.vspan) : Rect -> Nat
  (.vspan) self = self.height `minus` 1

  ||| The column of the left side of the rect
  export
  (.w) : Rect -> Integer
  (.w) b = b.pos.x

  ||| The column of the east side of the rect
  export
  (.e) : Rect -> Integer
  (.e) b = b.pos.x + natToInteger b.hspan

  ||| The row of the north side of the rect
  export
  (.n) : Rect -> Integer
  (.n) b = b.pos.y

  ||| The row of the south side of the rect.
  export
  (.s) : Rect -> Integer
  (.s) b = b.pos.y + natToInteger b.vspan

  ||| Northwest corner of the given rect
  export
  (.nw) : Rect -> Pos
  (.nw) b = b.pos

  ||| Northeast corner of the given rect
  export
  (.ne) : Rect -> Pos
  (.ne) b = MkPos b.e b.n

  ||| Northwest corner of the given rect
  export
  (.se) : Rect -> Pos
  (.se) b = MkPos b.e b.s

  ||| Southwest corner of the given rect
  export
  (.sw) : Rect -> Pos
  (.sw) b = MkPos b.w b.s

  ||| Return the smallest rectangle which contains the two points.
  export
  fromPoints : Pos -> Pos -> Rect
  fromPoints a b = MkRect (min a b) (a - b)

  ||| Split from the left at `w` and return the pieces
  export
  (.splitLeft) : Rect -> Nat -> (Rect, Rect)
  (.splitLeft) b w =
    let
      left  = MkRect b.nw (MkArea w b.height)
      right = fromPoints (left.ne.shiftRight 1) (b.se + unit)
    in (left, right)

  ||| Split from the right at `w` and return the pieces
  export
  (.splitRight) : Rect -> Nat -> (Rect, Rect)
  (.splitRight) b w =
    let
      right = fromPoints (b.ne.shiftLeft (w `minus` 1)) (b.se + unit)
      left  = fromPoints b.nw $ right.sw.shiftDown 1
    in (left, right)

  ||| Split vertically from the top at `h` and return the pieces.
  export
  (.splitTop) : Rect -> Nat -> (Rect, Rect)
  (.splitTop) b h =
    let
      top = MkRect b.nw (MkArea b.width h)
      bot = fromPoints (top.sw.shiftDown 1) (b.se + unit)
    in (top, bot)

  ||| Split vertically from the top at `h` and return the pieces.
  export
  (.splitBottom) : Rect -> Nat -> (Rect, Rect)
  (.splitBottom) b h =
    let
      bot = fromPoints (b.sw.shiftUp (h `minus` 1)) (b.se + unit)
      top = fromPoints b.nw $ bot.ne.shiftRight 1
    in (top, bot)

  ||| The smallest bounding box fully containing both rectangles.
  export
  union : Rect -> Rect -> Rect
  union a b =
    let
      tl = min a.nw b.nw
      br = min a.se b.se
    in fromPoints tl br

  ||| Rectangles form a semigroup with the union operation.
  export
  Semigroup Rect where
    (<+>) = union

  export
  (+) : Rect -> Area -> Rect
  r + v = MkRect (r.nw + v) r.size

  export
  (-) : Rect -> Area -> Rect
  r - v = MkRect (r.nw - v) r.size

  ||| Position contents relative to the top left of container.
  export
  relativeTo : (container : Rect) -> (contents : Rect) -> Rect
  relativeTo (MkRect nw _) (MkRect offset size) =
    let pos = MkPos (nw.x + offset.x) (nw.y + offset.y)
    in MkRect pos size

  public export
  (.shiftRight) : Rect -> Nat -> Rect
  (.shiftRight) self offset = { pos $= (+ (MkArea offset 0)) } self

  public export
  (.shiftLeft) : Rect -> Nat -> Rect
  (.shiftLeft) self offset = { pos := (self.pos - (MkArea offset 0)) } self

  public export
  (.shiftDown) : Rect -> Nat -> Rect
  (.shiftDown) self offset = { pos $= (+ (MkArea 0 offset)) } self

  public export
  (.shiftUp) : Rect -> Nat -> Rect
  (.shiftUp) self offset = { pos := (self.pos - (MkArea 0 offset)) } self

  public export
  (.contains) : Rect -> Rect -> Bool
  (.contains) self r =
    case (
      self.n <= r.n,
      self.s >= r.s,
      self.e >= r.e,
      self.w <= r.w
    ) of
      (True, True, True, True) => True
      _ => False

  public export
  (.center) : Rect -> Pos
  (.center) r = r.nw + (r.size / 2)

namespace OverloadsRectPos

  public export
  (.contains) : Rect -> Pos -> Bool
  (.contains) self (MkPos x y) =
       (x >= self.w) && (x <= self.e)
    && (y >= self.n) && (y <= self.s)

public export
(.contains) : Rect -> Area -> Bool
(.contains) self a = case (self.width >= a.width, self.height >= a.height) of
  (True, True) => True
  _ => False

public export
(.centerOn) : Area -> Pos -> Rect
(.centerOn) area center = MkRect nw area
  where
    nw : Pos
    nw = center - (area / 2)

public export
(.centerIn) : Area -> Rect -> Rect
(.centerIn) self window = case window.contains self of
  False => window
  True  => self.centerOn window.center

||| A common default size of terminal window.
export
r80x24 : Rect
r80x24 = MkRect origin (MkArea 80 24)

||| Get the current window size from the kernel.
export
getWinSize : HasIO io => io Area
getWinSize = do
  rawBits <- primIO prim__getWinSize
  -- the support function packs these values into a bits32 to avoid
  -- unecessary memory management, so we need to unpack them here.
  let high = rawBits `shiftR` 16 .&. 0xFFFF
  let low  = rawBits .&. 0xFFFF
  pure $ MkArea (cast low) (cast high)

||| Get the window geometry
export
screen : HasIO io => io Rect
screen = pure $ MkRect origin !(liftIO getWinSize)

||| shrink the rectangle by the given size
export
inset : Rect -> Area -> Rect
inset self offset = {
  pos  $= (+ offset),
  size := self.size - (2 * offset)
} self

||| shrink the rectangle by the given size
export
outset : Rect -> Area -> Rect
outset self offset = {
  pos  := self.pos - offset,
  size := self.size + (2 * offset)
} self

||| Inset a rectangle uniformly by one row and column.
export
shrink : Rect -> Rect
shrink r = inset r $ MkArea 1 1

||| Inset a rectangle uniformly by one row and column.
export
grow : Rect -> Rect
grow r = outset r $ MkArea 1 1

namespace Test
  0 TestPos : Pos
  TestPos = MkPos 5 10

  0 TestWindow : Rect
  TestWindow = MkRect origin (MkArea 80 24)

  testShiftRight : ((.shiftRight) TestPos 5) = MkPos 10 10
  testShiftRight = Refl

  testShiftLeft : ((.shiftLeft) TestPos 5) = MkPos 0 10
  testShiftLeft = Refl

  testShiftDown : ((.shiftDown) TestPos 5) = MkPos 5 15
  testShiftDown = Refl

  testShiftUp : ((.shiftUp) TestPos 5) = MkPos 5 5
  testShiftUp = Refl

  testFromPoints
    : fromPoints Pos.origin (MkPos 81 25)
      = MkRect Pos.origin (MkArea 80 24)
  testFromPoints = Refl

  testPtAddition : (TestPos + MkArea 0 0) = TestPos
  testPtAddition = Refl

  testSplitLeft
    : ((.splitLeft) TestWindow 1)
    = (MkRect Pos.origin (MkArea 1 24), MkRect (MkPos 2 1) (MkArea 79 24))
  testSplitLeft = Refl

  testSplitRight
    : ((.splitRight) TestWindow 1)
    = (MkRect Pos.origin (MkArea 79 24), MkRect (MkPos 80 1) (MkArea 1 24))
  testSplitRight = Refl

  testSplitTop
    : ((.splitTop) TestWindow 1)
    = (MkRect Pos.origin (MkArea 80 1), MkRect (MkPos 1 2) (MkArea 80 23))
  testSplitTop = Refl

  testSplitBottom
    : ((.splitBottom) TestWindow 1)
    = (MkRect Pos.origin (MkArea 80 23), MkRect (MkPos 1 24) (MkArea 80 1))
  testSplitBottom = Refl

  testContains1
    : ((.contains) TestWindow TestWindow) = True
  testContains1 = Refl

  testContains2
    : ((.contains) TestWindow ((.shiftRight) TestWindow 1)) = False
  testContains2 = Refl

  testContains3
    : ((.contains) TestWindow ((.shiftRight) (shrink TestWindow) 1)) = True
  testContains3 = Refl

  testContains4
    : ((.contains) TestWindow ((.shiftDown) TestWindow 1)) = False
  testContains4 = Refl

  testContains5
    : ((.contains) TestWindow ((.shiftDown) (shrink TestWindow) 1)) = True
  testContains5 = Refl

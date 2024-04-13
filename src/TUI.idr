||| Minimalist terminal UI framework.
|||
||| I can't get ncurses-idris working, so I'm rolling this pure-idris
||| alternative.
|||
||| It's higher-level than ncurses, with the goal of being able to
||| quickly create keyboard-driven interfaces that are 'good enough'
||| for experimentation and prototyping, with an eye toward efficient
||| data entry.
|||
||| The lack of ncurses support does pose some challenges. In
||| particular, it's not possible to distinguish between the start of
||| an escape sequence or the user pressing the escape key, as there
||| is no non-blocking way to get the next character from stdin.
|||
||| Other limitations include:
||| - no support for termcap or terminfo,
|||   - no checking or fallback.
|||
||| The primary advantage is sheer simplicity: no dependencies are
||| required beyond `contrib`, so long as you rely on an
||| ANSI-compatible terminal or emulator.
module TUI


import Control.ANSI
import Data.Vect
import Data.Vect.Quantifiers
import System
import System.File
import System.Signal
import Derive.Prelude


%default total
%language ElabReflection


||| Functions to consider moving elsewhere
namespace Util

  ||| Truncate a string to the given length.
  public export
  truncateTo : Nat -> String -> String
  truncateTo n s = pack $ take n $ unpack s

  ||| Format a string into an exact width
  |||
  ||| Pad if length is shorter than width, truncate if longer.
  public export
  frameString : Nat -> String -> String
  frameString w s =
    let l = length s
    in case (l < length s) of
      True  => padRight w ' ' s
      False => truncateTo w s

  ||| Find the unsigned difference between two natural numbers.
  public export
  diff : Nat -> Nat -> Nat
  diff a b = case a < b of
    True  => b `minus` a
    False => a `minus` b

  ||| Decrement the given `Fin` without changing the bound.
  public export
  pred : Fin n -> Fin n
  pred FZ     = FZ
  pred (FS k) = weaken k

  ||| `unpack`, but for SnocLists
  public export
  kcapnu : String -> SnocList Char
  kcapnu s = cast $ unpack s

  ||| `pack`, but for SnocLists
  public export
  kcap : SnocList Char -> String
  kcap s = pack $ cast s

  ||| `tail` for SnocList
  public export
  liat : SnocList a -> SnocList a
  liat [<] = [<]
  liat (xs :< x) = xs

  ||| `head` for SnocList
  public export
  daeh : SnocList a -> Maybe a
  daeh [<] = Nothing
  daeh (xs :< x) = Just x

  ||| Return the tail part of a regular list.
  public export
  tail : List a -> List a
  tail [] = []
  tail (x :: xs) = xs

  ||| Map a function over a heterogenous vector.
  |||
  ||| Unlike mapProperty, the result is homogenous vector. This is
  ||| useful for extracting properties which don't vary with index
  ||| type.
  public export
  mapAll
    :  {k : Nat}
    -> {xs : Vect k a}
    -> (f : forall x. p x -> y)
    -> All p xs
    -> Vect k y
  mapAll f xs = forget $ mapProperty f xs

  ||| Fold over a heterogenous vector.
  |||
  ||| The result is collected into a single value.
  ||| f : map each generic value into a single concrete value
  ||| g : accumulate concrete values into a single result.
  public export
  reduceAll
    :  {k : Nat}
    -> {xs : Vect k a}
    -> (g : y -> y -> y)
    -> (f : forall x. p x -> y)
    -> y
    -> All p xs
    -> y
  reduceAll g f accum [] = accum
  reduceAll g f accum (x :: xs) = reduceAll g f (g accum (f x)) xs

  ||| Update the value at the index, without changing the type.
  public export
  updateAt
    :  {k : Nat}
    -> {xs : Vect k a}
    -> (i : Fin k)
    -> (f : forall x. p x -> p x)
    -> All p xs
    -> All p xs
  updateAt FZ     f (x :: xs) = f x :: xs
  updateAt (FS i) f (x :: xs) = x :: updateAt i f xs


||| Functions and types having to do with terminal escape sequences.
|||
||| This is best-effort, patches welcome.
namespace EscapeSequences

  ||| Wrapper type for tracking the escape sequences received from
  ||| STDIN.
  export
  data EscState state
    = HaveEsc (SnocList Char) state
    | Default state

  ||| Abstract key value, decoded from ANSI escape sequence.
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
  %runElab derive "Key" [Ord, Eq, Show]

  ||| Track escape sequences for the inner state.
  export
  wrapEsc : state -> EscState state
  wrapEsc = Default

  ||| Project the wrapped value from the escape sequence state.
  export
  unwrapEsc : EscState state -> state
  unwrapEsc (HaveEsc _ s) = s
  unwrapEsc (Default   s) = s

  ||| It's handy to be able to `show` the escape state for debugging.
  export
  Show s => Show (EscState s) where
    show = show . unwrapEsc

  ||| Decode well-known escape sequences into abstract keys.
  |||
  ||| In particular, we handle the cursor keys.
  export
  decodeEsc : SnocList Char -> Maybe (Maybe Key)
  decodeEsc [<]          = Just Nothing
  decodeEsc [< '[']      = Just Nothing
  decodeEsc [< '[', 'C'] = Just $ Just Right
  decodeEsc [< '[', 'D'] = Just $ Just Left
  decodeEsc [< '[', 'A'] = Just $ Just Up
  decodeEsc [< '[', 'B'] = Just $ Just Down
  decodeEsc [< '\ESC']   = Just $ Just Escape
  decodeEsc _            = Nothing

  ||| Interpret console escape sequences as keys.
  |||
  ||| Note: this falls down if the user presses the escape key, because
  ||| we can't tell the difference between the key press and the start
  ||| of an escape sequence. It'd be better to use ncurses.
  export
  interpretEsc
    :  (Key -> state -> Maybe state)
    -> Char
    -> EscState state
    -> Maybe (EscState state)
  interpretEsc f c (HaveEsc esc s) = case (decodeEsc $ esc :< c) of
    Just Nothing    => Just $ HaveEsc (esc :< c) s
    Just (Just Escape) => Nothing
    Just (Just key) => Default <$> (f key s)
    Nothing         => Just $ Default s
  interpretEsc f '\ESC' (Default s) = Just $ HaveEsc [<] s
  interpretEsc f '\DEL' (Default s) = map Default $ f Delete    s
  interpretEsc f '\n'   (Default s) = map Default $ f Enter     s
  interpretEsc f '\t'   (Default s) = map Default $ f Tab       s
  interpretEsc f c      (Default s) = map Default $ f (Alpha c) s


||| Text-centric versions of geometric notions like Pos, Area, and
||| Rect.
namespace Geometry
  ||| The location of a character cell on the screen.
  public export
  record Pos where
    constructor MkPos
    x : Nat
    y : Nat
  %runElab derive "Pos" [Eq, Ord, Show]

  ||| Top-left screen corner
  public export
  origin : Pos
  origin = MkPos 1 1

  ||| The dimensions of a screen view
  public export
  record Area where
    constructor MkArea
    width : Nat
    height : Nat
  %runElab derive "Area" [Eq, Ord, Show]

  ||| Adding a point to an area returns a new point.
  public export
  (+) : Pos -> Area -> Pos
  (+) (MkPos x y) (MkArea w h) = MkPos (x + w) (y + h)

  ||| The difference between two locations defines an area
  public export
  (-) : Pos -> Pos -> Area
  (-) a b = MkArea (a.x `diff` b.x) (a.y `diff` b.y)

  ||| A width and height without a location.
  namespace Area
    ||| Combine two areas to yield an area that contains both
    export
    union : Area -> Area -> Area
    union a b = MkArea (max a.width a.width) (max a.height b.height)

    ||| Pack areas vertically
    export
    hunion : Area -> Area -> Area
    hunion a b = MkArea (max a.width b.width) (a.height + b.height)

    ||| Pack areas horizontally
    export
    vunion : Area -> Area -> Area
    vunion a b = MkArea (a.width + b.width) (max a.height b.height)

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

  ||| Associated definitiosn for `Rect`.
  namespace Rect
    ||| Northwest corner of the given rect
    export
    (.nw) : Rect -> Pos
    (.nw) b = b.pos

    ||| Northeast corner of the given rect
    export
    (.ne) : Rect -> Pos
    (.ne) b = b.pos + MkArea b.size.width 0

    ||| Northwest corner of the given rect
    export
    (.se) : Rect -> Pos
    (.se) b = b.pos + b.size

    ||| Southwest corner of the given rect
    export
    (.sw) : Rect -> Pos
    (.sw) b = b.pos + MkArea 0 b.size.height

    ||| The column of the left side of the rect
    export
    (.w) : Rect -> Nat
    (.w) b = b.pos.x

    ||| The column of the east side of the rect
    export
    (.e) : Rect -> Nat
    (.e) b = b.pos.x + b.size.width

    ||| The row of the north side of the rect
    export
    (.n) : Rect -> Nat
    (.n) b = b.pos.y

    ||| The row of the south side of the rect.
    export
    (.s) : Rect -> Nat
    (.s) b = b.pos.y + b.size.height

    ||| Return the smallest rectangle which contains the two points.
    export
    fromPoints : Pos -> Pos -> Rect
    fromPoints a b = MkRect (min a b) (a - b)

    ||| Split horizontally at `w` and return the pieces
    export
    hsplit : Rect -> Nat -> (Rect, Rect)
    hsplit b w =
      let
        left  = MkRect b.nw (MkArea w b.size.height)
        right = fromPoints (b.nw + MkArea w 0) b.se
      in
        (left , right)

    ||| Split vertically at `h` and return the pieces
    export
    vsplit : Rect -> Nat -> (Rect, Rect)
    vsplit b h =
      let
        top = MkRect b.nw (MkArea b.size.width h)
        bot = fromPoints (b.nw + MkArea 0 h) b.se
      in
        (top , bot)

    ||| The smallest bounding box fully containing both rectangles.
    export
    union : Rect -> Rect -> Rect
    union a b =
      let
        tl = min a.nw b.nw
        br = min a.se b.se
      in
        fromPoints tl br

    ||| Rectangles form a semigroup with the union operation.
    export
    Semigroup Rect where
      (<+>) = union

  ||| A common default size of terminal window.
  export
  r80x24 : Rect
  r80x24 = MkRect origin (MkArea 80 24)

  ||| shrink the rectangle by the given size
  export
  inset : Rect -> Area -> Rect
  inset (MkRect (MkPos x y) (MkArea width height)) offset = MkRect {
    pos = MkPos {
      x = (x + offset.width),
      y = (y + offset.height)
    },
    size = MkArea {
      width = (width `minus` 2 * offset.width),
      height = (height `minus` 2 * offset.height)
    }
  }

  ||| Inset a rectangle uniformly by one row and column.
  export
  shrink : Rect -> Rect
  shrink r = inset r $ MkArea 1 1


||| Functions and related to putting text on the screen
namespace Painting
  ||| Move the cursor to the given point
  export
  moveTo : Pos -> IO ()
  moveTo pos = putStr $ cursorMove pos.y pos.x

  ||| Draw text at the given point
  export
  showTextAt : Pos -> String -> IO ()
  showTextAt pos x = do
    moveTo pos
    putStr x

  ||| Draw a single character at the given point.
  export
  showCharAt : Pos -> Char -> IO ()
  showCharAt pos x = showTextAt pos (singleton x)

  ||| Clear the contents of the screen via ANSI codes.
  export
  clearScreen : IO ()
  clearScreen = putStr $ eraseScreen All

  ||| Show the cursor
  export
  showCursor : IO ()
  showCursor = putStr "\ESC[?25h"

  ||| Hide cursor
  export
  hideCursor : IO ()
  hideCursor = putStr "\ESC[?25l"

  ||| Save the cursor state and position.
  |||
  ||| The standard only supports one level of save / restore. This
  ||| should be called once at application start.
  export
  saveCursor : IO ()
  saveCursor = putStr "\ESC7"

  ||| Save the cursor state and position.
  |||
  ||| The standard only supports one level of save / restore. This
  ||| should be called once at application end.
  export
  restoreCursor : IO ()
  restoreCursor = putStr "\ESC8"

  ||| This attribute isn't part of the ANSI library in contrib, but is
  ||| arguably more useful than setting explicit colors.
  export
  reverseVideo : IO ()
  reverseVideo = putStr "\ESC[7m"

  ||| Undoes the above
  export
  unreverseVideo : IO ()
  unreverseVideo = putStr "\ESC[27m"

  ||| effectful version for setting arbitrary SGR attributes
  export
  sgr : List SGR -> IO ()
  sgr = putStr . escapeSGR

  ||| Symbolic type for box drawing characters
  public export
  data BoxChar
    = NW
    | NE
    | SW
    | SE
    | H
    | V

  ||| Draw the corresponding box character
  export
  boxChar : Pos -> BoxChar -> IO ()
  boxChar pos NW = showCharAt pos $ cast 0x250C
  boxChar pos NE = showCharAt pos $ cast 0x2510
  boxChar pos SW = showCharAt pos $ cast 0x2514
  boxChar pos SE = showCharAt pos $ cast 0x2518
  boxChar pos H  = showCharAt pos $ cast 0x2500
  boxChar pos V  = showCharAt pos $ cast 0x2502

  ||| Draw a horizontal line
  export
  hline : Pos -> Nat -> IO ()
  hline pos@(MkPos x y) width = do
    boxChar pos H
    case width of
      Z   => pure ()
      S n => hline (MkPos (S x) y) n

  ||| Draw a vertical line
  export
  vline : Pos -> Nat -> IO ()
  vline pos@(MkPos x y) height = do
    boxChar pos V
    case height of
      Z   => pure ()
      S n => vline (MkPos x (S y)) n

  ||| Draw a box around the given rectangle
  |||
  ||| Use with `shrink` or `inset` to layout contents within the frame.
  export
  box : Rect -> IO ()
  box r = do
    -- draw the lines at full size
    hline r.nw r.size.width
    hline r.sw r.size.width
    vline r.nw r.size.height
    vline r.ne r.size.height
    -- paint over with the corners
    boxChar r.nw NW
    boxChar r.ne NE
    boxChar r.sw SW
    boxChar r.se SE


||| Associated definitions `View`.
namespace View
  public export
  data State = Normal | Focused | Disabled

  ||| A view is a high-level UI component.
  |||
  ||| - It wraps an inner value, its state.
  ||| - It knows how to size itself, for layout purposes.
  ||| - It can draw itself to the screen
  ||| - It can update its state in response to events.
  public export
  interface View state where
    ||| Calculate the "requested" size
    size  : state -> Area

    ||| Draw the view into the given screen rectangle.
    paint : View.State -> Rect -> state -> IO ()

    ||| Possibly update our state in response to a key press.
    |||
    ||| The default implementation is a no-op. Override this for
    ||| stateful view.
    handle : Key -> state -> state
    handle _ s = s

  ||| Implement `View` for `()` as a no-op
  export
  View () where
    size  _     = MkArea 0 0
    paint _ _ _ = pure ()

  ||| Any type implementing `Show` is automatically a (non-interative)
  ||| view.
  export
  Show a => View a where
    size s = MkArea (length (show s)) 1
    paint _ r s = showTextAt r.nw (show s)

  ||| In implementing `View` for all `Show` types, we have
  ||| inadvertently made it ambigious what to do when we use a string
  ||| as a view. This alternative, named implementation draws the
  ||| string directly to the screen.
  export
  [string] View String where
    size s = MkArea (length s) 1
    paint _ r = showTextAt r.nw


||| An interactive view which represents an exclusive choice.
|||
||| XXX: rename me
||| this should be a "spinner" or "chooser", or "combo"
record Menu a where
  constructor MkMenu
  n       : Nat
  choices : Vect n a
  choice  : Fin  n

||| Associated definitions for `Menu`
namespace Menu

  ||| A unicode up arrow
  upArrow : String
  upArrow = "⬆"

  ||| A unicode down arrow
  downArrow : String
  downArrow = "⬇"

  ||| A unicode up/down arrow
  upDownArrow : String
  upDownArrow = "⬍"

  ||| Show the arrow indicator most appropriate for the given as a
  ||| hint to the user which keys will be effective.
  |||
  ||| - 0     : down arrow
  ||| - last  : the up arrow
  ||| - other : the up-down arrow.
  arrowForIndex : {k : Nat} -> Fin k -> String
  arrowForIndex FZ     = downArrow
  arrowForIndex (FS n) =
    if FS n == last
    then upArrow
    else upDownArrow

  ||| View implementation for Menu
  |||
  ||| Up / Down is used to cycle through alternatives.
  ||| TBD: filter options based on text typed.
  export
  View a => View (Menu a) where
    size self =
      let width = foldl max 0 $ map (width . size) self.choices
      in MkArea (width + 2) $ height $ size $ index self.choice self.choices

    paint state rect self = do
      case state of
        Focused => reverseVideo
        Disabled => sgr [SetStyle Faint]
        _ => sgr [Reset]
      paint state (snd $ hsplit rect 2) (index self.choice self.choices)
      showTextAt rect.nw (arrowForIndex {k = self.n} self.choice)
      sgr [Reset]

    handle Up   state = { choice := pred state.choice } state
    handle Down state = { choice := finS state.choice } state
    handle _    state = state

  ||| Construct a menu from a vector of views
  export
  menu : {k : Nat} -> View a => Vect (S k) a -> Menu a
  menu {k} choices = MkMenu (S k) choices (natToFinLt 0)


||| An editable string
export
record TextInput where
  constructor MkTextInput

  ||| Characters left of the cursor. The tail of this list is the
  ||| insertion point.
  left   : SnocList Char

  ||| Characters right of the cursor.
  right  : List Char


namespace TextInput
  ||| Construct a text input from a string.
  export
  fromString : String -> TextInput
  fromString s = MkTextInput {
    left   = kcapnu s,
    right  = []
  }

  ||| get the string value from the text input.
  toString : TextInput -> String
  toString self = (kcap self.left) ++ (pack self.right)

  ||| Insert a character.
  insert : Char -> TextInput -> TextInput
  insert c = { left $= (:< c) }

  ||| Delete a character.
  export
  delete : TextInput -> TextInput
  delete = { left $= liat }

  ||| Move insertion point rightward
  goRight : TextInput -> TextInput
  goRight self = case self.right of
    []      => self
    x :: xs => {
      left  $= (:< x),
      right := xs
    } self

  ||| Move insertion point rightward
  goLeft : TextInput -> TextInput
  goLeft self = case self.left of
    [<]     => self
    xs :< x => {
      left  := xs,
      right $= (x ::)
    } self

  ||| Implement View for TextInput
  export
  View TextInput where
    -- Size is the sum of left and right halves
    size self = MkArea ((length self.left) + (length self.right)) 1

    -- when un-focused, just show the string value.
    paint Normal rect self = do
      showTextAt rect.nw (toString self)
    -- when disabled, show a faint string
    paint Disabled rect self = do
      sgr [SetStyle Faint]
      showTextAt rect.nw (toString self)
      sgr [Reset]
    -- when focused, show the cursor position in the string.
    paint Focused rect self = do
      moveTo rect.nw
      putStr $ kcap $ self.left
      reverseVideo
      putStr $ case self.right of
        [] => " "
        x :: _ => singleton x
      unreverseVideo
      putStr $ pack $ tail self.right

    -- map keys to their obvious functions.
    handle Left      = goLeft
    handle Right     = goRight
    handle Delete    = delete
    handle (Alpha c) = insert c
    handle _         = id


||| Associated definitions for `Form`.
namespace Form
  public export
  record Field ty where
    constructor F
    label : String
    view : ty
    {auto impl : View ty}

  viewSize : Field ty -> Area
  viewSize self = size @{self.impl} self.view

  ||| A form displays a set of views, each with a string label.
  |||
  ||| One field has focus, and user input is routed to this sub-view.
  export
  record Form (tys : Vect k Type) where
    constructor MkForm
    fields : All Field tys
    focused : Fin k
    split : Nat

  parameters {k : Nat} {tys : Vect k Type}
    views : All Field tys -> HVect tys
    views tys = mapProperty (.view) tys

    labels : All Field tys -> Vect k String
    labels tys = mapAll (.label) tys

    maxLabelWidth : All Field tys -> Nat
    maxLabelWidth tys = reduceAll max (length . (.label)) 0 tys

    ||| Calculate the size the form widgets (not including the labels)
    export
    sizeViewsVertical : All Field tys -> Area
    sizeViewsVertical fields = reduceAll vunion (viewSize) (MkArea 0 0) fields


  ||| Render the form vertically.
  export
  paintVertical : {k : Nat} -> {tys : Vect k Type} -> Rect -> Form tys -> IO ()
  paintVertical window (MkForm views focused split) = do
    vline (MkPos (window.w + split + 1) window.n) (window.size.height)
    loop 0 window views
    where
      loop : {k : Nat} -> {tys : Vect k Type} -> Nat -> Rect -> All Field tys -> IO ()
      loop _  _ [] = pure ()
      loop i  window (x :: xs) = do
        let (top, bottom) = vsplit window (viewSize x).height
        let (left, right) = hsplit top (split + 3)
        if i == (finToNat focused)
          then do
            sgr [SetStyle SingleUnderline]
            showTextAt left.nw x.label
            sgr [Reset]
            paint @{x.impl} Focused right x.view
          else do
            showTextAt left.nw x.label
            paint @{x.impl} Normal right x.view
        loop (S i) bottom xs

  parameters {k : Nat} {tys : Vect (S k) Type}
    ||| Dispatch keyboard input to the currently-focused subview.
    export
    handleNth : Fin (S k) -> Key -> All Field tys -> All Field tys
    handleNth i k fields = updateAt i (handleView k) fields
      where
        handleView : Key -> Field ty -> Field ty
        handleView k f = { view $= handle @{f.impl} k } f

    ||| Increment the choice by one.
    export
    nextChoice : Form tys -> Form tys
    nextChoice = { focused $= finS }

  ||| The View implementation for form renders each labeled sub-view
  ||| vertically.
  |||
  ||| The labels are left-justified, while the sub-views are
  ||| left-justified, and aligned relative to the widest label in the
  ||| form.
  |||
  ||| Only one sub-view has focus. Tab is used to move focus to the
  ||| next form field.
  export
  {k : Nat} -> {tys : Vect (S k) Type} -> View (Form tys) where
    size self = sizeViewsVertical self.fields

    paint state rect self = do
      box rect
      paintVertical (shrink rect) self

    handle Tab self = nextChoice self
    handle key self = {
      fields := handleNth self.focused key self.fields
    } self


  form
    : {k : Nat}
    -> {tys : Vect (S k) Type}
    -> All Field tys
    -> Form tys
  form fields = MkForm fields 0 $ maxLabelWidth fields + 3


||| Low-level TUI application mainloop.
|||
||| Manages terminal state, handles OS-level signals, and receives
||| keyboard events from STDIN.
|||
||| Use this entry point if you do not want escape-sequence decoding.
covering
runRaw
  :  (Char -> state -> Maybe state)
  -> (state -> IO Builtin.Unit)
  -> state
  -> IO state
runRaw handler render init = do
  -- default SigINT handler doesn't clean up raw mode, so we need to
  -- handle it explicitly and make sure to clean up.
  Right _ <- collectSignal SigINT
           | Left err => die "couldn't trap SigINT"

  -- run mainloop
  hideCursor
  saveCursor
  ret <- withRawMode err (loop init)
  cleanup
  pure ret
where
  -- restore terminal state as best we can
  cleanup : IO ()
  cleanup = do
    restoreCursor
    showCursor

  -- ensure we restore terminal state on IO error
  err : e -> IO state
  err _ = do
    cleanup
    die "an unhandled error occured"

  -- this is the actual recursive mainloop. The unusual `()` in the
  -- signature allows loop to be partially-applied above.
  loop : state -> () -> IO state
  loop s () = do
    -- repaint the screen with the current state
    clearScreen
    moveTo (MkPos 0 0)
    render s

    -- Return immediately if SigINT was received. Nothing, in this
    -- case, means no signal, so continue normal operation.
    --
    -- If we ever need to handle some other signal, like SIGWINCH,
    -- it would be done here.
    Nothing <- handleNextCollectedSignal
             | Just SigINT => pure s
             | Just _      => die "unexpected signal"

    -- handle next key press
    case handler !getChar s of
      Nothing => pure s -- we are done, quit
      Just s  => loop s () -- go to next iteration.


||| Run a raw TUI application, decoding input escape sequences.
|||
||| Use this function if you want escape sequence decoding, but do not
||| want to use the view abstraction for rendering screen contents.
covering export
runTUI
  :  (Key -> state -> Maybe state)
  -> (state -> IO ())
  -> state
  -> IO state
runTUI handler render init = do
  ret <- runRaw (interpretEsc handler) (render . unwrapEsc) (wrapEsc init)
  pure $ unwrapEsc ret


||| Run a TUI application.
|||
||| Use this entry point if you want to use the `View` abstraction.
covering export
runView : View state => state -> IO state
runView init = do
  let window = r80x24 -- XXX: get real window size
  result <- runTUI wrapView (paint Normal window) init
  pure result
where
  wrapView : Key -> state -> Maybe state
  wrapView k s = Just $ handle k s



--- tests

testMenu : Menu String
testMenu = menu ["foo", "bar", "baz"]

testForm : Form [Menu String, Menu String, TextInput, TextInput]
testForm = form [
  F "F1" testMenu,
  F "Long name" testMenu,
  F "Text Input" (fromString "test"),
  F "Test" (fromString "test")
]

partial export
test : IO ()
test = do
  v <- runView testForm
  putStrLn ""

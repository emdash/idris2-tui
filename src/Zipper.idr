||| Application-specific zipper for JSON data
|||
module Zipper


import Data.SnocList
import Util
import Derive.Prelude


%default total
%language ElabReflection


namespace List
  ||| A Zipper over a list of values
  public export
  record Zipper a where
    constructor Z
    ||| Characters left of the cursor.
    |||
    ||| The tail of this list is the insertion point.
    left   : SnocList a
    ||| Characters right of the cursor.
    right  : List a

  ||| Create a zipper from a list
  public export
  fromList : List a -> Zipper a
  fromList list = Z {
    left  = cast list,
    right = []
  }

  public export
  toList : Zipper a -> List a
  toList self = (toList self.left) ++ (toList self.right)

  ||| Insert a character.
  public export
  insert : a -> Zipper a -> Zipper a
  insert c = { left $= (:< c) }

  ||| Delete a character.
  export
  delete : Zipper a -> Zipper a
  delete = { left $= liat }

  ||| Move insertion point rightward
  public export
  goRight : Zipper a -> Zipper a
  goRight self = case self.right of
    []      => self
    x :: xs => {
      left  $= (:< x),
      right := xs
    } self

  ||| Move insertion point rightward
  public export
  goLeft : Zipper a -> Zipper a
  goLeft self = case self.left of
    [<]     => self
    xs :< x => {
      left  := xs,
      right $= (x ::)
    } self

  ||| Get the length of both halves of the zipper
  public export
  length : Zipper a -> Nat
  length self = length self.left + length self.right

||| Based on:
||| https://www.st.cs.uni-saarland.de/edu/seminare/2005/advanced-fp/docs/huet-zipper.pdf
||| https://pavpanchekha.com/blog/zippers/huet.html
|||
||| This is left here mainly for future reference. Since the item
||| types have to be the same, we can't really use this in TUI.
namespace Huet
  -- redefine this here so that unit tests will typecheck.
  data Key = Up | Down | Left | Right | Enter | Delete | Tab | Escape | Alpha Char

  export
  data Tree item
    = Item    item
    | Section (List $ Tree item)
  %runElab derive "Tree" [Show]

  ||| Huet's generic tree path
  |||
  ||| "A path is like a zipper, allowing one to rip the tree structure
  ||| down to a certain location."
  |||
  ||| "A Node(l,p,r) contains its list l of elder siblings (starting
  ||| with the eldest), its father path p, and its list of younger
  ||| siblings (starting with the youngest)."
  |||
  ||| "Note: a tree presented by a path has sibling trees, uncle trees,
  ||| great-uncle trees, etc. But its father is a path, not a tree like
  ||| in usual graph[ical?] editors."
  export
  data Path item
    = Top
    | Node (List $ Tree item) (Path item) (List $ Tree item)
  %runElab derive "Path" [Show]

  ||| Huet's generic tree location
  |||
  ||| "A location consists of a distinguished tree, the current focus of
  ||| attention, and its path, representing its surrounding
  ||| context. Note that a location does *not* correspond to an
  ||| occurrence in the tree, ... rather [it is] a pointer to the arc
  ||| linking the designated subtree to the surrounding context.
  export
  record Cursor item where
    constructor Loc
    subtree: Tree item
    path: Path item
  %runElab derive "Cursor" [Show]

  ||| Move the zipper to the left.
  export
  goLeft : Cursor item -> Either String (Cursor item)
  goLeft (Loc t p) = case p of
    Top                       => Left "Left of Top"
    Node (l :: left) up right => Right $ Loc l $ Node left up $ t :: right
    Node []          up right => Left "Left of First"

  ||| Move the zipper to the right.
  export
  goRight : Cursor item -> Either String (Cursor item)
  goRight (Loc t p) = case p of
    Top                       => Left "Right of Top"
    Node left up (r :: right) => Right $ Loc r $ Node (t :: left) up right
    _                         => Left "Right of Last"

  ||| Move the zipper upwards
  export
  goUp : Cursor item -> Either String (Cursor item)
  goUp (Loc t p) = case p of
    Top                => Left "Up from Top"
    Node left up right => Right $ Loc (Section $ reverse left ++ t :: right) up

  ||| Move the zipper down
  export
  goDown : Cursor item -> Either String (Cursor item)
  goDown (Loc t p) = case t of
    Item    _             => Left "Down from Item"
    Section (t1 :: trees) => Right $ Loc t1 $ Node [] p trees
    _                     => Left "Down from Empty"

  ||| Get the nth child of the current tree.
  export
  nth : Cursor item -> Nat -> Either String (Cursor item)
  nth loc 0     = Left "Ntth Expects a positive integer"
  nth loc 1     = goDown  loc
  nth loc (S n) = goRight !(nth loc n)

  ||| Mutate the structure at the current location.
  export
  update : Cursor item -> Tree item -> Cursor item
  update (Loc _ p) t = Loc t p

  export
  insert : Cursor item -> Tree item -> Either String (Cursor item)
  insert l t = Right $ update l t

  export
  insertRight : Cursor item -> Tree item -> Either String (Cursor item)
  insertRight (Loc t p) r = case p of
    Top                => Left "Insert above top"
    Node left up right => Right $ Loc t $ Node left up $ r :: right
  export
  insertLeft : Cursor item -> Tree item -> Either String (Cursor item)
  insertLeft (Loc t p) r = case p of
    Top                => Left "Insert above top"
    Node left up right => Right $ Loc t $ Node left up right

  export
  insertDown : Cursor item -> Tree item -> Either String (Cursor item)
  insertDown (Loc t p) r = case t of
    Item _             => Left "Insert below leaf"
    Section children   => Right $ Loc t $ Node [] p children

  export
  delete : Cursor item -> Either String (Cursor item)
  delete (Loc _ p) = case p of
    Top   => Left "Delete of Top"
    Node left up  (r :: right) => Right $ Loc r $ Node left up right
    Node (l :: left) up []     => Right $ Loc l $ Node left up []
    Node [] up []              => Right $ Loc (Section []) up

  namespace Test
    testT : Tree Char
    testT =
      Section [
        Section [
          Item 'a',
          Item '*',
          Item 'b'
        ],
        Item '+',
        Section [
          Item 'c',
          Item '*',
          Item 'd'
        ]
      ]

    public export
    0 Result : Type -> Type
    Result r = (Maybe String, r)

    ignoreErrs : r -> Either String r -> Result r
    ignoreErrs def (Left l)  = (Just l, def)
    ignoreErrs _   (Right r) = (Nothing, r)

    export
    test : Key -> Result (Cursor Char) -> Maybe (Result (Cursor Char))
    test (Alpha c) (_, cursor) = Just $ ignoreErrs cursor $ insert  cursor (Item c)
    test Right     (_, cursor) = Just $ ignoreErrs cursor $ goRight cursor
    test Left      (_, cursor) = Just $ ignoreErrs cursor $ goLeft  cursor
    test Up        (_, cursor) = Just $ ignoreErrs cursor $ goUp    cursor
    test Down      (_, cursor) = Just $ ignoreErrs cursor $ goDown  cursor
    test Delete    (_, cursor) = Just $ ignoreErrs cursor $ delete cursor
    test Enter     (_, cursor) = Just $ (Nothing, cursor)
    test Tab       (_, cursor) = Just $ (Nothing, cursor)
    test Escape    (_, cursor) = Nothing
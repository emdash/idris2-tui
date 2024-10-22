module Main

import JSON
import JSON.Derive
import System
import System.File
import System.File.ReadWrite
import System.File.Virtual
import TUI
import TUI.MainLoop
import TUI.MainLoop.Default
import TUI.Zipper.List

%default total
%language ElabReflection


||| An Item in a user's todo-list
record Item where
  constructor I
  description : String
  completed   : Bool
%runElab derive "Item" [Show, Eq, Ord, FromJSON, ToJSON]

View Item where
  size self = size @{show} self.description
  paint state window self = paint @{show} state window self.description

||| A component for editing the todolist
todoList : List Item -> Component (List Item)
todoList items = component (fromList header items) onKey (Just . toList) where
  header : String
  header = "Description"

  onKey : Component.Handler (VList Item) (List Item) Key
  onKey key _ = exit

covering
fromFile : String -> IO (Maybe (List Item))
fromFile path = do
  Right contents <- readFile path | Left err => pure Nothing
  case decode contents of
    Left  err      => pure Nothing
    Right contents => pure $ Just contents

covering
toFile : String -> List Item -> IO ()
toFile path todolist = do
  ignore $ writeFile path $ encode todolist

covering
run : String -> IO ()
run path = do
  items <- fromFile path
  case !(runComponent !getDefault (todoList (fromMaybe [] items))) of
    Nothing => pure ()
    Just items => toFile path items

covering
main : IO ()
main = do
  case !getArgs of
    [_]       => die "No path given"
    [_, path] => run path
    _         => die "Expected exactly one argument."

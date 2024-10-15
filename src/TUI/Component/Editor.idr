||| Minimalist terminal UI Framework
|||
||| A Component for editing values.
|||
||| XXX: It's unclear if this component still serves a purpose or if
||| the `Modal` mechanism makes it obsolete. However, it's used by
||| `Form` at the moment, so it stays.
module TUI.Component.Editor


import Data.Maybe
import Data.String
import TUI.Component
import Util
import TUI.Zipper.List


%default total


||| A component for editing arbitrary values.
|||
||| An `Editor` can be in one of three states:
||| @ Empty    An uninitialized value.
||| @ Editing  Currently editing a value.
||| @ Accepted Holds a legal value, and possibly the last editor state.
public export
data Editor valueT
  = Empty    String
  | Editing  (Component valueT) (Maybe valueT)             String
  | Accepted valueT             (Maybe (Component valueT)) String

||| Defines how to create an editor for a value.
|||
||| XXX: this interface may be obsolete with the new component
||| arch.
public export
interface
     View valueT
  => Editable valueT
where
  constructor MkEditable
  fromValue  : valueT -> Component valueT
  toValue    : Component valueT -> Maybe valueT
  blank      : Component valueT

||| Get the current value out of the editor.
|||
||| If in the empty state, returns Nothing. If in the editing state,
||| returns the current value if it parses, or the cached value if
||| available. If in the accepted state, returns the accepted value.
export
(.value)
  :  Editable valueT
  => Editor valueT
  -> Maybe valueT
(.value) (Empty        _) = Nothing
(.value) (Editing  x y _) = toValue x <+> y
(.value) (Accepted x y _) = Just x


||| Get the placeholder value from the editor.
export
(.placeholder)
  :  Editable valueT
  => Editor valueT
  -> String
(.placeholder) (Empty        ph) = ph
(.placeholder) (Editing  _ _ ph) = ph
(.placeholder) (Accepted _ _ ph) = ph

||| Construct an empty editor.
export
empty : String -> Editor _
empty placeholder = Empty placeholder

||| Construct an editor initialized to a value.
export
accepted : a -> String -> Editor a
accepted value placeholder = Accepted value Nothing placeholder

||| Construct an editor in the editing state.
export
editing
  :  Editable valueT
  => valueT
  -> String
  -> Editor valueT
editing value ph = Editing (fromValue value) (Just value) ph

||| Transition to the editing state.
|||
||| This will re-use the previous editing state if one exists,
||| otherwise it will construct the editor from a value.
|||
||| Has no effect if already editing.
export
edit
  :  Editable valueT
  => Editor valueT
  -> Editor valueT
edit (Empty               ph) = Editing (blank {valueT = valueT}) Nothing  ph
edit (Accepted v Nothing  ph) = Editing (fromValue v)             (Just v) ph
edit (Accepted v (Just e) ph) = Editing e                         (Just v) ph
edit self                     = self

||| Try to transition to the Accepted state with the current value.
|||
||| If this succeeds, preserves editing state. If this fails, remains
||| in the editing state.
export
accept
  :  Editable valueT
  => valueT
  -> Editor valueT
  -> Editor valueT
accept value self@(Editing e v ph) = Accepted value (Just e) ph
accept _ self = self

||| Leave the editing state, restoring previous value if present.
export
rollback
  :  Editable valueT
  => Editor valueT
  -> Editor valueT
rollback (Editing _ Nothing  ph) = Empty ph
rollback (Editing e (Just v) ph) = Accepted v (Just e) ph
rollback self                    = self

||| Update the component when a value is merged into the editor
||| subcomponent.
merge : Component valueT -> Editor valueT -> Editor valueT
merge e (Editing  _ v str) = Editing  e v        str
merge e (Accepted v _ str) = Accepted v (Just e) str
merge _ self               = self

||| Editor implements View for any Editable type
export
Editable valueT => View (Editor valueT) where
  size (Empty placeholder)  = size placeholder
  size (Editing e _ _)      = size e
  size (Accepted value _ _) = size value

  paint state window self = case self of
    (Empty    placeholder) => paint state window placeholder
    (Editing  editor _ _)  => paint state window editor
    (Accepted value _ _)   => paint state window value

export
handle : Editable valueT => Component.Handler (Editor valueT) valueT
handle key self = case self of
  Empty        _ => handleDefault key
  Editing  c y _ => handleEditing c
  Accepted x y _ => handleDefault key
where
  handleDefault : Key -> IO $ Response (Editor valueT) valueT
  handleDefault Enter  = update $ edit self
  handleDefault Escape = exitWith self.value
  handleDefault _      = ignore

  onMerge
    :  (Maybe a -> Component valueT)
    -> (Maybe a -> Editor valueT)
  onMerge f result = merge (f result) self

  handleEditing : Component valueT -> IO $ Response (Editor valueT) valueT
  handleEditing editor = case !(handle key editor) of
    Continue x => update $ Editing !x self.value self.placeholder
    Yield    x => update $ accept x self
    Exit       => update $ rollback self
    (Push x f) => push x $ onMerge f -- see note below

-- The editor may itself delegate to modal components, so we need to
-- ensure that the inner editor component is updated in response.

||| Construct a new editor for the given value, returning its concrete
||| type.
export
new : Editable valueT => Maybe valueT -> String -> Editor valueT
new Nothing  placeholder = empty placeholder
new (Just v) placeholder = accepted v placeholder

||| Construct a new editor as an opaque component.
export
editor
  :  Editable valueT
  => Maybe valueT
  -> String
  -> Component valueT
editor value placeholder  = component (new value placeholder) handle

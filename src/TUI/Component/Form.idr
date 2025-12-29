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

||| A form is an editor for a heterogenous list of values.
module TUI.Component.Form

-- XXX: figure out what code breaks when these imports are made private.
import public Data.Vect
import public Data.Vect.Quantifiers
import TUI.Component
import TUI.Component.Editor
import TUI.Component.FocusRing
import TUI.Layout
import TUI.View
import TUI.Zipper.List
import TUI.Util


%default total


||| A field is a labeled Component.
|||
||| Use the `F` constructor if you want control over which component
||| is used. To use the default component for a particular type, see
||| the `field` function.
public export
record Field {0 events : List Type} valueT where
  constructor F
  label : String
  value : Component (HSum events) valueT

||| Contruct a field using the default component for the given value type.
|||
||| @label       The field label
||| @value       An optional initial value to populate the field.
||| @placeholder The placeholder string to use for an empty field.
|||
||| A field can be constructed for any type implementing `Editable`.
export
field
  :  {0 events : List Type}
  -> Has Key events
  => Editable events valueT
  => String
  -> Maybe valueT
  -> Field {events} valueT
field label value = F label $ editable value

||| Paint a single field.
|||
||| @split  The horizontal position to align field values to.
||| @state  The drawing state, as with any paint function.
||| @window The screen area to paint to, as with any paint function.
||| @self   The field value to paint.
|||
||| The label and contents are justified according to the split value.
export
paintField
  :  Nat
  -> State
  -> Rect
  -> Field valueT
  -> Context ()
paintField split state window self = do
  let (left, right) = window.splitLeft split
  case state of
    Focused => do
      sgr [SetStyle SingleUnderline]
      showTextAt left.nw self.label
      sgr [Reset]
      paint Focused right self.value
    state => do
      withState state $ showTextAt left.nw self.label
      paint state right self.value

||| Handle input for a single field.
|||
||| This just wraps the updates of the underlying `Editor`.
handleField
  :  {0 events : List Type}
  -> Component.Handler (Field {events} valueT) valueT (HSum events)
handleField event self = case !(handle event self.value) of
  Continue state => update $ {value := !state} self
  Yield result   => yield result
  Exit           => exit
  Push top merge => push top (onMerge merge)
where
  ||| Some boilerplate:
  ||| Proxy this modal merge back down to the underlying editor.
  onMerge : (Maybe a -> Component (HSum events) valueT) -> Maybe a -> Field {events} valueT
  onMerge merge result = {value := merge result} self

||| The focus state of a form
data FocusState = Edit | Submit | Cancel

||| XXX: This is some boilerplate right here. There should be a
||| component for this.
View FocusState where
  size _ = View.size "[Cancel] [Submit]"
  paint state window self = do
    window <- packRight submitState window "[Submit]"
    window <- packRight Normal      window " "
    ignore $  packRight cancelState window "[Cancel]"
  where
    submitState : State
    submitState = case self of
      Submit => Focused -- XXX: show as disabled when form is invalid
      _      => (demoteFocused state)

    cancelState : State
    cancelState = case self of
      Cancel => Focused
      _      => (demoteFocused state)

||| A form is a heterogenous container of labeled components.
|||
||| Form fields are placed automatically.
|||
||| Exactly one form field is focused at all times.
|||
||| The form has two states: editing and navigation. When in editing,
||| events pass to the selected form field. When in navigation mode,
||| events modify the form itself.
export
record Form {0 events : List Type} (tys : Vect k Type) where
  constructor MkForm
  fields : FocusRing {events} tys
  split  : Nat
  focus  : FocusState

||| When used, it aligns fields to the split value of the parent form.
implementation [splitAt]
     {split : Nat}
  -> View (Field valueT)
where
  size self = vunion (MkArea split 1) (size self.value)
  paint = paintField (split + 2)

||| View implementation for `Form`
export
implementation
     {k : Nat}
  -> {tys : Vect (S k) Type} -- see note below
  -> View (Form tys)
where
  size self = vunion (size @{vertical} self.fields) (size self.focus)
  paint state window self = do
    vline (window.nw.shiftRight (cast $ self.split + 1)) window.height
    ignore $ packTop @{vertical} fieldsState window self.fields
    ignore $ packBottom state window self.focus
  where
    fieldsState : State
    fieldsState = case self.focus of
      Edit   => state
      _      => demoteFocused state

||| Advance to the next component.
|||
||| When we reach the end of the field list, focus transfers to the
||| cancel button, then the submit button, then wraps back around to
||| the first component.
export
next
  :  {0 events : List Type}
  -> {k : Nat}
  -> {tys : Vect (S k) Type}
  -> Form {events} tys
  -> Form {events} tys
next self = case self.focus of
  Edit => if self.fields.selection == last
    then {focus := Cancel} self
    else {fields $= next} self
  Cancel => {focus := Submit} self
  Submit => {focus := Edit, fields $= choose 0} self

||| This handler trys to follow typical ARIA keybindings.
|||
||| We can't completely support ARIA patterns until the the library
||| implements support for modifier keys (e.g. Shift + TAB).
|||
||| For now, tab moves focus. Escape exits the form. Enter is proxied
||| to the form field which has focus, or if the submit button is
||| focused, will yield the form value.
|||
||| If a form field yields, we advance to the next field, so that
||| `Enter` in most stock components will also happen to do the right
||| thing. Something about this bothers me, but we'll try it like this
||| for now.
|||
||| XXX: to explore: is this necessary, or does the default handler of
||| the new FocusRing component do the job for us?
ariaKeys
  :  {0 events : List Type}
  -> Has Key events
  => {k : Nat}
  -> {tys : Vect (S k) Type}
  -> Single.Handler {events} (Form {events} tys) (HVect tys) Key
ariaKeys key self = case (key, self.focus) of
  (Tab,     _)     => update $ next self
  (Escape,  _)     => exit
  (_,      Edit)   => handleEdit
  (Enter,  Submit) => onSubmit
  (Enter,  Cancel) => exit
  _                => ignore
where
  validate : All Maybe a -> Maybe (HVect a)
  validate [] = Just []
  validate (x :: xs) = case isItJust x of
    Yes _ => (fromJust x ::) <$> validate xs
    No _  => Nothing

  onMerge : (Maybe a -> FocusRing {events} tys) -> Maybe a -> Form {events} tys
  onMerge merge result = {fields := merge result} self

  handleEdit : IO $ Response (HSum events) (Form {events} tys) (HVect tys)
  handleEdit = case !(handleSelected {events} (inject key) self.fields) of
    Continue state => update $ {fields := !state} self
    Yield _        => update $ next self
    Exit           => ignore
    Push top merge => push top $ onMerge merge

  ||| validate form fields
  onSubmit : IO $ Response (HSum events) (Form {events} tys) (HVect tys)
  onSubmit = case allIsJust self.fields.values of
    Nothing     => ignore
    Just values => yield values

||| Construct a concrete form from a list of fields.
|||
||| @k        The number of fields.
||| @tys      The type of each field.
||| @fields   The concrete list of fields
export
new
  :  {0 events : List Type}
  -> {k : Nat}
  -> {tys : Vect (S k) Type}
  -> (fields : All (Field {events}) tys)
  -> Form {events} tys
new fields = MkForm (new mkfields 0) maxLabelWidth Edit
  where
    ||| Get the character width of the longest label in the form.
    maxLabelWidth : Nat
    maxLabelWidth = reduceAll max (length . label) 0 fields

    ||| Construct a component for a single field.
    |||
    ||| `splitAt` is the `View` implementation which correctly
    ||| aligns the field content to our split value.
    |||
    ||| Editable is the implementation required for `splitAt` to work.
    mkfield : Field {events} valueT -> Component (HSum events) valueT
    mkfield f = component @{splitAt {split = maxLabelWidth}} {
      state   = f,
      handler = handleField,
      get     = ((.value) . (.value))
    }

    ||| Convert the input list of fields to a list of components.
    mkfields : All (Component (HSum events)) tys
    mkfields = mapProperty mkfield fields

||| Construct a form component that uses ARIA keys for navigation.
|||
||| @k        The number of fields.
||| @tys      The type of each field.
||| @fields   A list of values to populate the form.
|||
||| The value of the form is yielded to the parent when the user
||| explicitly submits the form value. Directly retrieving the value
||| via (.value) is not supported at this time.
export
ariaForm
  :  {0 events : List Type}
  -> Has Key events
  => {k : Nat}
  -> {tys : Vect (S k) Type}
  -> (fields : All (Field {events}) tys)
  -> Component (HSum events) (HVect tys)
ariaForm fields = component {
  stateT  = Form {events} tys,
  state   = new {events} fields,
  handler = only ariaKeys,
  get     = unavailable -- see note above
}

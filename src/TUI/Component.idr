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

||| Support for self-contained UI elements.
module TUI.Component


import public TUI.View
import public TUI.Event
import public TUI.Key

%default total

||| The result of handling an event within a component.
|||
||| This type extends `Extends.Result` with the `Push` case, which
||| signals that control should pass to a child component. Because
||| `Push` takes a component as a parameter, it must be defined in
||| this module.
|||
||| Note: this type is forward-declared, because mutual blocks do not
||| work with records, owing to a bug in Idris.
public export data Response : Type -> Type -> Type -> Type

||| A function which handles an event in a component.
|||
||| There are two variants: `Component.Handler` and `User.Handler`.
|||
||| Note: this type alias is forward-declared, because mutual blocks
||| do not workw ith records, owing to a bug in Idris.
public export
0 AbstractHandler
  :  (stateT       : Type)
  -> (valueT       : Type)
  -> (globalEventT : Type)
  -> (localEventT  : Type)
  -> Type

||| This type is the top-level event handler within a component.
|||
||| This is distinct from `Event.Handler` in that it returns a
||| `Response` rather than a `Result`. Because it is top-level, the
||| local and and global event types must agree.
public export
0 Handler
  :  (stateT : Type)
  -> (valueT : Type)
  -> (eventT : Type)
  -> Type
Handler stateT valueT eventT = AbstractHandler stateT valueT eventT eventT

||| A reusable user-interface element.
|||
||| Component is closely tied to `Stack` and `Modal`.
public export covering
record Component eventT valueT where
  constructor MkComponent
  0 State : Type
  state   : State
  handler : Component.Handler State valueT eventT
  get     : State -> Maybe valueT
  vimpl   : View State

-- implementations for forward-declared types

public export
data Response eventT stateT valueT
  = Continue (IO stateT)
  | Yield (IO (Maybe valueT))
  | Push (Component eventT a) (Maybe a -> stateT)

AbstractHandler stateT valueT globalT localT =
  localT -> stateT -> IO $ Response globalT stateT valueT

||| Get the value from the component, if it is available.
export
(.value) : Component eventT valueT -> Maybe valueT
(.value) self = self.get self.state

-- Hide this projection function. we use (.state) instead. This
-- suppresses warnings about `state` being shadowed in the definitions
-- below.
%hide Component.state

||| A component wraps a View, so a component is also a view.
export
View (Component _ _) where
  size self = size @{self.vimpl} self.state
  paint state window self = paint @{self.vimpl} state window self.state


||| These definitions make writing event handlers a bit nicer.
namespace ComponentDSL

  ||| A generic response: update with the given IO action.
  export
  continue : IO stateT -> IO (Response _ stateT _)
  continue state = pure $ Continue $ state

  ||| A generic response: update with the given value.
  export
  update : stateT -> IO (Response _ stateT _)
  update state = pure $ Continue $ pure state

  ||| A generic response: yield given value to the parent, or exit.
  export
  yield : valueT -> IO (Response _ _ valueT)
  yield value = pure $ Yield $ pure $ Just value

  ||| A generic response: exit.
  export
  exit : IO (Response _ _ valueT)
  exit = pure $ Yield $ pure Nothing

  ||| A generic response: yield or exit, depending on argument.
  export
  exitWith : Maybe valueT -> IO (Response _ _ valueT)
  exitWith Nothing  = exit
  exitWith (Just v) = yield v

  ||| A generic response: do nothing.
  export
  ignore : {auto self : stateT} -> IO (Response _ stateT _)
  ignore = update self

  ||| A generic response: yield if value is `Just`, ignore if nothing
  export
  exitIf : {auto self : stateT} -> Maybe valueT -> IO (Response _ stateT valueT)
  exitIf Nothing  = ignore
  exitIf (Just v) = yield v

  ||| A generic response: pass control to the given child component.
  |||
  ||| When the component yields or exits, the result is folded into the
  ||| current component via `merge`.
  export
  push
    :  {0 eventT : Type}
    -> (top   : Component eventT topT)
    -> (merge : Maybe topT -> stateT)
    -> IO (Response eventT stateT valueT)
  push top merge = pure $ Push top merge

  ||| A getter function which always returns Nothing
  |||
  ||| This is for components which cannot yield a partial value, or
  ||| which are still in development.
  export
  unavailable : stateT -> Maybe valueT
  unavailable _ = Nothing

||| Update a component in response to an event.
|||
||| This wraps the stored handler, which operates on `State`, turning
||| it into the component-level handler which is needed by client
||| code.
export
handle : Component.Handler (Component eventT valueT) valueT eventT
handle event self = case !(self.handler event self.state) of
  Continue state => update $ {state := !state} self
  Yield result   => pure $ Yield result
  Push top merge => push top $ updateInner merge
where
  updateInner : (Maybe a -> self.State) -> Maybe a -> Component eventT valueT
  updateInner merge result = {state := merge result} self

||| Construct a component.
|||
||| This takes a concrete type, view implementation, event handler,
||| and value accessor, returning an opaque value that reveals only
||| its value type and event type.
|||
||| Component is used extensively in this library to provided
||| re-usable building blocks for UIs.
export
component
  :  (vimpl    : View stateT)
  => (state    : stateT)
  -> (handler  : Component.Handler stateT valueT eventT)
  -> (get      : stateT -> Maybe valueT)
  -> Component eventT valueT
component {vimpl} init handler get = MkComponent {
  State = stateT,
  state = init,
  handler = handler,
  get = get,
  vimpl = vimpl
}

namespace Single
  ||| An event handler for a union of event types.
  public export
  0 Handler
    :  {0 events : List Type}
    -> (stateT   : Type)
    -> (valueT   : Type)
    -> (eventT   : Type)
    -> Type
  Handler stateT valueT eventT = AbstractHandler {
    stateT       = stateT,
    valueT       = valueT,
    globalEventT = HSum events,
    localEventT  = eventT
  }

  ||| Compose multiple `Single.Handler`s into a `Component.Handler`.
  export
  union
    :  {0 events : List Type}
    -> {0 stateT, valueT : Type}
    -> All (Single.Handler {events} stateT valueT) events
    -> Component.Handler stateT valueT (HSum events)
  union handlers event state = go handlers event state
    where
      -- subtle stuff here: globalEventT must always be `HSum events`,
      -- while `localEventT` must be free to vary, as we recurse.
      go
        :  All (Single.Handler {events} stateT valueT) a
        -> AbstractHandler stateT valueT (HSum events) (HSum a)
      go (h :: _ ) (Here  e) s = h e s
      go (_ :: hs) (There e) s = go hs e s

  ||| A dummy handler, for use with `union`.
  export
  unhandled : (0 eventT : Type) -> Single.Handler stateT valueT eventT
  unhandled _ event self = ignore

  ||| Lift a handler for a single event into a handler for a union.
  export
  only
    :  {0 events : List Type}
    -> Has eventT events
    => Single.Handler {events} stateT valueT eventT
    -> Component.Handler stateT valueT (HSum events)
  only wrapped event state = case the (Maybe eventT) $ project' event of
    Nothing => ignore
    Just key => wrapped key state


||| Take a `Component _ a` to a `Component _ b` via `f`.
|||
||| This is useful for specializing library components to
||| application-specific types.
|||
||| The function `f` applies only to the yield value, leaving the
||| internal state and interactive behavior unchanged.
|||
||| Example: Take a generic numeric component and produce a
||| length. Here, `(.mm`) is a function `Double -> Length`.
|||
|||    inputMM : Length -> Component Length
|||    inputMM length = (.mm) <$> numeric (length.convertTo MilliMeters)
export
Functor (Component eventT) where
  map f wrapped = component @{wrapped.vimpl} wrapped.state handle get
    where
      get : wrapped.State -> Maybe b
      get self = f <$> wrapped.get self

      handle : Component.Handler wrapped.State b eventT
      handle event state = case !(wrapped.handler event state) of
        Continue state => pure $ Continue state
        Yield result   => pure $ Yield $ do
          result <- result
          pure $ f <$> result
        Push top merge => push top merge

||| This is like above `map`, but takes a partial function.
|||
||| This is useful when you want to do further processing or
||| validation on the yield value.
|||
||| Note: if the wrapped component yields, but `f` returns Nothing,
||| the response is equivalent to `ignore`, rather than `exit`. The
||| assumption is that the component has failed validation, and so the
||| component should remain in place.
|||
||| XXX: does this correspond to a prelude interface?
export
mapMaybe : (a -> Maybe b) -> Component e a -> Component e b
mapMaybe f wrapped = component @{wrapped.vimpl} wrapped.state handle get
  where
    get : wrapped.State -> Maybe b
    get self = join $ f <$> wrapped.get self

    handle : Component.Handler wrapped.State b e
    handle event state = case !(wrapped.handler event state) of
      Continue state => pure $ Continue state
      Yield result   => do
        result <- result
        case f ?hole of
          Nothing => pure $ Continue $ pure wrapped.state
          v  => pure $ Yield $ pure v
      Push top merge => push top merge

||| Cute alias for `mapMaybe' above.
export
(<$?>) : (a -> Maybe b) -> Component e a -> Component e b
(<$?>) f c = mapMaybe f c

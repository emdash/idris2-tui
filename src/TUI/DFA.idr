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

||| This module is intended to explore the overlap between user
||| interfaces and automata theory. DFAs in this module are designed
||| to translate between different event types.
|||
||| - input modes
||| - command lines
||| - tool and menu bars
||| - structural editing
|||
||| In contrast with traditional lexing and parsing, the emphasis is
||| on interactive use. There's no need to track source locations, but
||| there is a need to provide user feedback.
module TUI.DFA


import Data.SnocList


%default total


||| The output of a DFAs transition function.
|||
||| @Discard Accept the current token, but otherwise do nothing.
||| @Advance Transition to the next state, emitting the given action.
||| @Accept  Transition to the final state, possibly emitting a final action.
||| @Reject
public export
data Transition stateT outputT
  = Discard
  | Advance stateT (Maybe outputT)
  | Accept  (Maybe outputT)
  | Reject  String -- XXX: generalize error type later later

||| The type of a DFAs transition function
public export
0 TransitionFn : Type -> Type -> Type -> Type
TransitionFn stateT inputT outputT = inputT -> stateT -> Transition stateT outputT

||| An abstract DFA.
|||
||| This type hides the concrete state type, enabling an API of
||| composable DFAs.
export
record Automaton inputT outputT where
  constructor MkAutomaton
  0 State    : Type
  state      : State
  start      : State
  transition : TransitionFn State inputT outputT

||| Compute the next state for an abstract DFA.
|||
||| This API enables composing aribtrary DFAs.
export
next : TransitionFn (Automaton inputT outputT) inputT outputT
next input self = case self.transition input self.state of
  Discard               => Discard
  Advance state output  => Advance ({state := state} self) output
  Accept  output        => Accept output
  Reject err            => Reject err

export
run : Automaton inputT outputT -> List inputT -> Either String (List outputT)
run self [] = Right []
run self (x :: xs) with (next x self)
  _ | Discard                = run self xs
  _ | Advance next' Nothing  = run next' xs
  _ | Advance next' (Just o) = Right $ o :: !(run next' xs)
  _ | Accept        Nothing  = Right $ []
  _ | Accept        (Just o) = Right $ [o]
  _ | Reject        err      = Left err

||| Construct a new DFA from an initial state and a transition function.
export
automaton
  :  {0 stateT, inputT, outputT : Type}
  -> (start : stateT)
  -> (transition : TransitionFn stateT inputT outputT)
  -> Automaton inputT outputT
automaton start transition = MkAutomaton {
  State = stateT,
  state = start,
  start = start,
  transition = transition
}

||| Reset a DFA to its initial state.
export
reset : Automaton inputT outputT -> Automaton inputT outputT
reset self = {state := self.start} self

||| Construct an automaton that always accepts.
export
accepting : (Maybe outputT) -> Automaton _ outputT
accepting output = automaton () f
  where f : TransitionFn () _ outputT
        f _ self = Accept output

||| Construct an automaton that always rejects.
export
rejecting : String -> Automaton _ _
rejecting error = automaton () $ f
  where f : TransitionFn () _ _
        f _ self = Reject error

||| Lift a pure function from (inputT -> Maybe outputT) to an Automaton.
export
liftF : (inputT -> Maybe outputT) -> Automaton inputT outputT
liftF mapping = automaton () $ f
  where f : TransitionFn () inputT outputT
        f input self = Advance () (mapping input)

||| Lift a single value to an Automaton.
|||
||| The machine will emit the same output token regardless of its
||| input.
export
repeat : Maybe outputT -> Automaton _ outputT
repeat output = liftF (const output)

||| A blanket rejecting Automaton
export
done : Automaton _ _
done = rejecting "Expected: End of Input"

||| Accept expected input (once), reject everything else.
export
expect
  :  Show inputT
  => Eq inputT
  => inputT
  -> Maybe outputT
  -> Automaton inputT outputT
expect expected output = automaton True handle
where
  handle : TransitionFn Bool inputT outputT
  handle _     False = Reject "Expected: End of Input"
  handle input True = case input == expected of
    True  => Accept output
    False => Reject "Expected: \{show input}"

||| Compose two automata by chaining the output.
|||
||| XXX: make sure this logic is sensible.
export
(.) : Automaton b c -> Automaton a b -> Automaton a c
(.) snd fst = automaton (fst, snd) chain
  where
    chain : TransitionFn (Automaton a b, Automaton b c) a c
    chain input self = case next input (Builtin.fst self) of
      Discard               => Discard
      Advance fst Nothing   => Advance (fst, Builtin.snd self) Nothing
      Advance fst (Just o)  => case next o (Builtin.snd self) of
        Discard     => Advance (fst, Builtin.snd self) Nothing
        Advance x y => Advance (fst, x) y
        Accept x    => Accept x
        Reject str  => Reject str
      Accept Nothing => Accept Nothing
      Accept (Just o) => case next o (Builtin.snd self) of
        Discard     => Accept  Nothing
        Advance x y => Advance (done, x) y
        Accept x    => Accept x
        Reject err  => Reject err
      Reject err    => Reject err

||| Sequence multiple automata.
export
seq : List (Automaton i o) -> Automaton i o
seq automata = automaton automata sequence
  where
    sequence : TransitionFn (List (Automaton i o)) i o
    sequence input [] = Reject "Expected: End of Input"
    sequence input (x :: xs) = case next input x of
      Discard => Discard
      Advance x y => Advance (x :: xs) y
      Accept x => Advance xs x
      Reject str => Reject str

||| Restart an automata when it accepts.
export
loop : Automaton i o -> Automaton i o
loop wrapped = automaton wrapped handle
  where
    handle : TransitionFn (Automaton i o) i o
    handle input self = case next input self of
      Discard     => Discard
      Advance x y => Advance x y
      Accept x    => Advance (reset self) x
      Reject err  => Reject err

||| Restart an automata when it rejects.
|||
||| This, unfortunately, drops the error value.
export
retry : Automaton i o -> Automaton i o
retry wrapped = automaton wrapped handle
  where
    handle : TransitionFn (Automaton i o) i o
    handle input self = case next input self of
      Discard     => Discard
      Advance x y => Advance x y
      Accept x    => Accept x
      Reject err  => Advance (reset self) Nothing

||| A DFA which simply returns its input unaltered.
export
identity : Automaton i i
identity = liftF (Just . id)


||| Modify the behavior of Automata with boolean predicates.
namespace Predicated
  ||| Pair an automaton with a predicate over the input.
  record Predicated inputT outputT where
    constructor P
    predicate : inputT -> Bool
    wrapped : Automaton inputT outputT

  ||| Run the given automaton until the predicate returns true.
  export
  until
    : (inputT -> Bool)
    -> Automaton inputT outputT
    -> Automaton inputT outputT
  until predicate wrapped = automaton (P predicate wrapped) handle
    where
      handle : TransitionFn (Predicated inputT outputT) inputT outputT
      handle input self = case (predicate input, next input self.wrapped) of
        (False, Discard)       => Discard
        (False, (Advance x y)) => Advance ({wrapped := x} self) y
        (False, (Accept x))    => Accept x
        (False, (Reject err))  => Reject err
        (True,  Discard)       => Accept Nothing
        (True,  (Advance x y)) => Accept y
        (True,  (Accept x))    => Accept x
        (True,  (Reject err))  => Reject err

  ||| Run the given automata while the predicate returns false.
  export
  while : (inputT -> Bool) -> Automaton inputT outputT -> Automaton inputT outputT
  while predicate wrapped = until (not . predicate) wrapped

  ||| Ignore input tokens for which the predicate returns True.
  export
  filter : (inputT -> Bool) -> Automaton inputT outputT -> Automaton inputT outputT
  filter predicate wrapped = automaton (P predicate wrapped) handle
    where
      handle : TransitionFn (Predicated inputT outputT) inputT outputT
      handle input self = case predicate input of
        True => Discard
        False => case next input self.wrapped of
          Discard     => Discard
          Advance x y => Advance ({wrapped := x} self) y
          Accept  x   => Accept x
          Reject err  => Reject err

  ||| Ignore input tokens for which the predicate returns False.
  export
  keep : (inputT -> Bool) -> Automaton inputT outputT -> Automaton inputT outputT
  keep predicate wrapped = filter (not . predicate) wrapped


||| Automata which rely on buffering of tokens.
namespace Buffered
  ||| Pairs an automaton with a buffer.
  export
  record Buffered inputT outputT where
    constructor B
    buffer : SnocList outputT
    wrapped : Automaton inputT outputT

  ||| Wraps an automaton, buffering its output until it accepts or rejects.
  |||
  ||| If the wrapped automaton accepts, then the buffer is sent
  ||| downstream as output. If the wrapped automaton rejects, the
  ||| error is passed unaltered.
  export
  buffered : Automaton inputT outputT -> Automaton inputT (List outputT)
  buffered wrapped = automaton (B [<] wrapped) handle
    where
      handle : TransitionFn (Buffered inputT outputT) inputT (List outputT)
      handle input self = case next input self.wrapped of
        Discard            => Discard
        Advance x Nothing  => Advance ({wrapped := x} self) Nothing
        Advance x (Just o) => Advance ({wrapped := x, buffer $= (:< o)} self) Nothing
        Accept Nothing     => Accept $ Just $ toList self.buffer
        Accept (Just x)    => Accept $ Just $ toList $ self.buffer :< x
        Reject err         => Reject err

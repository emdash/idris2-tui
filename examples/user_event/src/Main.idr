module Main


import Derive.Prelude
import TUI
import TUI.MainLoop
import TUI.MainLoop.Async
import IO.Async
import IO.Async.Loop.Poller
import IO.Async.Loop.Posix
import JSON.Derive


%default total
%language ElabReflection


||| This is the user-defined event type.
|||
||| To satisfy the requirements of `InputShim`, it must implement
||| `FromJSON`.
data Counter
  = Inc
  | Reset
%runElab derive "Counter" [FromJSON]

||| A counter event source.
counter : Has Counter evts => Nat -> EventSource evts
counter n = On $ go n
where
  go : Nat -> Channel (HSum evts) -> Async Poll errs ()
  go 0 chan = close chan
  go n@(S k) chan = do
    Sent <- send chan $ inject Inc | _ => pure ()
    sleep 1.s
    go k chan


||| The demo state consists of a cursor position and a count.
|||
||| The cursor position is updated via the keyboard, as usual. The
||| count is updated via the user timer event defined above.
record UserEventDemo where
  constructor MkUser
  pos : Pos
  count : Nat
%runElab derive "UserEventDemo" [Show]

||| We implement view for this type as per usual.
|||
||| Basically, we show the count at the current cursor position, along
||| with some help text.
View UserEventDemo where
  size _ = MkArea 1 1
  paint state window self = do
    sgr [SetReversed True]
    showTextAt self.pos $ show self.count
    sgr [Reset]
    window <- packBottom Normal window legend3
    window <- packBottom Normal window legend2
    ignore $  packBottom Normal window legend1
  where
    legend1 : String
    legend1 = "Arrow Keys to Move Cursor."

    legend2 : String
    legend2 = "<Enter> to accept values."

    legend3 : String
    legend3 = "<Esc> to cancel."

||| This shows how to create a component which responds to a
||| user-defined event.
|||
||| Here, `HSum [Counter, Key]` is the event type.
|||
||| `union [onCounter, onKey]` composes two distinct event
||| handlers.
|||
||| When you need to compose event handlers with `Union`, specify the
||| `User.Handler` type instead of `Component.Handler`.
userEventDemo : Pos -> Component (HSum [Counter, Key]) UserEventDemo
userEventDemo pos = component {
  state   = (MkUser pos 0),
  handler = union [onCounter, onKey],
  get     = Just . id
} where
  ||| Handle counter events.
  onCounter : Single.Handler UserEventDemo UserEventDemo Counter
  onCounter Inc   self = update $ {count $= S} self
  onCounter Reset self = update $ {count $= S} self

  ||| Handle key presses.
  onKey : Single.Handler UserEventDemo UserEventDemo Key
  onKey Up     self = update $ { pos := self.pos.shiftUp    1} self
  onKey Down   self = update $ { pos := self.pos.shiftDown  1} self
  onKey Left   self = update $ { pos := self.pos.shiftLeft  1} self
  onKey Right  self = update $ { pos := self.pos.shiftRight 1} self
  onKey Enter  self = yield self
  onKey Escape self = exit
  onKey _      self = ignore

partial export
main : IO ()
main = do
  window   <- screen
  let mainLoop : AsyncMain [Counter, Key] = asyncMain [(counter 10)]
  case !(runComponent mainLoop $ userEventDemo window.center) of
    Nothing => putStrLn "User Canceled"
    Just choice => putStrLn $ "User selected: \{show choice}"

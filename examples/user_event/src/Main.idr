module Main


import Derive.Prelude
import TUI
import TUI.MainLoop
import TUI.MainLoop.Async
import IO.Async
import IO.Async.Signal
import IO.Async.Loop.Poller
import IO.Async.Loop.Posix
import IO.Async.Loop.Epoll
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

||| A user-defined event source.
|||
||| It sends a sequence of `n` `Inc` events, then a `Reset` event,
||| then repeats.
covering
counter : Has Counter evts => Nat -> EventSource evts
counter n = go n
where
  go : Nat -> EventSource evts
  go 0 post = do
    post $ inject Main.Reset
    go n post
  go n@(S k) post = do
    post $ inject Inc
    sleep 1.s
    go k post

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
    showTextAt window.nw $ show window.size
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
||| When you need to compose event handlers with `Union`, specify
||| `Single.Handler` type instead of `Component.Handler`.
userEventDemo : Pos -> Component (HSum [Counter, Key]) UserEventDemo
userEventDemo pos = component {
  state   = (MkUser pos 0),
  handler = union [onCounter, onKey],
  get     = Just . id
} where
  ||| Handle counter events.
  onCounter : Single.Handler UserEventDemo UserEventDemo Counter
  onCounter Inc   self = update $ {count $= S} self
  onCounter Reset self = update $ {count := 0} self

  ||| Handle key presses.
  onKey : Single.Handler UserEventDemo UserEventDemo Key
  onKey Up     self = update $ { pos := self.pos.shiftUp    1} self
  onKey Down   self = update $ { pos := self.pos.shiftDown  1} self
  onKey Left   self = update $ { pos := self.pos.shiftLeft  1} self
  onKey Right  self = update $ { pos := self.pos.shiftRight 1} self
  onKey Enter  self = yield self
  onKey Escape self = exit
  onKey _      self = ignore

||| Main entry point
partial export
main : IO ()
main = do
  -- construct an async mainloop, specfying the additional counter event source.
  let mainLoop := asyncMain {evts = [Counter, Key]} [(counter 10)]
  -- create the application state, and run the component.
  case !(runComponent mainLoop $ userEventDemo (!screen).center) of
    Nothing => putStrLn "User Canceled"
    Just choice => putStrLn $ "User selected: \{show choice}"

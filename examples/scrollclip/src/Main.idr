module Main


import TUI
import TUI.Component.Box
import TUI.MainLoop
import TUI.MainLoop.Default
import Data.List


%default total


items : String -> VList String
items prefx = fromList "Items" $ item <$> [0..20]
  where
    item : Nat -> String
    item i = "\{prefx}: \{show i}"

record ViewPort a where
  constructor MkViewPort
  size     : Area
  contents : a
  offset   : (Integer, Integer)

viewport : Area -> a -> (Integer, Integer) -> ViewPort a
viewport = MkViewPort

View a => View (ViewPort a) where
  size self = self.size
  paint state window self = do
    clip window $ do
      -- now paint the 
      paint state (offset window self.offset) self.contents
    -- debug render offset in bottom left screen corner.
    showTextAt (MkPos 0 81) $ show window
  where
    offset : Rect -> (Integer, Integer) -> Rect
    offset self (x, y) = (self.shiftX x).shiftY y

[mine] View (Integer, Integer) where
  size = const $ MkArea 0 0
  paint state window self = do
    let state = demoteFocused state
    window <- packTop    state window $ box (MkArea 0 4) ' '
    window <- packTop    state window $ HRule
    window <- packBottom state window $ box (MkArea 0 2) ' '
    window <- packBottom state window $ HRule
    window <- packLeft   state window $ box (MkArea 5 4) ' '
    window <- packLeft   state window $ VRule
    window <- packLeft   state window $ viewport (MkArea 5 0) (Main.items "Left") $ (0, fst self)
    window <- packLeft   state window $ VRule
    paint state window $ viewport (MkArea 5 0) (Main.items "Right") $ (0, snd self)
    showTextAt origin $ show self

main : IO ()
main = do
  _ <- runView @{mine} !getDefault onKey (0, 0)
  pure ()
where
  onKey : Event.Handler (Integer, Integer) () Key
  onKey Up   (x, y) = update $ (x, y - 1)
  onKey Down (x, y) = update $ (x, y + 1)
  onKey Left (x, y) = update $ (x - 1, y)
  onKey Right(x, y) = update $ (x + 1, y)
  onKey _ _ = exit

module TUI.Prim


import System.FFI


%default total


||| Binds to the getWinSize function in `support/tui.c`.
export
%foreign "C:getWinSize,tui-idris"
prim__getWinSize : PrimIO Bits32

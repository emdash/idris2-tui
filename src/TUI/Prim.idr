module TUI.Prim


import System.FFI


%default total

export
%foreign "C:getWinSize,tui-idris"
prim__getWinSize : PrimIO Bits32



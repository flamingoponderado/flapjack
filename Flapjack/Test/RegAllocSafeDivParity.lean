import Flapjack.RiscV.CakeRegAlloc

/-! Same-input kernel replay of fourteen fresh original safe_div equations. -/
namespace Flapjack.Test.RegAllocSafeDivParity
open Flapjack Flapjack.RiscV.CakeRegAlloc

example : [0,0,0,0,7,0,1,1,6,6,75557863725914323419137,1,0,4294967295] =
    [RegAlloc.safeDiv 0 0, RegAlloc.safeDiv 1 0, RegAlloc.safeDiv 1208925819614629174706176 0, RegAlloc.safeDiv 0 7, RegAlloc.safeDiv 7 1, RegAlloc.safeDiv 6 7, RegAlloc.safeDiv 7 7, RegAlloc.safeDiv 8 7, RegAlloc.safeDiv 20 3, RegAlloc.safeDiv 18 3, RegAlloc.safeDiv 1208925819614629174706193 16, RegAlloc.safeDiv 1208925819614629174706193 1208925819614629174706176, RegAlloc.safeDiv 1208925819614629174706176 1267650600228229401496703205376, RegAlloc.safeDiv 18446744073709551615 4294967296] := by
  decide +kernel

-- This is a Flapjack-only executable wrapper, not a second HOL port.
example (x v : Nat) : cakeSafeDiv x v = RegAlloc.safeDiv x v := rfl

example (x v : Nat) : cakeSafeDiv x v = (if v = 0 then 0 else x / v) := rfl

end Flapjack.Test.RegAllocSafeDivParity

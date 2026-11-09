module

public import Flapjack.Pancake.PanSimp
public import Flapjack.Pancake.PanLang.ProgHOLInduction

@[expose] public section

/-!
Flapjack-specific representation bridges for the exact HOL `pan_simp` pass.

These results connect the `ProgHOL` ports to the production `Prog` helpers.
They are not HOL declarations themselves and therefore carry no `@[hol]`
tag.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- `toStringOfBytes` is injective because `ofString` is its left inverse.
This local statement avoids an import of the downstream PanGlobals module. -/
theorem panSimpToStringOfBytes_injective : Function.Injective toStringOfBytes := by
  intro left right heq
  have := congrArg ofString heq
  simpa [ofString_toStringOfBytes] using this

@[simp] theorem panSimpToStringOfBytes_eq_iff (left right : MlS) :
    toStringOfBytes left = toStringOfBytes right ↔ left = right := by
  constructor
  · exact fun h => panSimpToStringOfBytes_injective h
  · intro h
    cases h
    rfl

end Flapjack

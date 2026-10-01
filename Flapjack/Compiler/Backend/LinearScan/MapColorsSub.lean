import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.HiddenState
import Flapjack.Compiler.Backend.RegAlloc.StateMap

/-!
# linear_scan translation helper `map_colors_sub`

Ports of `linear_scanScript.sml:1264-1274`, the monadic map of `colors_sub`
defined for the CakeML translator and its equation with the tagged
`st_ex_MAP` (`stExMap`). Proof-side; the executed allocator is unchanged.
-/

namespace Flapjack.LinearScan

open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-- Exact HOL `map_colors_sub` (`linear_scanScript.sml:1264-1268`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "map_colors_sub_def"]
def mapColorsSub : List Nat → LsM (List Nat)
  | [] => ret []
  | x :: xs => bind (colorsSub x) fun fx => bind (mapColorsSub xs) fun fxs => ret (fx :: fxs)

/-- Exact HOL `map_colors_sub_eq` (`linear_scanScript.sml:1270-1274`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "map_colors_sub_eq"]
theorem mapColorsSubEq : mapColorsSub = stExMap colorsSub := by
  funext l
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [mapColorsSub, stExMap, ih]

end Flapjack.LinearScan

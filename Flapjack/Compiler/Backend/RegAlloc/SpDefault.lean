import Flapjack.Compiler.Backend.RegAlloc
import Flapjack.Misc.Sptree

/-!
# reg_alloc `sp_default`

Counterpart of `reg_allocScript.sml:1219-1222` `sp_default_def`.
-/

namespace Flapjack

/-- Exact HOL `sp_default_def` (`reg_allocScript.sml:1219-1222`): the colour
stored for `i`, or `i DIV 2` for a missing physical register and `0` otherwise. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "sp_default_def"]
def spDefault (t : Spt Nat) (i : Nat) : Nat :=
  match sptLookup i t with
  | none => if isPhyVar i then i / 2 else 0
  | some x => x

end Flapjack

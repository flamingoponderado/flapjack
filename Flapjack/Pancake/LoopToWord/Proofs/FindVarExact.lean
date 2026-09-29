import Flapjack.HolRef
import Flapjack.Misc.Sptree
import Flapjack.Pancake.LoopToWord

/-!
# Exact `find_var_neq_0_ctxt` proof port

The HOL context is an `sptree` `num_map`, rendered constructor-for-constructor
by `Spt Nat`. HOL's `domain` membership is `sptMem`, and `find_var` is the
tagged `findVarHOL` definition. HOL `EVEN m` is represented by `m % 2 = 0`,
as in the exact `sptLookup` equations.
-/

open Flapjack.LoopToWord

namespace Flapjack

/-- Exact HOL `find_var_neq_0_ctxt` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:178-184`. The quantified
lookup condition, domain premise, and conclusion are unchanged. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "find_var_neq_0_ctxt"]
theorem findVarNeZeroContextHOLExact (ctxt : Spt Nat) (v : Nat)
    (hcontext : ∀ n m, sptLookup n ctxt = some m → m ≠ 0 ∧ m % 2 = 0)
    (hdomain : sptMem v ctxt) : findVarHOL ctxt v ≠ 0 := by
  obtain ⟨m, hm⟩ := (sptMem_iff_lookup v ctxt).mp hdomain
  change (sptLookup v ctxt).getD 0 ≠ 0
  rw [hm]
  exact (hcontext v m hm).1

end Flapjack

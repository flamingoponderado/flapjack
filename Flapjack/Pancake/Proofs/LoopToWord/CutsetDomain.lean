import Flapjack.Pancake.Proofs.LoopToWord.LocalsRel

/-!
# Loop-to-word cutset domain fact

Exact support theorem from `loop_to_wordProofScript.sml`. The source `domain`
is represented by `sptDomain` on the exact Spt carrier, and `mkNewCutsetHOL`
retains register zero by construction.
-/

namespace Flapjack.LoopToWord

/-- Exact HOL `domain_mk_new_cutset_not_empty`: every generated cutset
contains register zero, so its domain is nonempty. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml"
  "domain_mk_new_cutset_not_empty"]
theorem domainMkNewCutsetNotEmpty (context : Spt Nat) (live : Spt Unit) :
    sptDomain (mkNewCutsetHOL context live) ≠ (fun _ => False) := by
  intro hempty
  have hzero : sptDomain (mkNewCutsetHOL context live) 0 := by
    change (sptLookup 0 (mkNewCutsetHOL context live)).isSome
    rw [mkNewCutsetHOL, sptLookup_sptInsert_zero]
    simp
  simp [hempty] at hzero

end Flapjack.LoopToWord

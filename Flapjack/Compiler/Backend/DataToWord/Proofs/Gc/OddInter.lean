module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.InterInsert
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AdjustedSet
public import Flapjack.Misc.SptreeLookup

@[expose] public section

/-! Intersections with adjusted source names ignore odd-key updates. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Inserting an odd key leaves the intersection with adjusted names unchanged. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "inter_insert_ODD_adjust_set_alt"]
theorem inter_insertOdd_adjustSet {α β : Type} (k : Nat) (v : α) (s : Spt α) (t : Spt β)
    (odd : k % 2 = 1) :
    sptInter (sptInsert k v s) (adjustSet t) = sptInter s (adjustSet t) := by
  rw [inter_insert]
  have absent := lookup_odd_adjustSet k t odd
  simp [sptDomain, absent]

/-- Deleting an odd key also leaves the adjusted-name intersection unchanged. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "inter_delete_ODD_adjust_set_alt"]
theorem inter_deleteOdd_adjustSet {α β : Type} (k : Nat) (s : Spt α) (t : Spt β)
    (odd : k % 2 = 1) :
    sptInter (sptDelete k s) (adjustSet t) = sptInter s (adjustSet t) := by
  apply (sptEqThm _ _ ⟨sptWfInter _ _, sptWfInter _ _⟩).2
  intro q
  rw [sptLookup_sptInterCases, sptLookup_sptInterCases, sptLookup_sptDelete]
  by_cases h : q = k
  · subst q
    simp [lookup_odd_adjustSet k t odd]
  · simp [h]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

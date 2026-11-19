module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.InterInsert
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AdjustedSet

@[expose] public section

/-! Intersections with adjusted source names ignore odd insertions. -/
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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

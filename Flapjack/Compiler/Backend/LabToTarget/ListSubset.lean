import Flapjack.Misc.ListSubset

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Misc

/-- Original arbitrary-element prefix-subset law. The standard decidable
 equality instance represents HOL equality; no custom comparison is assumed. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "list_subset_TAKE"]
theorem listSubsetTake {α : Type} [DecidableEq α] (i : Nat) (xs : List α) :
    listSubset (xs.take i) xs = true := by
  simp only [listSubset, List.all_eq_true, decide_eq_true_eq]
  intro x hx
  exact List.mem_of_mem_take hx

/-- Original transitivity over arbitrary lists, with both source premises. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "list_subset_trans"]
theorem listSubsetTrans {α : Type} [DecidableEq α] (a b c : List α) :
    listSubset a b = true ∧ listSubset b c = true → listSubset a c = true := by
  simp only [listSubset, List.all_eq_true, decide_eq_true_eq]
  rintro ⟨hab, hbc⟩ x hx
  exact hbc x (hab x hx)

end Flapjack.Compiler.Backend.LabToTarget

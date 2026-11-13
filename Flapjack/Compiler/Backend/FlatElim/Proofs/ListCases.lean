module

public import Flapjack.Misc.ListEl

@[expose] public section

/-! List-index equation used by the flat elimination proof. -/
namespace Flapjack.Compiler.Backend.FlatElim

/-- An in-bounds element satisfies every predicate that holds on its list. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "EVERY_EL_IMP"]
theorem every_el_imp {α : Type} (P : α → Bool) (xs : List α) (n : Nat)
    (premises : xs.all P = true ∧ n < xs.length) :
    P (@holEl α ⟨xs[n]'premises.2⟩ n xs) = true := by
  rw [@holEl_eq_getElem α ⟨xs[n]'premises.2⟩ n xs premises.2]
  exact (List.all_eq_true.mp premises.1) _ (List.getElem_mem premises.2)

@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "EL_REP_NONE_SOME_trivia"]
theorem el_replicateNone_some {α : Type} (n : Nat) (xs : List (Option α)) (i : Nat) (y : α)
    (bound : n < xs.length + i) :
    holEl n (xs ++ List.replicate i none) = some y ↔
      n < xs.length ∧ holEl n xs = some y := by
  have boundAppend : n < (xs ++ List.replicate i none).length := by simpa using bound
  rw [holEl_eq_getElem n _ boundAppend]
  by_cases inside : n < xs.length
  · rw [holEl_eq_getElem n xs inside]
    simp [inside]
  · simp [List.getElem_append, inside]

end Flapjack.Compiler.Backend.FlatElim

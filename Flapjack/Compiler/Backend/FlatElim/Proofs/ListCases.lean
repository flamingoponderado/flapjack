import Flapjack.Misc.ListEl

/-! List-index equation used by the flat elimination proof. -/
namespace Flapjack.Compiler.Backend.FlatElim

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

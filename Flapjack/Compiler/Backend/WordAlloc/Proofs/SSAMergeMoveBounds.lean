import Flapjack.Compiler.Backend.WordAlloc.SSAMergeMoves
import Lean.Elab.Tactic.Omega

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Fresh destinations lie between the original and resulting counter. This
infrastructure proof keeps arbitrary trees, repeated keys and arbitrary natural
counters. List membership over MAP FST renders both original EVERY clauses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "merge_moves_fst"]
theorem mergeMovesFst (names : List Nat) (next : Nat) (leftMap rightMap : Spt Nat) :
    let result := mergeMoves names leftMap rightMap next
    next ≤ result.2.2.1 ∧
    (∀ dest ∈ result.1.map Prod.fst, dest < result.2.2.1 ∧ dest ≥ next) ∧
    (∀ dest ∈ result.2.1.map Prod.fst, dest < result.2.2.1 ∧ dest ≥ next) := by
  induction names with
  | nil => simp [mergeMoves]
  | cons name names ih =>
    generalize h : mergeMoves names leftMap rightMap next = result at ih ⊢
    rcases result with ⟨leftMoves, rightMoves, counter, leftTree, rightTree⟩
    simp only at ih
    rcases ih with ⟨bound, leftBound, rightBound⟩
    simp only [mergeMoves, h]
    cases leftLookup : sptLookup name leftTree with
    | none => exact ⟨bound, leftBound, rightBound⟩
    | some leftValue =>
      cases rightLookup : sptLookup name rightTree with
      | none => exact ⟨bound, leftBound, rightBound⟩
      | some rightValue =>
        simp only
        split
        · exact ⟨bound, leftBound, rightBound⟩
        · simp only
          refine ⟨by omega, ?_, ?_⟩
          · intro dest member
            simp only [List.map_cons, List.mem_cons] at member
            rcases member with rfl | member
            · omega
            · have hb := leftBound dest member
              omega
          · intro dest member
            simp only [List.map_cons, List.mem_cons] at member
            rcases member with rfl | member
            · omega
            · have hb := rightBound dest member
              omega

end Flapjack.Compiler.Backend.WordAlloc

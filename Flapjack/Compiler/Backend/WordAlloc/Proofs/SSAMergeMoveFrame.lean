import Flapjack.Compiler.Backend.WordAlloc.SSAMergeMoves
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapExtend
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARegisterClass

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full native allocation and map frame: arbitrary lists, counters and Spt maps,
with exactly the original allocation-class premise and four result conjuncts. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "merge_moves_frame"]
theorem mergeMovesFrame (names : List Nat) (next : Nat) (leftMap rightMap : Spt Nat)
    (allocated : isAllocVar next) :
    let result := mergeMoves names leftMap rightMap next
    isAllocVar result.2.2.1 ∧ next ≤ result.2.2.1 ∧
      (ssaMapOK next leftMap → ssaMapOK result.2.2.1 result.2.2.2.1) ∧
      (ssaMapOK next rightMap → ssaMapOK result.2.2.1 result.2.2.2.2) := by
  induction names with
  | nil => simp [mergeMoves, allocated]
  | cons name names ih =>
    generalize h : mergeMoves names leftMap rightMap next = result at ih ⊢
    rcases result with ⟨leftMoves, rightMoves, counter, leftTree, rightTree⟩
    simp only at ih
    rcases ih with ⟨counterAllocated, bound, leftOK, rightOK⟩
    simp only [mergeMoves, h]
    cases leftLookup : sptLookup name leftTree with
    | none => exact ⟨counterAllocated, bound, leftOK, rightOK⟩
    | some leftValue =>
      cases rightLookup : sptLookup name rightTree with
      | none => exact ⟨counterAllocated, bound, leftOK, rightOK⟩
      | some rightValue =>
        simp only
        split
        · exact ⟨counterAllocated, bound, leftOK, rightOK⟩
        · simp only
          have nonphysical : ¬ isPhyVar counter := by
            simp only [isAllocVar, decide_eq_true_eq] at counterAllocated
            simp only [isPhyVar, decide_eq_true_eq]
            omega
          exact ⟨isAllocVarAdd counter counterAllocated, by omega,
            fun source => ssaMapOKExtend counter leftTree name ⟨leftOK source, nonphysical⟩,
            fun source => ssaMapOKExtend counter rightTree name ⟨rightOK source, nonphysical⟩⟩

end Flapjack.Compiler.Backend.WordAlloc

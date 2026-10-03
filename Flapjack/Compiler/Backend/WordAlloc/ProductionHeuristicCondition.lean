import Flapjack.Compiler.Backend.WordAlloc.ProductionHeuristicCountMap

namespace Flapjack.WordAlloc
open RiscV

/-! Actual conditional reads use the opposite update order from the original
getHeu If clause. These untagged implementation lemmas derive correspondence
for distinct and aliased registers without changing the executable path. -/

private def incrementRead (value : HeuData) : HeuData :=
  (value.1, value.2.1, value.2.2.1, value.2.2.2.1 + 1, value.2.2.2.2)

private theorem readLookup (name key : Nat) (tree : Spt HeuData) :
    sptLookup key (add1RhsReg name tree) =
      if key = name then some (incrementRead ((sptLookup name tree).getD (0,0,0,0,0)))
      else sptLookup key tree := by
  by_cases same : key = name
  · subst key
    cases found : sptLookup name tree <;>
      simp [add1RhsReg, found, incrementRead, sptLookup_sptInsert_same]
  · cases found : sptLookup name tree <;>
      simp [add1RhsReg, found, same,
        sptLookup_sptInsert_ne name key _ _ same]

theorem heuristicCondition_reads_commute (counts : WordHeuristicCountMap) (left right : Nat) :
    heuristicCountMapToNative ((counts.addRhsReg left).addRhsReg right) =
      heuristicCountMapToNative ((counts.addRhsReg right).addRhsReg left) := by
  apply (sptEqThm _ _ ⟨heuristicCountMap_wf _, heuristicCountMap_wf _⟩).mpr
  intro key
  simp only [heuristicCountMap_addRhsReg, readLookup]
  by_cases same : left = right
  · subst right; rfl
  · by_cases kl : key = left <;> by_cases kr : key = right <;>
      simp_all [eq_comm]

theorem heuristicCondition_reads (counts : WordHeuristicCountMap) (condition : Nat)
    (right : WordRegImm α) :
    heuristicCountMapToNative (match right with
      | .reg source => (counts.addRhsReg condition).addRhsReg source
      | .imm _ => counts.addRhsReg condition) =
      (match right with
      | .reg source => add1RhsReg condition
          (add1RhsReg source (heuristicCountMapToNative counts))
      | .imm _ => add1RhsReg condition (heuristicCountMapToNative counts)) := by
  cases right with
  | imm value => exact heuristicCountMap_addRhsReg counts condition
  | reg source =>
      rw [heuristicCondition_reads_commute, heuristicCountMap_addRhsReg,
        heuristicCountMap_addRhsReg]

end Flapjack.WordAlloc

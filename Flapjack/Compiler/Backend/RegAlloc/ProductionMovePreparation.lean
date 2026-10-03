import Flapjack.Compiler.Backend.RegAlloc.ProductionMoveAdmission
import Flapjack.Compiler.Backend.RegAlloc.ProductionInitDomain

namespace Flapjack.RegAlloc
open RiscV RiscV.CakeRegAlloc

/-! Actual/native wrapper infrastructure without independent HOL originals.
Source names, not successful allocator outputs, determine the move domain. -/

theorem allocatorDecoder_production (tree : WordClashTree) (name : Nat) :
    cakeAllocatorIndexLookup (cakeAllocatorIndex (cakeMkBij tree).toAllocator) name =
      Flapjack.spDefault (mkBij (productionClashTreeToNative tree)).1 name := by
  rw [mkBij_production]
  exact tagDecoder_production _ _

theorem allocatorMoves_production (tree : WordClashTree)
    (moves : List (Nat × (Nat × Nat))) :
    moves.map (cakeUpdateMove
      (cakeAllocatorIndexLookup (cakeAllocatorIndex (cakeMkBij tree).toAllocator))) =
    moves.map (updateMove (Flapjack.spDefault (mkBij (productionClashTreeToNative tree)).1)) := by
  apply List.map_congr_left
  intro move _
  rcases move with ⟨priority, left, right⟩
  simp only [cakeUpdateMove, updateMove, allocatorDecoder_production]

theorem allocatorMoves_bounds (tree : WordClashTree)
    (moves : List (Nat × (Nat × Nat)))
    (source : ∀ move ∈ moves,
      inClashTree (productionClashTreeToNative tree) move.2.1 ∧
      inClashTree (productionClashTreeToNative tree) move.2.2) :
    ∀ move ∈ moves.map (cakeUpdateMove
      (cakeAllocatorIndexLookup (cakeAllocatorIndex (cakeMkBij tree).toAllocator))),
      move.2.1 < (cakeMkBij tree).nextNode ∧ move.2.2 < (cakeMkBij tree).nextNode := by
  intro move member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  have left := producedAllocator_name_bound tree original.2.1 (source original originalMember).1
  have right := producedAllocator_name_bound tree original.2.2 (source original originalMember).2
  rcases original with ⟨priority, x, y⟩
  simp only [cakeUpdateMove]
  split
  · exact ⟨left, right⟩
  · exact ⟨right, left⟩

/-- Admission itself proves the endpoints are in the state dimension, even
when the unfiltered source move list is unrestricted. -/
theorem admittedMoves_bounds (state : CakeRaState) (limit : Nat)
    (moves : List (Nat × (Nat × Nat))) :
    ∀ move ∈ filterReversed (fun move => cakeFullConsistencyOk state limit move.2.1 move.2.2) moves,
      move.2.1 < state.dim ∧ move.2.2 < state.dim := by
  intro move member
  rw [filterReversed_production] at member
  have admitted := (List.mem_filter.mp (List.mem_reverse.mp member)).2
  simp only [cakeFullConsistencyOk, Bool.and_eq_true] at admitted
  exact ⟨of_decide_eq_true admitted.1.1.1.1.1.2,
    of_decide_eq_true admitted.1.1.1.1.2⟩

end Flapjack.RegAlloc

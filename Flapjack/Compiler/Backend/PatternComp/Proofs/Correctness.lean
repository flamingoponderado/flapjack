import Flapjack.Compiler.Backend.PatternExh.Proofs.Soundness

/-! Pattern compiler correctness over the proof-side matcher. The matcher and
finite-map carrier remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.PatternComp
open Flapjack PatternCommon PatternSemantics PatternExh

/-- Pattern compilation preserves every non-error row match. Its HOL
correspondence remains pending review of the underlying matcher and map. -/
theorem comp_correct (refs : HolFiniteMapExact Nat Term) (value : Term) (rows : List (Pat × Nat))
    (safe : matchRows refs rows value ≠ none) :
    dtEval refs value (comp rows) = matchRows refs rows value := by
  have movedEq := matchRows_moveConstUp refs value rows safe
  have movedSafe : matchRows refs (moveConstUp rows) value ≠ none := by rw [movedEq]; exact safe
  by_cases exhaustive : PatternExh.exhRows (moveConstUp rows) = true
  · obtain ⟨insertedSafe, insertedEq⟩ := matchRows_insertAny refs value (moveConstUp rows) movedSafe
    have codeEq := patsToCode_correct refs value (insertAny (moveConstUp rows)) insertedSafe
    have exhaustiveSound := exhRows_sound refs value (moveConstUp rows) movedSafe exhaustive
    simpa [comp, exhaustive, insertedEq exhaustiveSound, movedEq] using codeEq
  · have codeEq := patsToCode_correct refs value (moveConstUp rows) movedSafe
    simpa [comp, exhaustive, movedEq] using codeEq


end Flapjack.Compiler.Backend.PatternComp

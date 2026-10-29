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
  apply comp_correct_of_exhaustiveness refs value rows safe
  intro exhaustive
  apply exhRows_sound refs value (moveConstUp rows)
  · simpa [matchRows_moveConstUp refs value rows safe] using safe
  · exact exhaustive


end Flapjack.Compiler.Backend.PatternComp

import Flapjack.Compiler.Backend.PatternExh.Proofs.Soundness

/-! Pattern compiler correctness over the source-shaped matcher. -/
namespace Flapjack.Compiler.Backend.PatternComp
open Flapjack PatternCommon PatternSemantics PatternExh

private def toBroad (refs : HolFiniteMapExact Nat Term) : Nat → Option Term := refs.lookup

private def ofBroad (lookup : Nat → Option Term)
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat Term := ⟨lookup, support⟩

/-- The canonical finite-map parameter roundtrips through its lookup view. -/
theorem holFmapAsFiniteSupportParamWitness_comp_correct_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs := by
  cases refs
  exact ⟨rfl, rfl, rfl⟩

/-- Pattern compilation preserves every non-error row match. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_compScript.sml" "comp_thm"
  (fmap_as_finite_support_parameters := [refs])]
theorem comp_correct (refs : HolFiniteMapExact Nat Term) (value : Term) (rows : List (Pat × Nat))
    (safe : matchRows refs rows value ≠ none) :
    dtEval refs value (comp rows) = matchRows refs rows value := by
  have movedEq := matchRows_moveConstUp refs value rows safe
  have movedSafe : matchRows refs (moveConstUp rows) value ≠ none := by rw [movedEq]; exact safe
  by_cases exhaustive : PatternExh.exhRows (moveConstUp rows) = true
  · obtain ⟨insertedSafe, insertedEq⟩ := matchRows_insertAny refs value (moveConstUp rows) movedSafe
    have codeEq := patsToCode_correct refs value (insertAny (moveConstUp rows)) insertedSafe
    have exhaustiveSound := exhRows_sound refs (moveConstUp rows) value ⟨movedSafe, exhaustive⟩
    simpa [comp, exhaustive, insertedEq exhaustiveSound, movedEq] using codeEq
  · have codeEq := patsToCode_correct refs value (moveConstUp rows) movedSafe
    simpa [comp, exhaustive, movedEq] using codeEq


end Flapjack.Compiler.Backend.PatternComp

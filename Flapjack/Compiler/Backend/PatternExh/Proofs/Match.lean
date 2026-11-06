import Flapjack.Compiler.Backend.PatternSemantics.Semantics

/-! Row-matching safety for the exhaustiveness proof and pattern compiler. -/
namespace Flapjack.Compiler.Backend.PatternExh
open Flapjack PatternCommon PatternSemantics

private def toBroad (refs : HolFiniteMapExact Nat Term) : Nat → Option Term := refs.lookup

private def ofBroad (lookup : Nat → Option Term)
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat Term := ⟨lookup, support⟩

/-- The canonical finite-map parameter roundtrips through its lookup view. -/
theorem holFmapAsFiniteSupportParamWitness_matchRows_member_safe_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs := by
  cases refs
  exact ⟨rfl, rfl, rfl⟩

/-- Every row in a successful row scan is individually free of type errors. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "match_no_PTypeFailure"
  (fmap_as_finite_support_parameters := [refs])]
theorem matchRows_member_safe (refs : HolFiniteMapExact Nat Term) (value : Term)
    (rows : List (Pat × Nat)) (safe : matchRows refs rows value ≠ none) :
    ∀ row ∈ rows, pmatch refs row.1 value ≠ .typeFailure := by
  intro row member
  induction rows with
  | nil => simp at member
  | cons first rest ih =>
    obtain ⟨pattern, index⟩ := first
    have headSafe : pmatch refs pattern value ≠ .typeFailure := by
      intro bad
      apply safe
      rw [matchRows, bad]
    have tailSafe : matchRows refs rest value ≠ none := by
      cases head : pmatch refs pattern value with
      | typeFailure => exact (headSafe head).elim
      | failure => simpa [matchRows, head] using safe
      | success =>
        cases tail : matchRows refs rest value with
        | none =>
          apply False.elim
          apply safe
          rw [matchRows, head, tail]
        | some result => simp
    simp only [List.mem_cons] at member
    rcases member with equal | member
    · subst row
      exact headSafe
    · exact ih tailSafe member

end Flapjack.Compiler.Backend.PatternExh

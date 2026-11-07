import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileElement

/-! Preservation of the BVL-to-BVI reference relation by existing-cell writes. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value Ref)

/-- Updating a source cell and its relocated target cell preserves the
reference relation when the source cell already exists. This infrastructure
is used for array, byte-array, and thunk writes. -/
theorem refsRel_updateExisting (relocate : Nat → Nat)
    (source target : HolFiniteMapExact Nat (Ref Value)) (key : Nat) (cell : Ref Value)
    (related : refsRel relocate source target) (present : source.lookup key ≠ none) :
    refsRel relocate (source.updateEq (key, cell))
      (target.updateEq (relocate key, adjustRef relocate cell)) := by
  have domain (k : Nat) : (source.updateEq (key, cell)).lookup k ≠ none ↔ source.lookup k ≠ none := by
    by_cases eq : k = key
    · subst k
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, present]
    · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq]
  constructor
  · intro k hk
    have old := (domain k).1 hk
    by_cases eq : k = key
    · subst k
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    · have different : relocate k ≠ relocate key := by
        intro same
        exact eq (related.2.1 k key old present same)
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using related.1 k old
  · constructor
    · intro left right leftPresent rightPresent same
      exact related.2.1 left right ((domain left).1 leftPresent) ((domain right).1 rightPresent) same
    · intro k value lookup
      by_cases eq : k = key
      · subst k
        simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at lookup ⊢
        cases lookup
        rfl
      · have oldLookup : source.lookup k = some value := by
          simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using lookup
        have old : source.lookup k ≠ none := by rw [oldLookup]; simp
        have different : relocate k ≠ relocate key := by
          intro same
          exact eq (related.2.1 k key old present same)
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using related.2.2 k value oldLookup

/-- An existing-cell write preserves the complete state relation, including
separation of the target global array from relocated source references. -/
theorem stateRel_updateExisting {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (key : Nat) (cell : Ref Value) (related : stateRel relocate source target)
    (present : source.refs.lookup key ≠ none) :
    stateRel relocate { source with refs := source.refs.updateEq (key, cell) }
      { target with refs := target.refs.updateEq (relocate key, adjustRef relocate cell) } := by
  rcases related with ⟨refs, ffi, globals, rest⟩
  refine ⟨refsRel_updateExisting relocate source.refs target.refs key cell refs present, ffi, ?_, rest⟩
  intro ptr globalPtr
  obtain ⟨separate, size, lookup, bound⟩ := globals ptr globalPtr
  have distinct : ptr ≠ relocate key := separate key present
  refine ⟨?_, size, ?_, bound⟩
  · intro other otherPresent
    apply separate other
    by_cases eq : other = key
    · subst other
      exact present
    · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using otherPresent
  · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, distinct] using lookup

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

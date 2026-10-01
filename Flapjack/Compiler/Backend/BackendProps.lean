import Flapjack.HolRef
import Mathlib.Data.Set.Lattice

namespace Flapjack.Compiler.Backend.BackendProps

/-- Literal restriction of code-label pairs to nonzero entry indices. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "restrict_nonzero_def"]
def restrictNonzero (labels : Set (Nat × Nat)) : Set (Nat × Nat) :=
  {label | label ∈ labels ∧ label.2 ≠ 0}

/-- The restriction retains only members of the original arbitrary set. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "restrict_nonzero_SUBSET"]
theorem restrictNonzeroSubset (labels : Set (Nat × Nat)) :
    restrictNonzero labels ⊆ labels := by
  intro label h
  exact h.1

/-- The original subset hypothesis implies the restricted subset. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "restrict_nonzero_SUBSET_left"]
theorem restrictNonzeroSubsetLeft (s t : Set (Nat × Nat)) (h : s ⊆ t) :
    restrictNonzero s ⊆ t := by
  intro label hs
  exact h hs.1

/-- Restricting the left union operand preserves the original inclusion. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "restrict_nonzero_left_union"]
theorem restrictNonzeroLeftUnion (s a b : Set (Nat × Nat))
    (h : restrictNonzero s ⊆ a ∪ b) :
    restrictNonzero s ⊆ restrictNonzero a ∪ b := by
  intro label hs
  rcases h hs with ha | hb
  · exact Or.inl ⟨ha, hs.2⟩
  · exact Or.inr hb

/-- Restricting the right union operand preserves the original inclusion. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "restrict_nonzero_right_union"]
theorem restrictNonzeroRightUnion (s a b : Set (Nat × Nat))
    (h : restrictNonzero s ⊆ a ∪ b) :
    restrictNonzero s ⊆ a ∪ restrictNonzero b := by
  intro label hs
  rcases h hs with ha | hb
  · exact Or.inl ha
  · exact Or.inr ⟨hb, hs.2⟩

/-- Restriction is monotone under exactly the original subset premise. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "restrict_nonzero_mono"]
theorem restrictNonzeroMono (s t : Set (Nat × Nat)) (h : s ⊆ t) :
    restrictNonzero s ⊆ restrictNonzero t := by
  intro label hs
  exact ⟨h hs.1, hs.2⟩

/-- Restriction distributes over the union of an arbitrary set of sets. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "restrict_nonzero_BIGUNION"]
theorem restrictNonzeroBigUnion (ss : Set (Set (Nat × Nat))) :
    restrictNonzero (⋃₀ ss) = ⋃₀ (restrictNonzero '' ss) := by
  ext label
  constructor
  · intro h
    obtain ⟨s, hs, hlabel⟩ := Set.mem_sUnion.mp h.1
    exact Set.mem_sUnion.mpr
      ⟨restrictNonzero s, Set.mem_image_of_mem restrictNonzero hs, ⟨hlabel, h.2⟩⟩
  · intro h
    obtain ⟨t, ht, hlabel⟩ := Set.mem_sUnion.mp h
    obtain ⟨s, hs, rfl⟩ := ht
    exact ⟨Set.mem_sUnion.mpr ⟨s, hs, hlabel.1⟩, hlabel.2⟩

end Flapjack.Compiler.Backend.BackendProps

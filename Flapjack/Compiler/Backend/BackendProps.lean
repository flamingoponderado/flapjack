import Flapjack.HolRef
import Mathlib.Data.Set.Lattice

namespace Flapjack.Compiler.Backend.BackendProps

/-- Original zero-entry restriction over arbitrary Nat-pair sets.
This proof-side set operation has no executable compiler caller. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "restrict_zero_def"]
def restrictZero (labels : Set (Nat × Nat)) : Set (Nat × Nat) :=
  {label | label ∈ labels ∧ label.2 = 0}

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

/-- HOL `option_le_def`: `NONE` is the top of the order on `num option`,
    `NONE ≤ SOME _` fails, and `SOME` compares its payloads.  HOL's `bool`
    result is rendered as a decidable `Prop`. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_le_def"]
def optionLe : Option Nat → Option Nat → Prop
  | _, none => True
  | none, some _ => False
  | some n1, some n2 => n1 ≤ n2

instance optionLeDecidable (x y : Option Nat) : Decidable (optionLe x y) := by
  rcases x with _ | _ <;> rcases y with _ | _ <;> unfold optionLe <;> infer_instance

@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_le_refl"]
theorem optionLe_refl : ∀ x, optionLe x x := by
  intro x
  rcases x with _ | _ <;> simp [optionLe]

@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_le_trans"]
theorem optionLe_trans : ∀ x y z, optionLe x y ∧ optionLe y z → optionLe x z := by
  intro x y z h
  rcases x with _ | _ <;> rcases y with _ | _ <;> rcases z with _ | _ <;>
    simp_all [optionLe]; omega

/-- HOL `option_le_max_right`.  HOL `OPTION_MAP2 MAX n m` is `Option.map₂ max n m`
    (`SOME (MAX a b)` exactly when both are `SOME`). -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_le_max_right"]
theorem optionLe_max_right (x n m : Option Nat) :
    optionLe x (Option.map₂ max n m) ↔ optionLe x n ∨ optionLe x m := by
  rcases x with _ | _ <;> rcases n with _ | _ <;> rcases m with _ | _ <;>
    simp [optionLe]

end Flapjack.Compiler.Backend.BackendProps

import Mathlib.Data.Set.Insert
import Flapjack.Compiler.Backend.BackendProps

/-! Identical-input replay of original backendProps nonzero-label observations.
Finite examples and the two UNIV membership checks do not establish
cross-language equivalence. Universal subset/union laws are proved separately. -/
namespace Flapjack.Test.BackendPropsNonzeroLabelsParity
open Flapjack.Compiler.Backend.BackendProps

private abbrev Labels := Set (Nat × Nat)
private def mixed : Labels := {(7,0),(7,2),(8,1)}
private def left : Labels := {(7,0),(7,2)}
private def right : Labels := {(8,1),(8,0)}

-- nz_empty
example : restrictNonzero ∅ = (∅ : Labels) := by
  ext label
  simp [restrictNonzero]

-- nz_zero
example : restrictNonzero {(7,0),(0,0)} = (∅ : Labels) := by
  ext label
  rcases label with ⟨identifier, entry⟩
  by_cases zero : entry = 0 <;>
    simp [restrictNonzero, or_and_right, zero]

-- nz_first_zero
example : restrictNonzero {(0,0),(0,1)} = ({(0,1)} : Labels) := by
  ext label
  rcases label with ⟨identifier, entry⟩
  by_cases zero : entry = 0 <;>
    simp [restrictNonzero, or_and_right, zero]

-- nz_mixed
example : restrictNonzero mixed = ({(7,2),(8,1)} : Labels) := by
  ext label
  rcases label with ⟨identifier, entry⟩
  by_cases zero : entry = 0 <;>
    simp [restrictNonzero, mixed, or_and_right, zero]

-- nz_duplicate
example : restrictNonzero {(8,1),(8,1),(8,0)} = ({(8,1)} : Labels) := by
  ext label
  rcases label with ⟨identifier, entry⟩
  by_cases zero : entry = 0 <;>
    simp [restrictNonzero, or_and_right, zero]

-- nz_large
example : restrictNonzero
    {(1208925819614629174706176,0),
      (1208925819614629174706176,1208925819614629174706176)} =
    ({(1208925819614629174706176,1208925819614629174706176)} : Labels) := by
  ext label
  rcases label with ⟨identifier, entry⟩
  by_cases zero : entry = 0 <;>
    simp [restrictNonzero, or_and_right, zero]

-- nz_subset: non-vacuous application of the full universal source theorem.
example : restrictNonzero mixed ⊆ mixed := restrictNonzeroSubset mixed

-- nz_subset_left: the original premise and conclusion are both checked.
example : mixed ⊆ mixed ∪ {(9,0)} ∧ restrictNonzero mixed ⊆ mixed ∪ {(9,0)} := by
  have h : mixed ⊆ mixed ∪ {(9,0)} := Set.subset_union_left
  exact ⟨h, restrictNonzeroSubsetLeft mixed _ h⟩

-- nz_left_union
example : restrictNonzero mixed ⊆ left ∪ right ∧
    restrictNonzero mixed ⊆ restrictNonzero left ∪ right := by
  have h : restrictNonzero mixed ⊆ left ∪ right := by
    intro label hl
    rcases hl with ⟨hl, nonzero⟩
    simp only [mixed, Set.mem_insert_iff, Set.mem_singleton_iff] at hl
    rcases hl with rfl | rfl | rfl <;> simp_all [left, right]
  exact ⟨h, restrictNonzeroLeftUnion mixed left right h⟩

-- nz_right_union
example : restrictNonzero mixed ⊆ left ∪ right ∧
    restrictNonzero mixed ⊆ left ∪ restrictNonzero right := by
  have h : restrictNonzero mixed ⊆ left ∪ right := by
    intro label hl
    rcases hl with ⟨hl, nonzero⟩
    simp only [mixed, Set.mem_insert_iff, Set.mem_singleton_iff] at hl
    rcases hl with rfl | rfl | rfl <;> simp_all [left, right]
  exact ⟨h, restrictNonzeroRightUnion mixed left right h⟩

-- nz_mono
example : mixed ⊆ mixed ∪ {(9,0),(9,3)} ∧
    restrictNonzero mixed ⊆ restrictNonzero (mixed ∪ {(9,0),(9,3)}) := by
  have h : mixed ⊆ mixed ∪ {(9,0),(9,3)} := Set.subset_union_left
  exact ⟨h, restrictNonzeroMono mixed _ h⟩

-- nz_bigunion: arbitrary-set-of-sets theorem at overlapping/empty inputs.
example :
    let ss : Set Labels := {{(7,0),(8,1)}, ∅, {(8,1),(9,2)}}
    restrictNonzero (⋃₀ ss) = ⋃₀ (restrictNonzero '' ss) :=
  restrictNonzeroBigUnion _

-- nz_univ_kept
example : (1208925819614629174706176,1) ∈ restrictNonzero Set.univ := by
  simp [restrictNonzero]

-- nz_univ_zero (original result F).
example : (1208925819614629174706176,0) ∉ restrictNonzero Set.univ := by
  simp [restrictNonzero]

-- nz_false_premise (original result F).
example : ¬restrictNonzero mixed ⊆ ({(7,0)} : Labels) := by
  intro h
  have member : (7,2) ∈ restrictNonzero mixed := by simp [restrictNonzero, mixed]
  have impossible := h member
  simp at impossible

end Flapjack.Test.BackendPropsNonzeroLabelsParity

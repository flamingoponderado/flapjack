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

/-- Full original `option_le_max`:
`option_le (OPTION_MAP2 MAX n m) x ⇔ option_le n x /\ option_le m x`. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_le_max"]
theorem optionLe_max (n m x : Option Nat) :
    optionLe (Option.map₂ max n m) x ↔ optionLe n x ∧ optionLe m x := by
  rcases x with _ | _ <;> rcases n with _ | _ <;> rcases m with _ | _ <;>
    simp [optionLe]

/-- Full original `option_le_eq_eqns`: the four cancellation laws of
`option_le` under `OPTION_MAP2 $+` (`Option.map₂ (· + ·)`). -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_le_eq_eqns"]
theorem optionLe_eq_eqns (n m p : Option Nat) :
    (optionLe (Option.map₂ (· + ·) n m) (Option.map₂ (· + ·) n p) ↔
      n = none ∨ optionLe m p) ∧
    (optionLe (Option.map₂ (· + ·) n m) (Option.map₂ (· + ·) p n) ↔
      n = none ∨ optionLe m p) ∧
    (optionLe (Option.map₂ (· + ·) n m) (Option.map₂ (· + ·) p m) ↔
      m = none ∨ optionLe n p) ∧
    (optionLe (Option.map₂ (· + ·) n m) (Option.map₂ (· + ·) m p) ↔
      m = none ∨ optionLe n p) := by
  rcases n with _ | _ <;> rcases m with _ | _ <;> rcases p with _ | _ <;>
    simp [optionLe]
  omega

/-- Full original `option_map2_max_add`: `OPTION_MAP2 $+` distributes over
`OPTION_MAP2 MAX` on either side. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_map2_max_add"]
theorem optionMap2_max_add (n m p : Option Nat) :
    Option.map₂ (· + ·) n (Option.map₂ max m p) =
        Option.map₂ max (Option.map₂ (· + ·) n m) (Option.map₂ (· + ·) n p) ∧
    Option.map₂ (· + ·) (Option.map₂ max m p) n =
        Option.map₂ max (Option.map₂ (· + ·) m n) (Option.map₂ (· + ·) p n) := by
  rcases n with _ | _ <;> rcases m with _ | _ <;> rcases p with _ | _ <;>
    simp [Nat.add_max_add_left, Nat.add_max_add_right]

/-- Full original `OPTION_MAP2_MAX_COMM`:
`OPTION_MAP2 MAX x y = OPTION_MAP2 MAX y x`. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "OPTION_MAP2_MAX_COMM"]
theorem optionMap2_max_comm (x y : Option Nat) :
    Option.map₂ max x y = Option.map₂ max y x := by
  rcases x with _ | _ <;> rcases y with _ | _ <;> simp [Nat.max_comm]

/-- Full original `OPTION_MAP2_MAX_ASSOC`:
`OPTION_MAP2 MAX x (OPTION_MAP2 MAX y z) = OPTION_MAP2 MAX (OPTION_MAP2 MAX x y) z`. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "OPTION_MAP2_MAX_ASSOC"]
theorem optionMap2_max_assoc (x y z : Option Nat) :
    Option.map₂ max x (Option.map₂ max y z) = Option.map₂ max (Option.map₂ max x y) z := by
  rcases x with _ | _ <;> rcases y with _ | _ <;> rcases z with _ | _ <;>
    simp [Nat.max_assoc]

end Flapjack.Compiler.Backend.BackendProps

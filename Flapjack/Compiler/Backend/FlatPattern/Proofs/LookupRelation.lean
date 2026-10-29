import Flapjack.Compiler.Backend.FlatPattern.Proofs.GeneratedNames
import Batteries.Data.List.Basic

/-! Association-list relations used by the pattern-binding simulation. -/
namespace Flapjack.Compiler.Backend.FlatPattern

/-- HOL-shaped association-list lookup with propositional key equality. This
Flapjack helper avoids imposing a separate equality instance on HOL's
polymorphic key type. -/
noncomputable def holALookup {K V : Type} (entries : List (K × V)) (key : K) : Option V :=
  open Classical in
  match entries with
  | [] => none
  | (entryKey, value) :: rest => if key = entryKey then some value else holALookup rest key

/-- Propositional lookup agrees with the evaluator's list lookup whenever the
key's Boolean equality is lawful. -/
theorem holALookup_eq_lookup {K V : Type} [BEq K] [LawfulBEq K] (entries : List (K × V)) (key : K) :
    holALookup entries key = entries.lookup key := by
  classical
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨entryKey, value⟩ := entry
    by_cases same : key = entryKey
    · subst entryKey
      simp [holALookup]
    · have beqFalse : (key == entryKey) = false := by
        cases h : key == entryKey <;> simp_all [beq_iff_eq]
      simp [holALookup, List.lookup_cons, same, beqFalse, ih]

/-- The HOL-shaped lookup agrees with flat evaluation's lookup on mlstring
identifiers. -/
theorem holALookup_mlString {V : Type} (entries : List (Flapjack.Basis.Pure.MlString.MlString × V))
    (key : Flapjack.Basis.Pure.MlString.MlString) : holALookup entries key = entries.lookup key := by
  exact holALookup_eq_lookup entries key

/-- Association-list lookup searches the right list only when the left list
does not contain the key. -/
theorem holALookup_append {K V : Type} (left right : List (K × V)) (key : K) :
    holALookup (left ++ right) key = (holALookup left key).orElse (fun _ => holALookup right key) := by
  classical
  induction left with
  | nil => simp [holALookup]
  | cons entry rest ih =>
    obtain ⟨entryKey, value⟩ := entry
    by_cases same : key = entryKey <;> simp [holALookup, same, ih]

/-- The original option relation for independently typed payloads. -/
def optionRel {A B : Type} (relation : A → B → Prop) : Option A → Option B → Prop
  | none, none => True
  | some left, some right => relation left right
  | _, _ => False

/-- Related lookups for the keys selected by a predicate. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "ALOOKUP_rel_def"]
def aLookupRel {K A B : Type} (predicate : K → Prop) (relation : A → B → Prop)
    (left : List (K × A)) (right : List (K × B)) : Prop :=
  ∀ key, predicate key → optionRel relation (holALookup left key) (holALookup right key)

/-- Empty association lists are related for any key and value relations. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "ALOOKUP_rel_empty"]
theorem aLookupRel_empty {K A B : Type} (predicate : K → Prop) (relation : A → B → Prop) :
    aLookupRel predicate relation [] [] := by
  simp [aLookupRel, holALookup, optionRel]

/-- Adding a key outside the observed predicate to either side does not change
the relation. The original theorem uses the same value type on both sides. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "ALOOKUP_rel_cons_false"]
theorem aLookupRel_cons_false {K V : Type} (predicate : K → Prop) (relation : V → V → Prop)
    (key : K) (value : V) (left right : List (K × V)) :
    (¬ predicate key → (aLookupRel predicate relation ((key, value) :: left) right ↔ aLookupRel predicate relation left right)) ∧
    (¬ predicate key → (aLookupRel predicate relation left ((key, value) :: right) ↔ aLookupRel predicate relation left right)) := by
  classical
  constructor <;> intro excluded <;> unfold aLookupRel <;> constructor <;> intro related query selected
  all_goals have different : query ≠ key := by intro same; subst query; exact excluded selected
  all_goals simpa [holALookup, different] using related query selected

/-- A successful association-list lookup identifies an actual list member. -/
theorem holALookup_member {K V : Type} (entries : List (K × V)) (key : K) (value : V)
    (found : holALookup entries key = some value) : (key, value) ∈ entries := by
  classical
  induction entries with
  | nil => simp [holALookup] at found
  | cons entry rest ih =>
    obtain ⟨entryKey, entryValue⟩ := entry
    by_cases same : key = entryKey
    · subst entryKey
      simp [holALookup] at found
      subst entryValue
      simp
    · simp [holALookup, same] at found
      exact List.mem_cons_of_mem _ (ih found)

/-- A relation that is reflexive on the observed bindings relates a list to itself. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "ALOOKUP_rel_refl"]
theorem aLookupRel_refl {K V : Type} (predicate : K → Prop) (relation : V → V → Prop)
    (entries : List (K × V)) (refl : ∀ key value, predicate key → (key, value) ∈ entries → relation value value) :
    aLookupRel predicate relation entries entries := by
  intro key selected
  cases found : holALookup entries key with
  | none => simp [optionRel]
  | some value =>
    exact refl key value selected (holALookup_member entries key value found)

/-- Matching heads preserve the lookup relation when their values are related
at observed keys. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "ALOOKUP_rel_cons"]
theorem aLookupRel_cons {K A B : Type} (predicate : K → Prop) (relation : A → B → Prop)
    (key : K) (leftValue : A) (rightValue : B) (left : List (K × A)) (right : List (K × B))
    (head : predicate key → relation leftValue rightValue) (tail : aLookupRel predicate relation left right) :
    aLookupRel predicate relation ((key, leftValue) :: left) ((key, rightValue) :: right) := by
  classical
  intro query selected
  by_cases same : query = key
  · subst query
    simpa [holALookup, optionRel] using head selected
  · simpa [holALookup, same] using tail query selected

/-- Pointwise related mapped bindings induce related association-list lookups. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "ALOOKUP_rel_MAP_same"]
theorem aLookupRel_map_same {X K A B : Type} (predicate : K → Prop) (relation : A → B → Prop)
    (f : X → K × A) (g : X → K × B) (xs : List X)
    (pointwise : ∀ x ∈ xs, (f x).1 = (g x).1 ∧
      (predicate (g x).1 → relation (f x).2 (g x).2)) :
    aLookupRel predicate relation (xs.map f) (xs.map g) := by
  induction xs with
  | nil => exact aLookupRel_empty predicate relation
  | cons x xs ih =>
    have head := pointwise x (by simp)
    have tail : ∀ y ∈ xs, (f y).1 = (g y).1 ∧
        (predicate (g y).1 → relation (f y).2 (g y).2) := by
      intro y member
      exact pointwise y (by simp [member])
    cases fx : f x with
    | mk key leftValue =>
     cases gx : g x with
     | mk key' rightValue =>
      simp only [fx, gx] at head
      simp only [List.map_cons, fx, gx]
      cases head.1
      exact aLookupRel_cons predicate relation key leftValue rightValue (xs.map f) (xs.map g)
        head.2 (ih tail)

/-- Pointwise weakening of the payload relation preserves related lookups. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "ALOOKUP_rel_mono_rel"]
theorem aLookupRel_mono_rel {K A B : Type} (predicate : K → Prop) (relation relation' : A → B → Prop)
    (left : List (K × A)) (right : List (K × B))
    (weaken : ∀ leftValue rightValue, relation leftValue rightValue → relation' leftValue rightValue)
    (related : aLookupRel predicate relation left right) : aLookupRel predicate relation' left right := by
  intro key selected
  have h := related key selected
  cases leftLookup : holALookup left key <;> cases rightLookup : holALookup right key <;>
    simp [leftLookup, rightLookup, optionRel] at h ⊢
  exact weaken _ _ h

/-- Equality-related lookup results are equal at observed keys. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "ALOOKUP_rel_EQ_ALOOKUP"]
theorem aLookupRel_eq_lookup {K V : Type} (predicate : K → Prop) (left right : List (K × V))
    (key : K) (related : aLookupRel predicate Eq left right) (selected : predicate key) :
    holALookup left key = holALookup right key := by
  have h := related key selected
  cases leftLookup : holALookup left key <;> cases rightLookup : holALookup right key <;>
    simp [leftLookup, rightLookup, optionRel] at h ⊢
  exact h

/-- An unobserved prefix on the left does not affect the lookup relation. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "ALOOKUP_rel_APPEND_L_false"]
theorem aLookupRel_append_left_false {K A B : Type} (predicate : K → Prop) (relation : A → B → Prop)
    (front suffix : List (K × A)) (right : List (K × B))
    (excluded : ∀ binding ∈ front, ¬ predicate binding.1) :
    aLookupRel predicate relation (front ++ suffix) right ↔ aLookupRel predicate relation suffix right := by
  have absent (key : K) (selected : predicate key) : holALookup front key = none := by
    cases found : holALookup front key with
    | none => rfl
    | some value =>
      have member := holALookup_member front key value found
      exact (excluded (key, value) member selected).elim
  unfold aLookupRel
  constructor <;> intro related key selected
  all_goals simpa [holALookup_append, absent key selected] using related key selected

/-- Pairwise lookup relations on prefixes and suffixes compose across append. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "ALOOKUP_rel_append_suff"]
theorem aLookupRel_append {K A B : Type} (predicate : K → Prop) (relation : A → B → Prop)
    (left₁ left₂ : List (K × A)) (right₁ right₂ : List (K × B))
    (first : aLookupRel predicate relation left₁ right₁) (second : aLookupRel predicate relation left₂ right₂) :
    aLookupRel predicate relation (left₁ ++ left₂) (right₁ ++ right₂) := by
  intro key selected
  have h₁ := first key selected
  have h₂ := second key selected
  simp only [holALookup_append]
  cases leftFound : holALookup left₁ key <;> cases rightFound : holALookup right₁ key <;>
    simp [leftFound, rightFound, optionRel] at h₁ ⊢
  · exact h₂
  · exact h₁

/-- Pairwise-related entries with equal keys imply related association-list
lookups. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "ALOOKUP_rel_eq_fst"]
theorem aLookupRel_of_forall₂ {K A B : Type} (predicate : K → Prop) (relation : A → B → Prop)
    (left : List (K × A)) (right : List (K × B))
    (related : List.Forall₂ (fun x y => x.1 = y.1 ∧ (predicate x.1 → relation x.2 y.2)) left right) :
    aLookupRel predicate relation left right := by
  induction related with
  | nil => exact aLookupRel_empty predicate relation
  | @cons leftEntry rightEntry leftTail rightTail head tail ih =>
    obtain ⟨leftKey, leftValue⟩ := leftEntry
    obtain ⟨rightKey, rightValue⟩ := rightEntry
    simp only at head
    rcases head with ⟨same, headRelation⟩
    subst rightKey
    exact aLookupRel_cons predicate relation leftKey leftValue rightValue leftTail rightTail headRelation ih

end Flapjack.Compiler.Backend.FlatPattern

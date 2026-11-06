import Flapjack.Compiler.Backend.FlatPattern.Proofs.GeneratedNames
import Flapjack.Misc.Alist
import Flapjack.Misc.Option.Rel
import Batteries.Data.List.Basic

/-! Association-list relations used by the pattern-binding simulation. -/
namespace Flapjack.Compiler.Backend.FlatPattern

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

/-- Related association lists have related lookups when matching keys identify
related values. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "LIST_REL_ALOOKUP_OPTREL"]
theorem listRelALookupOptRel {K A B : Type} (relation : K × A → K × B → Prop)
    (valueRelation : A → B → Prop) (left : List (K × A)) (right : List (K × B)) (key : K)
    (related : List.Forall₂ relation left right)
    (matching : ∀ x y, relation x y → x ∈ left → y ∈ right →
      (key = x.1 ∨ key = y.1) → x.1 = y.1 ∧ valueRelation x.2 y.2) :
    optionRel valueRelation (holALookup left key) (holALookup right key) := by
  classical
  induction related with
  | nil => simp [holALookup, optionRel]
  | @cons x y xs ys head tail ih =>
    have tailMatching : ∀ a b, relation a b → a ∈ xs → b ∈ ys →
        (key = a.1 ∨ key = b.1) → a.1 = b.1 ∧ valueRelation a.2 b.2 := by
      intro a b hab ha hb hit
      exact matching a b hab (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb) hit
    obtain ⟨kx, vx⟩ := x
    obtain ⟨ky, vy⟩ := y
    by_cases hx : key = kx
    · have pair := matching (kx, vx) (ky, vy) head (by simp) (by simp) (Or.inl hx)
      have sameKeys : kx = ky := pair.1
      subst ky
      simpa [holALookup, hx, optionRel] using pair.2
    · by_cases hy : key = ky
      · have pair := matching (kx, vx) (ky, vy) head (by simp) (by simp) (Or.inr hy)
        exact (hx (hy.trans pair.1.symm)).elim
      · simp only [holALookup, hx, hy, if_false]
        exact ih tailMatching

/-- Related association lists have equal lookups when matching keys identify
equal entries. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "LIST_REL_ALOOKUP"]
theorem listRelALookup {K V : Type} (relation : K × V → K × V → Prop)
    (left right : List (K × V)) (key : K) (related : List.Forall₂ relation left right)
    (matching : ∀ x y, relation x y → x ∈ left → y ∈ right →
      (key = x.1 ∨ key = y.1) → x = y) :
    holALookup left key = holALookup right key := by
  have result := listRelALookupOptRel relation Eq left right key related (by
    intro x y hxy hx hy hit
    have same := matching x y hxy hx hy hit
    subst y
    exact ⟨rfl, rfl⟩)
  cases leftEq : holALookup left key <;> cases rightEq : holALookup right key <;>
    simp_all [optionRel]

/-- Flapjack helper: filtering twice is one filter when the second predicate
implies the first on the list. This is not a separate HOL declaration. -/
private theorem filter_filter_of_subsumed {A : Type} (first second : A → Bool)
    (xs : List A) (subsumed : ∀ x ∈ xs, second x = true → first x = true) :
    (xs.filter first).filter second = xs.filter second := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases firstAt : first x <;> cases secondAt : second x <;>
      simp_all [List.filter]

/-- Flapjack helper: aligned list elements that agree on a filter predicate
remain related after filtering. This is not a separate HOL declaration. -/
private theorem forall₂_filter_of_members {A B : Type} (relation : A → B → Prop)
    (first : A → Bool) (second : B → Bool) {xs : List A} {ys : List B}
    (related : List.Forall₂ relation xs ys)
    (agree : ∀ x ∈ xs, ∀ y ∈ ys, relation x y → first x = second y) :
    List.Forall₂ relation (xs.filter first) (ys.filter second) := by
  induction related with
  | nil => simp
  | @cons x y xs ys head tail ih =>
    have same := agree x (by simp) y (by simp) head
    have tailAgree : ∀ x ∈ xs, ∀ y ∈ ys, relation x y → first x = second y := by
      intro a ha b hb hab
      exact agree a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hab
    have tailRelated := ih tailAgree
    cases firstAt : first x <;> cases secondAt : second y <;>
      simp_all [List.filter]

/-- Related filtered lists remain related when both filters are narrowed in
the same way on related entries. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "LIST_REL_FILTER_MONO"]
theorem listRelFilterMono {A B : Type} (relation : A → B → Prop)
    (p1 p3 : A → Bool) (p2 p4 : B → Bool) (xs : List A) (ys : List B)
    (related : List.Forall₂ relation (xs.filter p1) (ys.filter p2))
    (leftNarrow : ∀ x ∈ xs, p3 x = true → p1 x = true)
    (rightNarrow : ∀ y ∈ ys, p4 y = true → p2 y = true)
    (agree : ∀ x ∈ xs, ∀ y ∈ ys, relation x y → p3 x = p4 y) :
    List.Forall₂ relation (xs.filter p3) (ys.filter p4) := by
  have narrowed := forall₂_filter_of_members relation p3 p4 related (by
    intro x hx y hy hxy
    exact agree x (List.mem_filter.mp hx).1 y (List.mem_filter.mp hy).1 hxy)
  simpa [filter_filter_of_subsumed p1 p3 xs leftNarrow,
    filter_filter_of_subsumed p2 p4 ys rightNarrow] using narrowed

/-- A false condition selects the second branch. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "COND_false"]
theorem condFalse {A : Type} (condition : Bool) (yes no : A) (isFalse : condition = false) :
    (if condition then yes else no) = no := by
  simp [isFalse]

/-- A true condition selects the first branch. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "COND_true"]
theorem condTrue {A : Type} (condition : Bool) (yes no : A) (isTrue : condition = true) :
    (if condition then yes else no) = yes := by
  simp [isTrue]

/-- Flapjack helper: list relation under equality is list equality. This is
used to state HOL's equality specializations without duplicating their proof. -/
private theorem forall₂_eq_iff {A : Type} (xs ys : List A) :
    List.Forall₂ Eq xs ys ↔ xs = ys := by
  constructor
  · intro related
    induction related with
    | nil => rfl
    | cons same tail ih => cases same; simp [ih]
  · intro same
    subst ys
    induction xs with
    | nil => exact .nil
    | cons x xs ih => exact .cons rfl ih

/-- Equal filtered lists remain equal after compatible narrowing. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "FILTER_EQ_MONO"]
theorem filterEqMono {A : Type} (p1 p2 p3 p4 : A → Bool) (xs ys : List A)
    (filtered : xs.filter p1 = ys.filter p2)
    (leftNarrow : ∀ x ∈ xs, p3 x = true → p1 x = true)
    (rightNarrow : ∀ y ∈ ys, p4 y = true → p2 y = true)
    (agree : ∀ x ∈ xs, ∀ y ∈ ys, x = y → p3 x = p4 y) :
    xs.filter p3 = ys.filter p4 := by
  apply (forall₂_eq_iff _ _).mp
  exact listRelFilterMono Eq p1 p3 p2 p4 xs ys
    ((forall₂_eq_iff _ _).mpr filtered) leftNarrow rightNarrow agree

/-- Filtering a list and then narrowing agrees with narrowing its filtered
result. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "FILTER_EQ_MONO_TRANS"]
theorem filterEqMonoTrans {A : Type} (p1 p3 : A → Bool) (xs ys : List A)
    (filtered : xs.filter p1 = ys)
    (leftNarrow : ∀ x ∈ xs, p3 x = true → p1 x = true)
    (agree : ∀ x ∈ xs, ∀ y ∈ ys, x = y → p3 x = p3 y) :
    xs.filter p3 = ys.filter p3 := by
  apply filterEqMono p1 (fun _ => true) p3 p3 xs ys
  · have all : ys.filter (fun _ => true) = ys := by
      induction ys with
      | nil => rfl
      | cons y ys ih => simp [List.filter]
    simpa only [all] using filtered
  · exact leftNarrow
  · simp
  · exact agree

/-- Filtering preserves lookup when every entry for the queried key is kept. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "FILTER_EQ_ALOOKUP_EQ"]
theorem filterEqALookupEq {K V : Type} (predicate : K × V → Bool)
    (xs ys : List (K × V)) (key : K) (filtered : xs.filter predicate = ys)
    (kept : ∀ value, predicate (key, value) = true) :
    holALookup xs key = holALookup ys key := by
  classical
  subst ys
  induction xs with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨entryKey, value⟩ := entry
    by_cases same : key = entryKey
    · subst entryKey
      simp [List.filter, kept value, holALookup]
    · cases selected : predicate (entryKey, value) <;>
        simp [List.filter, selected, holALookup, same, ih]

/-- Looking up after such a filter gives the original lookup. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "ALOOKUP_FILTER_EQ"]
theorem aLookupFilterEq {K V : Type} (predicate : K × V → Bool)
    (xs : List (K × V)) (key : K) (kept : ∀ value, predicate (key, value) = true) :
    holALookup (xs.filter predicate) key = holALookup xs key :=
  (filterEqALookupEq predicate xs (xs.filter predicate) key rfl kept).symm

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

/-- Narrowing observed keys and weakening their value relation preserves
related lookups. HOL's predicate premise quantifies two unused variables of
independent inhabited types; these vacuous binders are omitted here. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "ALOOKUP_rel_mono"]
theorem aLookupRel_mono {K A B : Type} (predicate predicate' : K → Prop)
    (relation relation' : A → B → Prop) (left : List (K × A)) (right : List (K × B))
    (related : aLookupRel predicate relation left right)
    (narrow : ∀ key, predicate' key → predicate key)
    (weaken : ∀ key leftValue rightValue,
      predicate' key ∧ relation leftValue rightValue → relation' leftValue rightValue) :
    aLookupRel predicate' relation' left right := by
  intro key selected
  have old := related key (narrow key selected)
  cases leftLookup : holALookup left key <;> cases rightLookup : holALookup right key <;>
    simp [leftLookup, rightLookup, optionRel] at old ⊢
  exact weaken key _ _ ⟨selected, old⟩

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
  exact aLookupRel_mono predicate predicate relation relation' left right related
    (fun _ selected => selected) (fun _ _ _ h => weaken _ _ h.2)

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

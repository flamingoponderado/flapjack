import Flapjack.Misc.List
import Flapjack.SemanticPrimitivesHOL
import Batteries.Data.List.Basic

/-! Relation between store entries in the source semantics. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.SemanticPrimitivesHOL

@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "sv_rel_def"]
def storeValueRel {A B : Type} (relation : A → B → Prop) : StoreValue A → StoreValue B → Prop
  | .refv left, .refv right => relation left right
  | .w8array left, .w8array right => left = right
  | .varray left, .varray right => List.Forall₂ relation left right
  | .thunk mode left, .thunk mode' right => mode = mode' ∧ relation left right
  | _, _ => False

/-- Pointwise implication lifts through the complete store-value relation. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "sv_rel_mono"]
theorem storeValueRel_mono {A B : Type} (P Q : A → B → Prop)
    (monotone : ∀ x y, P x y → Q x y) (x : StoreValue A) (y : StoreValue B)
    (related : storeValueRel P x y) : storeValueRel Q x y := by
  cases x <;> cases y <;> simp_all [storeValueRel]
  case varray.varray _ _ =>
    induction related with
    | nil => exact .nil
    | cons head _ ih => exact .cons (monotone _ _ head) ih

/-- A related store entry can be found at the same index on the target side.
This shared curried helper is used by the HOL-shaped `store_lookup` port in
the source evaluator proof. -/
theorem storeValueRel_lookup {A B : Type} {R : A → B → Prop} {left : List (StoreValue A)}
    {right : List (StoreValue B)} (related : List.Forall₂ (storeValueRel R) left right)
    (index : Nat) (value : StoreValue A) (found : storeLookup index left = some value) :
    ∃ target, storeLookup index right = some target ∧ storeValueRel R value target := by
  induction related generalizing index with
  | nil => simp [storeLookup] at found
  | @cons source target left right head tail ih =>
    cases index with
    | zero =>
      simp [storeLookup] at found
      subst value
      exact ⟨target, rfl, head⟩
    | succ index =>
      simp only [storeLookup, List.getElem?_cons_succ] at found ⊢
      exact ih index found

/-- Store assignment makes the same type check on related entries.
HOL performs this type comparison inline. -/
theorem storeValueRel_sameType {A B : Type} {R : A → B → Prop}
    (left old : StoreValue A) (right old' : StoreValue B)
    (entries : storeValueRel R left right) (values : storeValueRel R old old') :
    storeValueSameType left old = storeValueSameType right old' := by
  cases left <;> cases right <;> cases old <;> cases old' <;>
    simp_all [storeValueRel, storeValueSameType]
  case thunk.thunk.thunk.thunk m _ m' _ _ _ _ _ =>
    cases m <;> cases m' <;> simp_all

/-- A successful store assignment has a related successful assignment.
This shared curried helper is used by the HOL-shaped `store_assign` port in
the source evaluator proof. -/
theorem storeAssign_related {A B : Type} {R : A → B → Prop}
    {left : Store A} {right : Store B} {value : StoreValue A} {value' : StoreValue B}
    (stores : List.Forall₂ (storeValueRel R) left right) (index : Nat)
    (values : storeValueRel R value value') {result : Store A}
    (assigned : storeAssign index value left = some result) :
    ∃ result', storeAssign index value' right = some result' ∧
      List.Forall₂ (storeValueRel R) result result' := by
  cases found : storeLookup index left with
  | none =>
    change left[index]? = none at found
    simp [storeAssign, found] at assigned
  | some entry =>
    obtain ⟨entry', found', entries⟩ := storeValueRel_lookup stores index entry found
    change left[index]? = some entry at found
    change right[index]? = some entry' at found'
    have types := storeValueRel_sameType entry value entry' value' entries values
    by_cases valid : storeValueSameType entry value = true
    · have valid' : storeValueSameType entry' value' = true := by rw [← types]; exact valid
      have resultEq : left.set index value = result := by
        simpa [storeAssign, found, valid] using assigned
      refine ⟨right.set index value', ?_, ?_⟩
      · simp [storeAssign, found', valid']
      · rw [← resultEq]
        exact Flapjack.forall₂_set _ _ _ value value' index ⟨values, stores⟩
    · simp [storeAssign, found, valid] at assigned

/-- Inspecting related stores at the same index preserves absence.
HOL proves this lookup fact inline when needed. -/
theorem storeValueRel_lookup_none {A B : Type} {R : A → B → Prop}
    {left : List (StoreValue A)} {right : List (StoreValue B)}
    (related : List.Forall₂ (storeValueRel R) left right) (index : Nat)
    (absent : storeLookup index left = none) : storeLookup index right = none := by
  induction related generalizing index with
  | nil => simp [storeLookup]
  | cons _ _ ih =>
    cases index with
    | zero => simp [storeLookup] at absent
    | succ index =>
      simp only [storeLookup, List.getElem?_cons_succ] at absent ⊢
      exact ih index absent


end Flapjack.SemanticPrimitivesProps

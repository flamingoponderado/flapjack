import Flapjack.Compiler.Backend.SourceToFlat.Proofs.StateRel

/-! Store-update infrastructure for the factored source-to-flat state relation.
The underlying value and state relations remain subject to HOL review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.SemanticPrimitivesHOL

/-- Flapjack infrastructure: pointwise related lists remain related after
updating the same index with related elements. -/
theorem forall₂_set {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (related : List.Forall₂ R xs ys) (n : Nat) (x : α) (y : β) (replacement : R x y) :
    List.Forall₂ R (xs.set n x) (ys.set n y) := by
  induction related generalizing n with
  | nil => simp
  | cons head tail ih =>
    cases n with
    | zero => simp only [List.set_cons_zero]; exact .cons replacement tail
    | succ n => simp only [List.set_cons_succ]; exact .cons head (ih n)

/-- Flapjack infrastructure: appending related values preserves a pointwise
list relation. -/
theorem forall₂_append_one {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (related : List.Forall₂ R xs ys) (x : α) (y : β) (replacement : R x y) :
    List.Forall₂ R (xs ++ [x]) (ys ++ [y]) := by
  induction related with
  | nil => exact .cons replacement .nil
  | cons head tail ih => exact .cons head ih

/-- Successful source store assignment has a related flat assignment at the
same list index. This is infrastructure over the factored value relation. -/
theorem storeAssign_related (genv : GlobalEnv)
    (source : Store SemanticPrimitivesHOL.Value) (flat : Store FlatSem.Value)
    (storesRel : List.Forall₂ (StoreValueRel genv) source flat) (n : Nat)
    (value : StoreValue SemanticPrimitivesHOL.Value) (flatValue : StoreValue FlatSem.Value)
    (valueRel : StoreValueRel genv value flatValue) (source' : Store SemanticPrimitivesHOL.Value)
    (assigned : storeAssign n value source = some source') :
    ∃ flat', storeAssign n flatValue flat = some flat' ∧
      List.Forall₂ (StoreValueRel genv) source' flat' := by
  cases oldLookup : source[n]? with
  | none => simp [storeAssign, oldLookup] at assigned
  | some old =>
    obtain ⟨flatOld, flatLookup, oldRel⟩ := forall₂_lookup storesRel n old oldLookup
    cases same : storeValueSameType old value with
    | false => simp [storeAssign, oldLookup, same] at assigned
    | true =>
      have flatSame : storeValueSameType flatOld flatValue = true :=
        (storeValueSameType_related genv old value flatOld flatValue oldRel valueRel).symm.trans same
      refine ⟨flat.set n flatValue, ?_, ?_⟩
      · simp [storeAssign, flatLookup, flatSame]
      · have sourceEq : source.set n value = source' := by simpa [storeAssign, oldLookup, same] using assigned
        rw [← sourceEq]
        exact forall₂_set storesRel n value flatValue valueRel

/-- A successful source assignment has a flat assignment one slot later,
preserving the reserved entry and the state relation. This is infrastructure
over the factored source-to-flat value and state relations. -/
theorem stateRel_storeAssign {C F : Type} (genv : GlobalEnv)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (statesRel : StateRel genv source flat) (n : Nat)
    (value : StoreValue SemanticPrimitivesHOL.Value) (flatValue : StoreValue FlatSem.Value)
    (valueRel : StoreValueRel genv value flatValue) (sourceRefs : Store SemanticPrimitivesHOL.Value)
    (assigned : storeAssign n value source.refs = some sourceRefs) :
    ∃ flatRefs, storeAssign (n + 1) flatValue flat.refs = some flatRefs ∧
      flatRefs.take 1 = flat.refs.take 1 ∧
      StateRel genv { source with refs := sourceRefs } { flat with refs := flatRefs } := by
  cases statesRel with
  | intro nonempty refs clock ffi =>
    obtain ⟨reserved, rest, hflat⟩ := List.exists_cons_of_ne_nil nonempty
    have relatedRest : List.Forall₂ (StoreValueRel genv) source.refs rest := by simpa [hflat] using refs
    obtain ⟨flatRest, flatAssigned, updatedRel⟩ :=
      storeAssign_related genv source.refs rest relatedRest n value flatValue valueRel sourceRefs assigned
    refine ⟨reserved :: flatRest, ?_, ?_, ?_⟩
    · simp only [hflat]
      change storeAssign (Nat.succ n) flatValue (reserved :: rest) = some (reserved :: flatRest)
      have wholeEq : storeAssign (Nat.succ n) flatValue (reserved :: rest) =
          (storeAssign n flatValue rest).map (List.cons reserved) := by
        simp only [storeAssign, List.getElem?_cons_succ, List.set_cons_succ]
        cases rest[n]? with
        | none => rfl
        | some old =>
          change (if storeValueSameType old flatValue then some (reserved :: rest.set n flatValue) else none) =
            (if storeValueSameType old flatValue then some (rest.set n flatValue) else none).map (List.cons reserved)
          split <;> rfl
      rw [wholeEq, flatAssigned]
      rfl
    · simp [hflat]
    · apply StateRel.intro
      · simp
      · simpa using updatedRel
      · exact clock
      · exact ffi

/-- Allocating related entries preserves the state relation and reserves one
additional leading flat-store slot. This is Flapjack infrastructure over the
factored source-to-flat relations. -/
theorem stateRel_storeAlloc {C F : Type} (genv : GlobalEnv)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (statesRel : StateRel genv source flat)
    (value : StoreValue SemanticPrimitivesHOL.Value) (flatValue : StoreValue FlatSem.Value)
    (valueRel : StoreValueRel genv value flatValue) :
    StateRel genv { source with refs := (storeAlloc value source.refs).1 }
      { flat with refs := (storeAlloc flatValue flat.refs).1 } ∧
    (storeAlloc flatValue flat.refs).2 = (storeAlloc value source.refs).2 + 1 ∧
    (storeAlloc flatValue flat.refs).1.take 1 = flat.refs.take 1 := by
  cases statesRel with
  | intro nonempty refs clock ffi =>
    obtain ⟨reserved, rest, hflat⟩ := List.exists_cons_of_ne_nil nonempty
    have relatedRest : List.Forall₂ (StoreValueRel genv) source.refs rest := by simpa [hflat] using refs
    have updatedRel := forall₂_append_one relatedRest value flatValue valueRel
    constructor
    · apply StateRel.intro
      · simp [storeAlloc, hflat]
      · simpa [storeAlloc, hflat] using updatedRel
      · exact clock
      · exact ffi
    · constructor
      · simp [storeAlloc, hflat, relatedRest.length_eq, Nat.add_comm]
      · simp [storeAlloc, hflat]

end Flapjack.Compiler.Backend.SourceToFlat

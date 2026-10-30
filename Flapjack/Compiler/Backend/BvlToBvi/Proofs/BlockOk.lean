import Flapjack.Compiler.Backend.BvlToBvi.Proofs.ApplyOk

/-! Block-operation cases of BVL well-formedness preservation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value Ref State doApp)

namespace BlockCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end BlockCarrier

/-- Flapjack helper: decoding a well-formed list value yields well-formed
elements, used for the original block-operation cases. -/
theorem valueToList_ok (refs : HolFiniteMapExact Nat (Ref Value))
    (value : Value) (values : List Value) (ok : bvOk refs value)
    (decode : BvlSem.valueToList value = some values) : bvOkList refs values := by
  cases value with
  | block tag fields =>
    cases fields with
    | nil =>
      simp only [BvlSem.valueToList] at decode
      split at decode
      · simp_all [bvOkList]
      · contradiction
    | cons head tail =>
      cases tail with
      | nil => simp [BvlSem.valueToList] at decode
      | cons tail rest =>
        cases rest with
        | cons _ _ => simp [BvlSem.valueToList] at decode
        | nil =>
          simp only [BvlSem.valueToList] at decode
          split at decode
          · cases h : BvlSem.valueToList tail with
            | none => simp [h] at decode
            | some rest =>
              simp only [h, Option.map, Option.some.injEq] at decode
              subst values
              simp only [bvOk, bvOkList] at ok
              simp only [bvOkList]
              exact ⟨ok.1, valueToList_ok refs tail rest ok.2.1 h⟩
          · contradiction
  | _ => simp [BvlSem.valueToList] at decode
termination_by sizeOf value

/-- Block-construction case of primitive application. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok_cons {C F : Type} (tag : Nat)
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (ok : stateOk s) (argsOk : bvOkList s.refs args)
    (run : doApp (.blockOp (.cons tag)) args s = .val (value, t)) :
    stateOk t ∧ bvOk t.refs value ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  simp only [doApp, BvlSem.applyBlock, Flapjack.SemanticPrimitivesHOL.Result.val.injEq,
    Prod.mk.injEq] at run
  rcases run with ⟨rfl, rfl⟩
  exact ⟨ok, by simpa [bvOk] using argsOk, id⟩

/-- Extended-block-construction case of primitive application. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok_consExtend {C F : Type} (tag : Nat)
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (ok : stateOk s) (argsOk : bvOkList s.refs args)
    (run : doApp (.blockOp (.consExtend tag)) args s = .val (value, t)) :
    stateOk t ∧ bvOk t.refs value ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  simp only [doApp] at run
  cases h : BvlSem.applyBlock (.consExtend tag) args s with
  | none => simp [h] at run
  | some pair =>
    cases pair with
    | mk result next =>
      simp only [h, Flapjack.SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      unfold BvlSem.applyBlock at h
      repeat' first | split at h | contradiction
      all_goals simp_all [bvOk, bvOkList]
      rcases h with ⟨rfl, _⟩
      simp only [bvOk]
      apply (bvOkList_iff _ _).2
      intro item member
      rcases List.mem_append.mp member with initial | segment
      · exact (bvOkList_iff _ _).1 argsOk.2 item initial
      · exact (bvOkList_iff _ _).1 argsOk.1 item
          (List.mem_of_mem_drop (List.mem_of_mem_take segment))

/-- List-append case of primitive application. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok_listAppend {C F : Type}
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (ok : stateOk s) (argsOk : bvOkList s.refs args)
    (run : doApp (.blockOp .listAppend) args s = .val (value, t)) :
    stateOk t ∧ bvOk t.refs value ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  simp only [doApp] at run
  cases h : BvlSem.applyBlock .listAppend args s with
  | none => simp [h] at run
  | some pair =>
    cases pair with
    | mk result next =>
      simp only [h, Flapjack.SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      unfold BvlSem.applyBlock at h
      repeat' first | split at h | contradiction
      all_goals simp_all [bvOkList]
      simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨xs, hxs, ys, hys, rfl, rfl⟩ := h
      have xok := valueToList_ok s.refs _ xs argsOk.1 hxs
      have yok := valueToList_ok s.refs _ ys argsOk.2 hys
      refine ⟨ok, ?_, id⟩
      apply listToValue_ok
      intro item member
      rcases List.mem_append.mp member with inX | inY
      · exact (bvOkList_iff _ _).1 xok item inX
      · exact (bvOkList_iff _ _).1 yok item inY

/-- Conversion from a list value to a block preserves well-formedness. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok_fromList {C F : Type} (tag : Nat)
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (ok : stateOk s) (argsOk : bvOkList s.refs args)
    (run : doApp (.blockOp (.fromList tag)) args s = .val (value, t)) :
    stateOk t ∧ bvOk t.refs value ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  simp only [doApp] at run
  cases h : BvlSem.applyBlock (.fromList tag) args s with
  | none => simp [h] at run
  | some pair =>
    cases pair with
    | mk result next =>
      simp only [h, Flapjack.SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      unfold BvlSem.applyBlock at h
      repeat' first | split at h | contradiction
      all_goals simp_all [bvOkList]
      simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨values, decode, rfl, rfl⟩ := h
      exact ⟨ok, by simpa [bvOk] using valueToList_ok s.refs _ values argsOk decode, id⟩

/-- Block and reference-array element selection preserves well-formedness. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok_elemAt {C F : Type} (index : Nat)
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (ok : stateOk s) (argsOk : bvOkList s.refs args)
    (run : doApp (.blockOp (.elemAt index)) args s = .val (value, t)) :
    stateOk t ∧ bvOk t.refs value ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  simp only [doApp] at run
  cases h : BvlSem.applyBlock (.elemAt index) args s with
  | none => simp [h] at run
  | some pair =>
    cases pair with
    | mk result next =>
      simp only [h, Flapjack.SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      unfold BvlSem.applyBlock at h
      repeat' first | split at h | contradiction
      all_goals simp_all [bvOk, bvOkList]
      all_goals simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      all_goals obtain ⟨item, selected, rfl, rfl⟩ := h
      all_goals refine ⟨ok, ?_, id⟩
      all_goals first
        | exact (bvOkList_iff _ _).1 argsOk item (List.mem_of_getElem? selected)
        | (have member := List.mem_of_getElem? selected
           simp_all [stateOk, bvOkList_iff]
           grind)

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

import Flapjack.Compiler.Backend.BvlToBvi.Proofs.BlockOk

/-! Memory-operation well-formedness for BVL primitive application. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value Ref State doApp)

namespace MemoryCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end MemoryCarrier

/-- Replacing or allocating a value array containing well-formed values
preserves the source state invariant. -/
theorem stateOk_updateValueArray {C F : Type} (s : State C F) (key : Nat)
    (values : List Value) (ok : stateOk s) (valuesOk : bvOkList s.refs values) :
    stateOk { s with refs := s.refs.updateEq (key, .valueArray values) } := by
  let refs := s.refs.updateEq (key, .valueArray values)
  have subset : ∀ k, s.refs.lookup k ≠ none → refs.lookup k ≠ none := by
    intro k present
    exact BvlProps.refs_update_mono s.refs key k (.valueArray values) present
  constructor
  · intro item member
    have original := ok.1 item member
    cases item with
    | none => trivial
    | some value => exact bvOk_domain_mono s.refs value refs original subset
  · intro k
    by_cases eq : k = key
    · simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq, if_true]
      exact bvOkList_domain_mono s.refs values refs valuesOk subset
    · have prior := ok.2 k
      have lookup : refs.lookup k = s.refs.lookup k := by
        simp [refs, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq]
      rw [lookup]
      cases h : s.refs.lookup k with
      | none => trivial
      | some ref =>
        cases ref with
        | valueArray values =>
          simp only [h] at prior
          exact bvOkList_domain_mono s.refs values refs prior subset
        | thunk _ value =>
          simp only [h] at prior
          exact bvOk_domain_mono s.refs value refs prior subset
        | _ => trivial

/-- Reference allocation preserves well-formedness of the state, its new
pointer, and all previously valid environment values. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok_ref {C F : Type}
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (ok : stateOk s) (argsOk : bvOkList s.refs args)
    (run : doApp (.memOp .ref) args s = .val (value, t)) :
    stateOk t ∧ bvOk t.refs value ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  have subset := BvlProps.doApp_refs_mono (.memOp .ref) args s t value run
  have preserve := fun envOk => bvOkList_domain_mono s.refs env t.refs envOk subset
  simp only [doApp, BvlSem.applyMemory, Flapjack.SemanticPrimitivesHOL.Result.val.injEq,
    Prod.mk.injEq] at run
  rcases run with ⟨rfl, rfl⟩
  exact ⟨stateOk_updateValueArray s _ args ok argsOk,
    by simp [bvOk, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL], preserve⟩

/-- Replicated value-array allocation preserves primitive well-formedness. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok_refArray {C F : Type}
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (ok : stateOk s) (argsOk : bvOkList s.refs args)
    (run : doApp (.memOp .refArray) args s = .val (value, t)) :
    stateOk t ∧ bvOk t.refs value ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  have subset := BvlProps.doApp_refs_mono (.memOp .refArray) args s t value run
  have preserve := fun envOk => bvOkList_domain_mono s.refs env t.refs envOk subset
  have hval : BvlSem.applyMemory .refArray args s = some (value, t) := by
    simp only [doApp] at run
    cases h : BvlSem.applyMemory .refArray args s <;> simp_all
  unfold BvlSem.applyMemory at hval
  repeat' first | split at hval | contradiction
  all_goals simp_all [bvOk, bvOkList]
  rcases hval with ⟨rfl, rfl⟩
  constructor
  · apply stateOk_updateValueArray _ _ _ ok
    apply (bvOkList_iff _ _).2
    intro item member
    have eq := List.eq_of_mem_replicate member
    subst item
    exact argsOk
  · simp [bvOk, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- Updating an element of a value array preserves primitive well-formedness. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok_update {C F : Type}
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (ok : stateOk s) (argsOk : bvOkList s.refs args)
    (run : doApp (.memOp .update) args s = .val (value, t)) :
    stateOk t ∧ bvOk t.refs value ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  have subset := BvlProps.doApp_refs_mono (.memOp .update) args s t value run
  have preserve := fun envOk => bvOkList_domain_mono s.refs env t.refs envOk subset
  have hval : BvlSem.applyMemory .update args s = some (value, t) := by
    simp only [doApp] at run
    cases h : BvlSem.applyMemory .update args s <;> simp_all
  unfold BvlSem.applyMemory at hval
  repeat' first | split at hval | contradiction
  all_goals simp_all [bvOk, bvOkList, BvlSem.unitValue]
  rcases hval with ⟨rfl, rfl⟩
  constructor
  · apply stateOk_updateValueArray _ _ _ ok
    apply (bvOkList_iff _ _).2
    intro item member
    rcases List.mem_or_eq_of_mem_set member with old | fresh
    · simp_all [stateOk, bvOkList_iff]
      grind
    · subst item
      exact argsOk
  · simp [bvOk, bvOkList]

/-- Selecting a block or value-array element preserves well-formedness. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok_el {C F : Type}
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (ok : stateOk s) (argsOk : bvOkList s.refs args)
    (run : doApp (.memOp .el) args s = .val (value, t)) :
    stateOk t ∧ bvOk t.refs value ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  have hval : BvlSem.applyMemory .el args s = some (value, t) := by
    simp only [doApp] at run
    cases h : BvlSem.applyMemory .el args s <;> simp_all
  unfold BvlSem.applyMemory at hval
  repeat' first | split at hval | contradiction
  all_goals simp_all [bvOk, bvOkList]
  all_goals simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hval
  all_goals obtain ⟨item, selected, rfl, rfl⟩ := hval
  all_goals refine ⟨ok, ?_, id⟩
  all_goals first
    | exact (bvOkList_iff _ _).1 argsOk item (List.mem_of_getElem? selected)
    | (have member := List.mem_of_getElem? selected
       simp_all [stateOk, bvOkList_iff]
       grind)

/-- Complete memory-operation case of primitive application. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok_memory {C F : Type} (op : ClosLang.MemOp)
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (ok : stateOk s) (argsOk : bvOkList s.refs args)
    (run : doApp (.memOp op) args s = .val (value, t)) :
    stateOk t ∧ bvOk t.refs value ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  have subset := BvlProps.doApp_refs_mono (.memOp op) args s t value run
  have preserve := fun envOk => bvOkList_domain_mono s.refs env t.refs envOk subset
  have hval : BvlSem.applyMemory op args s = some (value, t) := by
    simp only [doApp] at run
    cases h : BvlSem.applyMemory op args s <;> simp_all
  cases op with
  | ref => exact doApp_ok_ref args env s t value ok argsOk run
  | refArray => exact doApp_ok_refArray args env s t value ok argsOk run
  | update => exact doApp_ok_update args env s t value ok argsOk run
  | el => exact doApp_ok_el args env s t value ok argsOk run
  | _ =>
    unfold BvlSem.applyMemory at hval
    repeat' first | split at hval | contradiction
    all_goals simp_all [bvOk, bvOkList, BvlSem.boolValue, BvlSem.unitValue]
    all_goals try (rcases hval with ⟨rfl, _⟩; simp [bvOk, bvOkList])
    all_goals try (rcases hval with ⟨rfl, _⟩; apply listToValue_ok; simp [bvOk])
    all_goals try simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hval
    all_goals repeat' first
      | (rcases hval with ⟨rfl, rfl⟩
         constructor
         · first | exact stateOk_updateByteArray s _ _ _ ok | exact ok
         · simp [bvOk, bvOkList, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
      | (obtain ⟨_, _, hval⟩ := hval
         try simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hval)
      | simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hval
      | split at hval

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveArray

/-! Global-variable primitives for the proof-side flat pattern simulation.
The evaluator and relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Appending pointwise related lists preserves their relation. -/
theorem forall₂_append_lists {A B : Type} {R : A → B → Prop} {xs : List A} {ys : List B}
    (related : List.Forall₂ R xs ys) {xs' : List A} {ys' : List B} (related' : List.Forall₂ R xs' ys') :
    List.Forall₂ R (xs ++ xs') (ys ++ ys') := by
  induction related with
  | nil => exact related'
  | cons head _ ih => exact .cons head ih

/-- Global allocation preserves the corresponding uninitialized slots. -/
theorem doApp_globalAlloc_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (count : Nat) (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.globalVarAlloc count) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.globalVarAlloc count) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
  | nil =>
    simp [FlatSem.doApp, FlatSem.doAppFlat] at run
    rcases run with ⟨rfl, rfl⟩
    refine ⟨{ target with globals := target.globals ++ List.replicate count none }, .val FlatSem.unitValue, ?_, ?_, .value ?_⟩
    · simp [FlatSem.doApp, FlatSem.doAppFlat]
    · refine ⟨states.1, states.2.1, states.2.2.1, ?_, states.2.2.2.2⟩
      exact forall₂_append_lists states.2.2.2.1 (forall₂_replicate count (show optionRel ValueRel none none from trivial))
    · exact (valueRel_conv none [] _).2 ⟨[], rfl, .nil⟩

/-- Initializing an uninitialized global preserves related values and states. -/
theorem doApp_globalInit_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (index : Nat) (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.globalVarInit index) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.globalVarInit index) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
  | @cons value value' tail tail' values rest =>
    cases rest with
    | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
    | nil =>
      cases found : source.globals[index]? with
      | none => simp [FlatSem.doApp, FlatSem.doAppFlat, found] at run
      | some slot =>
        cases slot with
        | some _ => simp [FlatSem.doApp, FlatSem.doAppFlat, found] at run
        | none =>
          obtain ⟨slot', found', slotRel⟩ := forall₂_getElem_some states.2.2.2.1 index none found
          cases slot' with
          | some _ => simp [optionRel] at slotRel
          | none =>
            simp [FlatSem.doApp, FlatSem.doAppFlat, found] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨{ target with globals := target.globals.set index (some value') }, .val FlatSem.unitValue, ?_, ?_, .value ?_⟩
            · simp [FlatSem.doApp, FlatSem.doAppFlat, found']
            · exact ⟨states.1, states.2.1, states.2.2.1,
                forall₂_set states.2.2.2.1 index (show optionRel ValueRel (some value) (some value') from values), states.2.2.2.2⟩
            · exact (valueRel_conv none [] _).2 ⟨[], rfl, .nil⟩

/-- A successful global lookup finds a related value in the target state. -/
theorem doApp_globalLookup_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (index : Nat) (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.globalVarLookup index) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.globalVarLookup index) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
  | nil =>
    cases found : source.globals[index]? with
    | none => simp [FlatSem.doApp, FlatSem.doAppFlat, found] at run
    | some slot =>
      cases slot with
      | none => simp [FlatSem.doApp, FlatSem.doAppFlat, found] at run
      | some value =>
        obtain ⟨slot', found', slotRel⟩ := forall₂_getElem_some states.2.2.2.1 index (some value) found
        cases slot' with
        | none => simp [optionRel] at slotRel
        | some value' =>
          simp [FlatSem.doApp, FlatSem.doAppFlat, found] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨target, .val value', by simp [FlatSem.doApp, FlatSem.doAppFlat, found'], states, .value slotRel⟩

/-- The flat identity primitive returns related values. -/
theorem doApp_id_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source .id values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target .id values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
  | @cons value value' tail tail' values rest =>
    cases rest with
    | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
    | nil =>
      simp [FlatSem.doApp, FlatSem.doAppFlat] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨target, .val value', by simp [FlatSem.doApp, FlatSem.doAppFlat], states, .value values⟩

/-- Flat constructor-length tests agree on related arguments. -/
theorem doApp_lenEq_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (length : Nat) (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.lenEq length) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.lenEq length) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
  | @cons value value' tail tail' head rest =>
    cases rest with
    | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
    | nil =>
      cases value with
      | conv tag fields =>
        obtain ⟨fields', rfl, fieldsRel⟩ := (valueRel_conv tag fields value').1 head
        have lengths := forall₂_length fieldsRel
        simp [FlatSem.doApp, FlatSem.doAppFlat] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨target, .val (FlatSem.boolValue (fields.length == length)), ?_, states, .value ?_⟩
        · simp [FlatSem.doApp, FlatSem.doAppFlat, ← lengths]
        · cases fields.length == length <;> simp [FlatSem.boolValue] <;>
            exact (valueRel_conv _ [] _).2 ⟨[], rfl, .nil⟩
      | litv _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
        simp [FlatSem.doApp, FlatSem.doAppFlat] at run

/-- Flat constructor-tag and length tests agree on related arguments. -/
theorem doApp_tagLenEq_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (tag length : Nat) (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.tagLenEq tag length) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.tagLenEq tag length) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
  | @cons value value' tail tail' head rest =>
    cases rest with
    | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
    | nil =>
      cases value with
      | conv stamp fields =>
        cases stamp with
        | none => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
        | some pair =>
          obtain ⟨actual, typeId⟩ := pair
          obtain ⟨fields', rfl, fieldsRel⟩ := (valueRel_conv (some (actual, typeId)) fields value').1 head
          have lengths := forall₂_length fieldsRel
          simp [FlatSem.doApp, FlatSem.doAppFlat] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨target, .val (FlatSem.boolValue (actual == tag && fields.length == length)), ?_, states, .value ?_⟩
          · simp [FlatSem.doApp, FlatSem.doAppFlat, ← lengths]
          · cases (actual == tag && fields.length == length) <;> simp [FlatSem.boolValue] <;>
              exact (valueRel_conv _ [] _).2 ⟨[], rfl, .nil⟩
      | litv _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
        simp [FlatSem.doApp, FlatSem.doAppFlat] at run

/-- Flat field and reference projections return related values. -/
theorem doApp_el_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (index : Nat) (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.el index) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.el index) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
  | @cons value value' tail tail' head rest =>
    cases rest with
    | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
    | nil =>
      cases value with
      | conv tag fields =>
        obtain ⟨fields', rfl, fieldsRel⟩ := (valueRel_conv tag fields value').1 head
        cases found : fields[index]? with
        | none => simp [FlatSem.doApp, FlatSem.doAppFlat, found] at run
        | some field =>
          simp [FlatSem.doApp, FlatSem.doAppFlat, found] at run
          rcases run with ⟨rfl, rfl⟩
          obtain ⟨field', found', fieldRel⟩ := forall₂_getElem_some fieldsRel index field found
          exact ⟨target, .val field', by simp [FlatSem.doApp, FlatSem.doAppFlat, found'], states, .value fieldRel⟩
      | loc flag address =>
        have eq := (valueRel_loc flag address value').1 head
        subst value'
        cases index with
        | succ _ => simp [FlatSem.doApp, FlatSem.doAppFlat] at run
        | zero =>
          cases found : Flapjack.SemanticPrimitivesHOL.storeLookup address source.refs with
          | none => simp [FlatSem.doApp, FlatSem.doAppFlat, found] at run
          | some entry =>
            cases entry with
            | refv field =>
              simp [FlatSem.doApp, FlatSem.doAppFlat, found] at run
              rcases run with ⟨rfl, rfl⟩
              obtain ⟨field', found', fieldRel⟩ := stateRel_lookup_ref cfg source target states address field found
              exact ⟨target, .val field', by simp [FlatSem.doApp, FlatSem.doAppFlat, found'], states, .value fieldRel⟩
            | w8array _ | varray _ | thunk _ _ => simp [FlatSem.doApp, FlatSem.doAppFlat, found] at run
      | litv _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
        simp [FlatSem.doApp, FlatSem.doAppFlat] at run

/-- Every flat-specific primitive operation preserves the proof-side state and
result relations whenever source primitive application succeeds. -/
theorem doApp_flat_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (op : FlatLang.Op) (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (notSource : ∀ sourceOp, op ≠ .src sourceOp)
    (run : FlatSem.doApp source op values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target op values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases op with
  | src sourceOp => exact (notSource sourceOp rfl).elim
  | globalVarAlloc count => exact doApp_globalAlloc_related cfg source target sourceFinal count values values' result states related run
  | globalVarInit index => exact doApp_globalInit_related cfg source target sourceFinal index values values' result states related run
  | globalVarLookup index => exact doApp_globalLookup_related cfg source target sourceFinal index values values' result states related run
  | id => exact doApp_id_related cfg source target sourceFinal values values' result states related run
  | lenEq length => exact doApp_lenEq_related cfg source target sourceFinal length values values' result states related run
  | tagLenEq tag length => exact doApp_tagLenEq_related cfg source target sourceFinal tag length values values' result states related run
  | el index => exact doApp_el_related cfg source target sourceFinal index values values' result states related run

end Flapjack.Compiler.Backend.FlatPattern

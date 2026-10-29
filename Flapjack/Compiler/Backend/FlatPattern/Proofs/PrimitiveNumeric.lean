import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveArray

/-! Numeric primitives for the proof-side flat pattern simulation. The
evaluator and relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Flat Boolean values are related to themselves. -/
theorem boolValue_related (value : Bool) : ValueRel (FlatSem.boolValue value) (FlatSem.boolValue value) := by
  cases value <;> exact (valueRel_conv _ [] _).2 ⟨[], rfl, .nil⟩

/-- Projection to source primitives is identical on related flat values. -/
theorem flatToValue_related (value value' : FlatSem.Value) (related : ValueRel value value') :
    FlatSem.flatToValue value = FlatSem.flatToValue value' := by
  cases value with
  | litv lit =>
    have eq := (valueRel_lit lit value').1 related
    subst value'
    rfl
  | loc flag index =>
    have eq := (valueRel_loc flag index value').1 related
    subst value'
    rfl
  | conv stamp fields =>
    obtain ⟨fields', rfl, contents⟩ := (valueRel_conv stamp fields value').1 related
    cases fields with
    | nil =>
      cases contents
      rfl
    | cons first rest =>
      cases contents
      cases stamp with
      | none => rfl
      | some pair =>
        obtain ⟨tag, typeId⟩ := pair
        cases typeId <;> rfl
  | vectorv fields =>
    obtain ⟨fields', rfl, _⟩ := (valueRel_vector fields value').1 related
    rfl
  | closure env name body =>
    obtain ⟨_, _, _, _, _, rfl⟩ := (valueRel_closure env name body value').1 related
    rfl
  | recclosure env funs name =>
    obtain ⟨_, _, _, _, _, rfl⟩ := (valueRel_recclosure env funs name value').1 related
    rfl

/-- The values produced by the source-to-flat primitive projection are
related to themselves, including its default and Boolean cases. -/
theorem valueToFlat_related (value : SemanticPrimitivesHOL.Value) :
    ValueRel (FlatSem.valueToFlat value) (FlatSem.valueToFlat value) := by
  cases value with
  | litv lit => exact (valueRel_lit lit _).2 rfl
  | conv stamp fields =>
    cases stamp with
    | none => exact (valueRel_vector [] _).2 ⟨[], rfl, .nil⟩
    | some stamp =>
      cases stamp with
      | typeStamp name number =>
        cases number with
        | zero =>
          cases fields with
          | nil =>
            simp only [FlatSem.valueToFlat]
            split
            · exact boolValue_related true
            · split
              · exact boolValue_related false
              · exact (valueRel_vector [] _).2 ⟨[], rfl, .nil⟩
          | cons _ _ => exact (valueRel_vector [] _).2 ⟨[], rfl, .nil⟩
        | succ _ => exact (valueRel_vector [] _).2 ⟨[], rfl, .nil⟩
      | exnStamp _ => exact (valueRel_vector [] _).2 ⟨[], rfl, .nil⟩
  | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ | env _ =>
    exact (valueRel_vector [] _).2 ⟨[], rfl, .nil⟩

/-- The mapped primitive argument lists are equal for related flat values. -/
theorem flatToValue_map_related {values values' : List FlatSem.Value} (related : List.Forall₂ ValueRel values values') :
    values.map FlatSem.flatToValue = values'.map FlatSem.flatToValue := by
  induction related with
  | nil => rfl
  | cons head _ ih => simp [flatToValue_related _ _ head, ih]

/-- The numeric projection preserves successful results, raised exceptions,
and aborts across related states and argument lists. -/
theorem applyNumericProjection_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (op : Op) (values values' : List FlatSem.Value) (errorValue : FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (states : StateRel cfg source target)
    (related : List.Forall₂ ValueRel values values') (errorRel : ValueRel errorValue errorValue)
    (run : FlatSem.applyNumericProjection source op values errorValue = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.applyNumericProjection target op values' errorValue = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  have arguments := flatToValue_map_related related
  have ffi := states.2.2.1
  cases called : SemanticPrimitivesHOL.doApp ([], source.ffi) op (values.map FlatSem.flatToValue) with
  | none => simp [FlatSem.applyNumericProjection, called] at run
  | some output =>
    obtain ⟨ignored, output⟩ := output
    cases output with
    | val value =>
      simp [FlatSem.applyNumericProjection, called] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨target, .val (FlatSem.valueToFlat value), ?_, states, .value (valueToFlat_related value)⟩
      simp [FlatSem.applyNumericProjection, ffi, ← arguments, called]
    | err error =>
      cases error with
      | raise raised =>
        simp [FlatSem.applyNumericProjection, called] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨target, .err (.raise errorValue), ?_, states, .error (.raise errorRel)⟩
        simp [FlatSem.applyNumericProjection, ffi, ← arguments, called]
      | abort abort =>
        simp [FlatSem.applyNumericProjection, called] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨target, .err (.abort abort), ?_, states, .error (.abort abort)⟩
        simp [FlatSem.applyNumericProjection, ffi, ← arguments, called]

/-- Arithmetic application preserves related states and results. -/
theorem doApp_arith_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (action : Arith) (typ : PrimType) (values values' : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (states : StateRel cfg source target)
    (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src (.arith action typ)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src (.arith action typ)) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  have run' : FlatSem.applyNumericProjection source (.arith action typ) values FlatSem.divExnV = some (sourceFinal, result) := by
    simpa [FlatSem.doApp, FlatSem.doAppNumeric] using run
  obtain ⟨targetFinal, result', targetRun, finalStates, resultRel⟩ :=
    applyNumericProjection_related cfg source target sourceFinal (.arith action typ) values values' FlatSem.divExnV result
      states related ((valueRel_conv _ [] _).2 ⟨[], rfl, .nil⟩) run'
  exact ⟨targetFinal, result', by simpa [FlatSem.doApp, FlatSem.doAppNumeric] using targetRun, finalStates, resultRel⟩

/-- Primitive conversions preserve related states and results. -/
theorem doApp_fromTo_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (sourceTyp targetTyp : PrimType) (values values' : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (states : StateRel cfg source target)
    (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src (.fromTo sourceTyp targetTyp)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src (.fromTo sourceTyp targetTyp)) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  have run' : FlatSem.applyNumericProjection source (.fromTo sourceTyp targetTyp) values FlatSem.chrExnV = some (sourceFinal, result) := by
    simpa [FlatSem.doApp, FlatSem.doAppNumeric] using run
  obtain ⟨targetFinal, result', targetRun, finalStates, resultRel⟩ :=
    applyNumericProjection_related cfg source target sourceFinal (.fromTo sourceTyp targetTyp) values values' FlatSem.chrExnV result
      states related ((valueRel_conv _ [] _).2 ⟨[], rfl, .nil⟩) run'
  exact ⟨targetFinal, result', by simpa [FlatSem.doApp, FlatSem.doAppNumeric] using targetRun, finalStates, resultRel⟩

/-- Word shifts preserve related states and results. -/
theorem doApp_shift_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (width : WordSize) (shift : Shift) (amount : Nat) (values values' : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (states : StateRel cfg source target)
    (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src (.shift width shift amount)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src (.shift width shift amount)) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  have run' : FlatSem.applyNumericProjection source (.shift width shift amount) values FlatSem.divExnV = some (sourceFinal, result) := by
    simpa [FlatSem.doApp, FlatSem.doAppNumeric] using run
  obtain ⟨targetFinal, result', targetRun, finalStates, resultRel⟩ :=
    applyNumericProjection_related cfg source target sourceFinal (.shift width shift amount) values values' FlatSem.divExnV result
      states related ((valueRel_conv _ [] _).2 ⟨[], rfl, .nil⟩) run'
  exact ⟨targetFinal, result', by simpa [FlatSem.doApp, FlatSem.doAppNumeric] using targetRun, finalStates, resultRel⟩

end Flapjack.Compiler.Backend.FlatPattern

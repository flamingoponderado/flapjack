import Flapjack.Compiler.Backend.FlatToClos.Proofs.Thunk
import Flapjack.Compiler.Backend.FlatToClos.Proofs.MemoryExpressions

/-! Thunk primitive simulations using the proof-side state and value relations.
These are infrastructure lemmas, not reviewed HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- Allocating related thunk payloads preserves the corresponding stores. -/
theorem storeRel_allocThunk (refs : Store FlatSem.Value)
    (targetRefs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value)) (mode : ThunkMode)
    (value : FlatSem.Value) (targetValue : ClosSem.Value)
    (stores : StoreRel refs targetRefs) (related : ValueRel value targetValue) :
    StoreRel (refs ++ [.thunk mode value])
      (targetRefs.updateEq (refs.length, .thunk mode targetValue)) := by
  intro index
  have original := stores index
  by_cases same : index = refs.length
  · subst index
    simp [HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL, related]
  · have different : refs.length ≠ index := Ne.symm same
    by_cases bound : index < refs.length
    · simpa [List.getElem?_append, bound, HolFiniteMapExact.lookup_updateEq,
        Flapjack.FUPDATE_HOL, same, different] using original
    · have past : refs.length + 1 ≤ index := by omega
      have originalNone : refs[index]? = none := List.getElem?_eq_none (by omega)
      have originalFree : targetRefs.lookup index = none := by simpa [originalNone] using original
      simpa [List.getElem?_append, bound, past, HolFiniteMapExact.lookup_updateEq,
        Flapjack.FUPDATE_HOL, same, different] using originalFree

/-- Thunk allocation requires a single argument. -/
theorem allocThunk_wrong_arity {C F : Type} (state : FlatSem.State C F) (mode : ThunkMode)
    (args : List FlatSem.Value) (wrong : args.length ≠ 1) :
    (FlatSem.applyResult state (.src (.thunkOp (.allocThunk mode))) args).2 =
      .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]
  | cons first rest =>
    cases rest with
    | nil => simp at wrong
    | cons second rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]

/-- Thunk allocation simulates arbitrary argument evaluation, rejecting
invalid evaluated-thunk payloads and allocating related fresh stores. -/
theorem evaluate_allocThunk {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (mode : ThunkMode) (args : List FlatLang.Exp)
    (argSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.thunkOp (.allocThunk mode))) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.thunkOp (.allocThunk mode))) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argSim := argSim argsNotTypeError
  unfold EvalSim at argSim ⊢
  simp only [compile, compileExps_reverse] at argSim
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  rw [FlatSem.evaluate, ClosSem.evaluate, closFix]
  simp only [flatFix]
  cases flatRun : FlatSem.evaluate env source args.reverse with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate (compileExps names args).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argSim ⊢
      rcases argSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        rename_i sourceArgs targetArgs
        have resultShape : (FlatSem.applyResult next (.src (.thunkOp (.allocThunk mode))) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 1 := by
          by_contra wrong
          apply resultShape
          apply allocThunk_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | cons _ _ => simp at length
          | nil =>
            rename_i sourceValue targetValue
            have safe : FlatSem.badThunkUpdate mode sourceValue next.refs = false := by
              cases h : FlatSem.badThunkUpdate mode sourceValue next.refs <;>
                simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                  FlatSem.doAppData, h] at resultShape ⊢
            have targetSafe := badThunkUpdate_related mode sourceValue targetValue next.refs nextTarget.refs
              head states.2.2.2.1
            rw [safe] at targetSafe
            have index := leastUnusedRef_eq_length next.refs nextTarget.refs states.2.2.2.1
            have stores := storeRel_allocThunk next.refs nextTarget.refs mode sourceValue targetValue states.2.2.2.1 head
            have updated : StateRel { next with refs := next.refs ++ [.thunk mode sourceValue] }
                { nextTarget with refs := nextTarget.refs.updateEq (next.refs.length, .thunk mode targetValue) } := by
              rcases states with ⟨maxApp, ffi, clock, _, globals, globalValues, install⟩
              exact ⟨maxApp, ffi, clock, stores, globals, globalValues, install⟩
            simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
              FlatSem.doAppData, safe, storeAlloc, ClosSem.doApp, ← targetSafe, index, updated,
              EvalResultRel.value (.cons (ValueRel.loc false next.refs.length) .nil)]

/-- Updating a related unevaluated thunk with related payloads preserves
the stores, irrespective of the new thunk mode. -/
theorem updateThunkOp_related {C F : Type} (source : FlatSem.State C F)
    (target : ClosSem.State C F) (index : Nat) (old value : FlatSem.Value)
    (targetValue : ClosSem.Value) (mode : ThunkMode) (states : StateRel source target)
    (related : ValueRel value targetValue)
    (found : source.refs[index]? = some (.thunk .notEvaluated old))
    (safe : FlatSem.badThunkUpdate mode value source.refs = false) :
    ∃ targetNext,
      FlatSem.doAppData source (.thunkOp (.updateThunk mode)) [.loc false index, value] =
        some (some ({ source with refs := source.refs.set index (.thunk mode value) }, .val FlatSem.unitValue)) ∧
      ClosSem.doApp (.thunkOp (.updateThunk mode)) [.refPtr false index, targetValue] target =
        .val (ClosSem.unitValue, targetNext) ∧
      StateRel { source with refs := source.refs.set index (.thunk mode value) } targetNext := by
  have slot := states.2.2.2.1 index
  simp only [found] at slot
  obtain ⟨oldTarget, targetFound, _⟩ := slot
  have targetSafe := badThunkUpdate_related mode value targetValue source.refs target.refs related states.2.2.2.1
  rw [safe] at targetSafe
  have newStores := storeRel_setThunk source.refs target.refs index _ mode value targetValue states.2.2.2.1 found related
  refine ⟨{ target with refs := target.refs.updateEq (index, .thunk mode targetValue) }, ?_, ?_, ?_⟩
  · simp [FlatSem.doAppData, safe, storeAssign, found, storeValueSameType]
  · simp [ClosSem.doApp, ← targetSafe, targetFound]
  · rcases states with ⟨maxApp, ffi, clock, _, globals, values, install⟩
    exact ⟨maxApp, ffi, clock, newStores, globals, values, install⟩

/-- Thunk updates require exactly two arguments. -/
theorem updateThunk_wrong_arity {C F : Type} (state : FlatSem.State C F) (mode : ThunkMode)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src (.thunkOp (.updateThunk mode))) args).2 =
      .err (.abort .typeError) := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  all_goals simp_all [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
    FlatSem.doAppMemory, FlatSem.doAppData]

/-- A thunk update expression is simulated whenever source
evaluation does not abort with a type error. -/
theorem evaluate_updateThunk {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (mode : ThunkMode) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.thunkOp (.updateThunk mode))) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.thunkOp (.updateThunk mode))) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  simp only [compile, compileExps_reverse] at argsSim
  rw [FlatSem.evaluate, ClosSem.evaluate, closFix]
  simp only [flatFix]
  cases flatRun : FlatSem.evaluate env source args.reverse with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate (compileExps names args).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argsSim ⊢
      rcases argsSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        rename_i sourceArgs targetArgs
        have resultShape : (FlatSem.applyResult next (.src (.thunkOp (.updateThunk mode))) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have argLength : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply updateThunk_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at argLength
        | cons valueRel tail =>
          cases tail with
          | nil => simp at argLength
          | cons pointerRel tail =>
            cases tail with
            | cons _ _ => simp at argLength
            | nil =>
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at resultShape
              cases pointerRel <;>
                simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
                  FlatSem.doAppMemory, FlatSem.doAppData] at resultShape
              case loc flag pointer =>
                cases flag with
                | true => simp at resultShape
                | false =>
                  rename_i sourceValue targetValue
                  have safe : FlatSem.badThunkUpdate mode sourceValue next.refs = false := by
                    cases h : FlatSem.badThunkUpdate mode sourceValue next.refs <;>
                      simp [h] at resultShape ⊢
                  cases found : next.refs[pointer]? with
                  | none => simp [safe, storeAssign, found] at resultShape
                  | some entry =>
                    cases entry with
                    | refv _ | w8array _ | varray _ =>
                      simp [safe, storeAssign, found, storeValueSameType] at resultShape
                    | thunk oldMode old =>
                      cases oldMode with
                      | evaluated => simp [safe, storeAssign, found, storeValueSameType] at resultShape
                      | notEvaluated =>
                        obtain ⟨targetUpdated, sourceUpdate, targetUpdate, updatedStates⟩ :=
                          updateThunkOp_related next nextTarget pointer old sourceValue targetValue mode states valueRel found safe
                        simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                          sourceUpdate, targetUpdate, updatedStates, FlatSem.unitValue, ClosSem.unitValue,
                          EvalResultRel.value (.cons (ValueRel.tuple .nil) .nil)]

end Flapjack.Compiler.Backend.FlatToClos

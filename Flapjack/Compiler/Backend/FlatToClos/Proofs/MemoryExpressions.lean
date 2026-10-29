import Flapjack.Compiler.Backend.FlatToClos.Proofs.Memory
import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases

/-! Reference-expression cases for the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- A reference allocation with the wrong arity fails with a source type error. -/
theorem ref_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 1) :
    (FlatSem.applyResult state (.src .opref) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]
  | cons first rest =>
    cases rest with
    | nil => simp at wrong
    | cons second rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]

/-- Reference allocation creates related source and closure stores, with the
source type-error exclusion used by the correctness theorem. -/
theorem evaluate_ref {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .opref) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .opref) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src .opref) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 1 := by
          by_contra wrong
          apply resultShape
          apply ref_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | cons _ _ => simp at length
          | nil =>
            rename_i sourceValue targetValue
            have index := leastUnusedRef_eq_length next.refs nextTarget.refs states.2.2.2.1
            have updated := stateRel_allocRef next nextTarget sourceValue targetValue states head
            simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
              storeAlloc, ClosSem.doApp, ClosSem.applyMemory, index, updated,
              EvalResultRel.value (.cons (ValueRel.loc true next.refs.length) .nil)]

/-- Byte-array length rejects any argument count other than one. -/
theorem byteArrayLength_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 1) :
    (FlatSem.applyResult state (.src .aw8length) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]
  | cons first rest =>
    cases rest with
    | nil => simp at wrong
    | cons second rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]

/-- Reading the length of a byte array gives the same integer on both sides,
including the argument-evaluation error cases. -/
theorem evaluate_byteArrayLength {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .aw8length) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .aw8length) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src .aw8length) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 1 := by
          by_contra wrong
          apply resultShape
          apply byteArrayLength_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | cons _ _ => simp at length
          | nil =>
            simp only [List.reverse_singleton] at resultShape
            cases head <;> simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
              FlatSem.doAppMemory] at resultShape
            case loc flag index =>
              cases found : storeLookup index next.refs with
              | none => simp [found] at resultShape
              | some stored =>
                cases stored <;> simp [found] at resultShape
                case w8array bytes =>
                  have targetFound := lookup_byteArray states found
                  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                    found, ClosSem.doApp, ClosSem.applyMemory, targetFound, states,
                    EvalResultRel.value (.cons (ValueRel.int _) .nil)]

/-- Value-array length rejects any argument count other than one. -/
theorem arrayLength_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 1) :
    (FlatSem.applyResult state (.src .alength) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]
  | cons first rest =>
    cases rest with
    | nil => simp at wrong
    | cons second rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]

/-- Related value arrays have the same length after evaluating arbitrary
argument lists, provided the source application avoids a type error. -/
theorem evaluate_arrayLength {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .alength) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .alength) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src .alength) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 1 := by
          by_contra wrong
          apply resultShape
          apply arrayLength_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | cons _ _ => simp at length
          | nil =>
            simp only [List.reverse_singleton] at resultShape
            cases head <;> simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
              FlatSem.doAppMemory] at resultShape
            case loc flag index =>
              cases found : storeLookup index next.refs with
              | none => simp [found] at resultShape
              | some stored =>
                cases stored <;> simp [found] at resultShape
                case varray items =>
                  obtain ⟨targetItems, targetFound, itemRel⟩ := lookup_array states found
                  have sameLength := itemRel.length_eq
                  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                    found, ClosSem.doApp, ClosSem.applyMemory, targetFound, ← sameLength, states,
                    EvalResultRel.value (.cons (ValueRel.int _) .nil)]

end Flapjack.Compiler.Backend.FlatToClos

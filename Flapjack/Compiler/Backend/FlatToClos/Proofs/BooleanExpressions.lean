import Flapjack.Compiler.Backend.FlatToClos.Proofs.IntegerExpressions

/-! Boolean arithmetic for the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- Boolean negation rejects any argument count other than one. -/
theorem boolNot_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 1) :
    (FlatSem.applyResult state (.src (.arith .not .boolT)) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp at wrong
    | cons second rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- Boolean negation gives related Boolean values,
including the argument-evaluation error cases. -/
theorem evaluate_boolNot {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith .not .boolT)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith .not .boolT)) args] := by
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
  simp only [compile, compileExps, compileExp, compileOp, compileArith] at ⊢
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
        have resultShape : (FlatSem.applyResult next (.src (.arith .not .boolT)) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 1 := by
          by_contra wrong
          apply resultShape
          apply boolNot_wrong_arity next
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | cons _ _ => simp at length
          | nil =>
            simp only [List.reverse_singleton] at resultShape
            cases head <;> simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
              FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp,
              SemanticPrimitivesHOL.doAppNumericCore] at resultShape
            case con rel =>
              rename_i sourceFields targetFields tag typeId
              cases rel with
              | nil =>
                cases typeId <;> simp_all [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
                  FlatSem.applyNumericProjection, FlatSem.flatToValue, FlatSem.valueToFlat,
                  SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore,
                  SemanticPrimitivesHOL.boolValue, SemanticPrimitivesHOL.checkType,
                  ClosSem.doApp, ClosSem.applyBlock, ClosSem.asBool,
                  BackendCommon.trueTag, BackendCommon.falseTag, FlatLang.boolId]
                all_goals split_ifs at resultShape <;> simp_all
                all_goals simp_all [SemanticPrimitivesHOL.boolTypeNum, FlatSem.boolValue,
                  ClosSem.boolValue, ofString, BackendCommon.boolToTag]
                all_goals exact .value (.cons (.con .nil) .nil)
              | cons _ _ => simp_all

/-- A rejected fallback arithmetic operation simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_rejectedArithFallback {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (action : Arith) (typ : PrimType)
    (compiled : ∀ xs, compileArith trace action typ xs = .let .none xs (.var .none 0))
    (rejects : ∀ (state : FlatSem.State C F) args,
      (FlatSem.applyResult state (.src (.arith action typ)) args).2 = .err (.abort .typeError))
    (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith action typ)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith action typ)) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compileExp, compileOp, compiled] at ⊢
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
        have resultShape : (FlatSem.applyResult next (.src (.arith action typ)) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        exact False.elim (resultShape (rejects next sourceArgs.reverse))

/-- Character and string arithmetic always fails after argument evaluation. -/
theorem nonNumericArith_rejects {C F : Type} (state : FlatSem.State C F) (action : Arith)
    (typ : PrimType) (invalid : typ = .charT ∨ typ = .strT) (args : List FlatSem.Value) :
    (FlatSem.applyResult state (.src (.arith action typ)) args).2 = .err (.abort .typeError) := by
  rcases invalid with rfl | rfl <;>
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
      SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- Character and string arithmetic preserve prior argument errors. -/
theorem evaluate_nonNumericArith {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (action : Arith) (typ : PrimType)
    (invalid : typ = .charT ∨ typ = .strT) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith action typ)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith action typ)) args] := by
  apply evaluate_rejectedArithFallback env names values source target trace action typ
  · intro xs
    rcases invalid with rfl | rfl <;> rfl
  · intro state values
    exact nonNumericArith_rejects state action typ invalid values
  · exact argsSim
  · exact notTypeError

end Flapjack.Compiler.Backend.FlatToClos

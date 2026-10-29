import Flapjack.Compiler.Backend.FlatToClos.Proofs.IntegerOperations
import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases

/-! Integer-expression cases for flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- Integer addition rejects any argument count other than two. -/
theorem intAdd_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src (.arith .add .intT)) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- Integer addition simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_intAdd {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith .add .intT)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith .add .intT)) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compileExp, compileOp, compileArith] at ⊢
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
        have resultShape : (FlatSem.applyResult next (.src (.arith .add .intT)) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply intAdd_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons indexRel tail =>
          cases tail with
          | nil => simp at length
          | cons pointerRel tail =>
            cases tail with
            | cons _ _ => simp at length
            | nil =>
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at resultShape
              cases pointerRel <;> simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
                FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore] at resultShape
              case con rel =>
                rename_i sourceFields targetFields tag typeId
                cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
                split_ifs at resultShape <;> simp_all
              case int _ =>
                cases indexRel <;> try (simp_all)
                case con rel =>
                  rename_i sourceFields targetFields tag typeId
                  cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
                  split_ifs at resultShape <;> simp_all
                case int _ =>
                  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
                    FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
                    SemanticPrimitivesHOL.doAppNumericCore, ClosSem.doApp, ClosSem.applyNumeric,
                    ClosSem.doIntApp, states, EvalResultRel.value (.cons (ValueRel.int _) .nil)]


/-- Integer subtraction rejects any argument count other than two. -/
theorem intSub_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src (.arith .sub .intT)) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- Integer subtraction simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_intSub {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith .sub .intT)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith .sub .intT)) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compileExp, compileOp, compileArith] at ⊢
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
        have resultShape : (FlatSem.applyResult next (.src (.arith .sub .intT)) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply intSub_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons indexRel tail =>
          cases tail with
          | nil => simp at length
          | cons pointerRel tail =>
            cases tail with
            | cons _ _ => simp at length
            | nil =>
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at resultShape
              cases pointerRel <;> simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
                FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore] at resultShape
              case con rel =>
                rename_i sourceFields targetFields tag typeId
                cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
                split_ifs at resultShape <;> simp_all
              case int _ =>
                cases indexRel <;> try (simp_all)
                case con rel =>
                  rename_i sourceFields targetFields tag typeId
                  cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
                  split_ifs at resultShape <;> simp_all
                case int _ =>
                  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
                    FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
                    SemanticPrimitivesHOL.doAppNumericCore, ClosSem.doApp, ClosSem.applyNumeric,
                    ClosSem.doIntApp, states, EvalResultRel.value (.cons (ValueRel.int _) .nil)]


/-- Integer multiplication rejects any argument count other than two. -/
theorem intMul_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src (.arith .mul .intT)) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- Integer multiplication simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_intMul {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith .mul .intT)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith .mul .intT)) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compileExp, compileOp, compileArith] at ⊢
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
        have resultShape : (FlatSem.applyResult next (.src (.arith .mul .intT)) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply intMul_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons indexRel tail =>
          cases tail with
          | nil => simp at length
          | cons pointerRel tail =>
            cases tail with
            | cons _ _ => simp at length
            | nil =>
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at resultShape
              cases pointerRel <;> simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
                FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore] at resultShape
              case con rel =>
                rename_i sourceFields targetFields tag typeId
                cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
                split_ifs at resultShape <;> simp_all
              case int _ =>
                cases indexRel <;> try (simp_all)
                case con rel =>
                  rename_i sourceFields targetFields tag typeId
                  cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
                  split_ifs at resultShape <;> simp_all
                case int _ =>
                  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
                    FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
                    SemanticPrimitivesHOL.doAppNumericCore, ClosSem.doApp, ClosSem.applyNumeric,
                    ClosSem.doIntApp, states, EvalResultRel.value (.cons (ValueRel.int _) .nil)]

end Flapjack.Compiler.Backend.FlatToClos

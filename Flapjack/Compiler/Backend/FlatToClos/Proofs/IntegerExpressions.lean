import Flapjack.Compiler.Backend.FlatToClos.Proofs.IntegerOperations
import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases

/-! Integer-expression cases for flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- The emitted zero check and integer operation agree with flat division
and remainder, including the Div exception. -/
theorem intDivMod_body_related {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (action : Arith) (left right : Int)
    (states : StateRel source target) (supported : action = .div ∨ action = .mod) :
    let flat := FlatSem.applyResult source (.src (.arith action .intT)) [.litv (.intLit left), .litv (.intLit right)]
    let clos := ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.blockOp .equal) [.var trace 0, .op trace (.intOp (.const 0)) []])
        (.raise trace (.op trace (.blockOp (.cons 2)) []))
        (.op trace (.intOp (if action = .div then .div else .mod)) [.var trace 0, .var trace 1])]
      (.number right :: .number left :: env) target
    StateRel flat.1 clos.2 ∧ EvalResultRel flat.2 clos.1 := by
  rcases supported with rfl | rfl <;> by_cases zero : right = 0
  all_goals have flipped : (0 = right) ↔ right = 0 := eq_comm
  all_goals simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
    FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore,
    ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock, ClosSem.applyNumeric, ClosSem.doIntApp,
    ClosSem.doEq, ClosSem.boolValue, ClosSem.asBool, BackendCommon.trueTag, BackendCommon.falseTag, zero, flipped, states]
  all_goals first | exact .raise (.con .nil) | exact .value (.cons (.int _) .nil)

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


/-- Integer division rejects any argument count other than two. -/
theorem intDiv_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src (.arith .div .intT)) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- Integer division simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_intDiv {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith .div .intT)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith .div .intT)) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src (.arith .div .intT)) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply intDiv_wrong_arity
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
              case int left =>
                cases indexRel <;> try (simp_all)
                case con rel =>
                  rename_i sourceFields targetFields tag typeId
                  cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
                  split_ifs at resultShape <;> simp_all
                case int right =>
                  simpa using intDivMod_body_related next nextTarget trace values .div left right states (Or.inl rfl)


/-- Integer remainder rejects any argument count other than two. -/
theorem intMod_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src (.arith .mod .intT)) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- Integer remainder simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_intMod {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith .mod .intT)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith .mod .intT)) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src (.arith .mod .intT)) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply intMod_wrong_arity
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
              case int left =>
                cases indexRel <;> try (simp_all)
                case con rel =>
                  rename_i sourceFields targetFields tag typeId
                  cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
                  split_ifs at resultShape <;> simp_all
                case int right =>
                  simpa using intDivMod_body_related next nextTarget trace values .mod left right states (Or.inr rfl)

end Flapjack.Compiler.Backend.FlatToClos

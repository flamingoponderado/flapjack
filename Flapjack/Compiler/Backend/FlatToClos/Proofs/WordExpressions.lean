import Flapjack.Compiler.Backend.FlatToClos.Proofs.IntegerExpressions
import Flapjack.Compiler.Backend.FlatToClos.Proofs.WordOperations

/-! Word arithmetic expression simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- Word64 addition rejects any argument count other than two. -/
theorem word64Add_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src (.arith .add (.wordT .w64))) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- Word64 addition simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_word64Add {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith .add (.wordT .w64))) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith .add (.wordT .w64))) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src (.arith .add (.wordT .w64))) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply word64Add_wrong_arity
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
              case word64 _ =>
                cases indexRel <;> try (simp_all)
                case con rel =>
                  rename_i sourceFields targetFields tag typeId
                  cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
                  split_ifs at resultShape <;> simp_all
                case word64 _ =>
                  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
                    FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
                    SemanticPrimitivesHOL.doAppNumericCore, ClosSem.doApp, ClosSem.applyNumeric,
                    ClosSem.doWordApp, ClosSem.doWordAppIntegral, ClosSem.applyWordOp,
                    SemanticPrimitivesHOL.wordArith, states, EvalResultRel.value (.cons (ValueRel.word64 _) .nil)]


/-- Word8 addition rejects any argument count other than two. -/
theorem word8Add_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src (.arith .add (.wordT .w8))) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- Word8 addition simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_word8Add {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith .add (.wordT .w8))) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith .add (.wordT .w8))) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src (.arith .add (.wordT .w8))) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply word8Add_wrong_arity
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
              case word8 left =>
                cases indexRel <;> try (simp_all)
                case con rel =>
                  rename_i sourceFields targetFields tag typeId
                  cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
                  split_ifs at resultShape <;> simp_all
                case word8 right =>
                  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
                    FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
                    SemanticPrimitivesHOL.doAppNumericCore, ClosSem.doApp, ClosSem.applyNumeric,
                    ClosSem.doWordApp, ClosSem.doWordAppIntegral, ClosSem.intToByte_toNat, ClosSem.applyWordOp,
                    SemanticPrimitivesHOL.wordArith, states]
                  exact .value (.cons (by simpa using (ValueRel.word8 (left + right))) .nil)


/-- Word64 subtraction rejects any argument count other than two. -/
theorem word64Sub_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src (.arith .sub (.wordT .w64))) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- Word64 subtraction simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_word64Sub {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith .sub (.wordT .w64))) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith .sub (.wordT .w64))) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src (.arith .sub (.wordT .w64))) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply word64Sub_wrong_arity
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
              case word64 _ =>
                cases indexRel <;> try (simp_all)
                case con rel =>
                  rename_i sourceFields targetFields tag typeId
                  cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
                  split_ifs at resultShape <;> simp_all
                case word64 _ =>
                  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
                    FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
                    SemanticPrimitivesHOL.doAppNumericCore, ClosSem.doApp, ClosSem.applyNumeric,
                    ClosSem.doWordApp, ClosSem.doWordAppIntegral, ClosSem.applyWordOp,
                    SemanticPrimitivesHOL.wordArith, states, EvalResultRel.value (.cons (ValueRel.word64 _) .nil)]


/-- Word8 subtraction rejects any argument count other than two. -/
theorem word8Sub_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src (.arith .sub (.wordT .w8))) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- Word8 subtraction simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_word8Sub {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith .sub (.wordT .w8))) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith .sub (.wordT .w8))) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src (.arith .sub (.wordT .w8))) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply word8Sub_wrong_arity
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
              case word8 left =>
                cases indexRel <;> try (simp_all)
                case con rel =>
                  rename_i sourceFields targetFields tag typeId
                  cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
                  split_ifs at resultShape <;> simp_all
                case word8 right =>
                  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
                    FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
                    SemanticPrimitivesHOL.doAppNumericCore, ClosSem.doApp, ClosSem.applyNumeric,
                    ClosSem.doWordApp, ClosSem.doWordAppIntegral, ClosSem.intToByte_toNat, ClosSem.applyWordOp,
                    SemanticPrimitivesHOL.wordArith, states]
                  exact .value (.cons (by simpa using (ValueRel.word8 (left - right))) .nil)


/-- Word64 bitwise AND rejects any argument count other than two. -/
theorem word64And_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src (.arith .and (.wordT .w64))) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- Word64 bitwise AND simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_word64And {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith .and (.wordT .w64))) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith .and (.wordT .w64))) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src (.arith .and (.wordT .w64))) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply word64And_wrong_arity
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
              case word64 _ =>
                cases indexRel <;> try (simp_all)
                case con rel =>
                  rename_i sourceFields targetFields tag typeId
                  cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
                  split_ifs at resultShape <;> simp_all
                case word64 _ =>
                  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
                    FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
                    SemanticPrimitivesHOL.doAppNumericCore, ClosSem.doApp, ClosSem.applyNumeric,
                    ClosSem.doWordApp, ClosSem.doWordAppIntegral, ClosSem.applyWordOp,
                    SemanticPrimitivesHOL.wordArith, states, EvalResultRel.value (.cons (ValueRel.word64 _) .nil)]


/-- Word8 bitwise AND rejects any argument count other than two. -/
theorem word8And_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src (.arith .and (.wordT .w8))) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- Word8 bitwise AND simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_word8And {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith .and (.wordT .w8))) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith .and (.wordT .w8))) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src (.arith .and (.wordT .w8))) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply word8And_wrong_arity
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
              case word8 left =>
                cases indexRel <;> try (simp_all)
                case con rel =>
                  rename_i sourceFields targetFields tag typeId
                  cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
                  split_ifs at resultShape <;> simp_all
                case word8 right =>
                  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
                    FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
                    SemanticPrimitivesHOL.doAppNumericCore, ClosSem.doApp, ClosSem.applyNumeric,
                    ClosSem.doWordApp, ClosSem.doWordAppIntegral, ClosSem.intToByte_toNat, ClosSem.applyWordOp,
                    SemanticPrimitivesHOL.wordArith, states]
                  exact .value (.cons (by simpa using (ValueRel.word8 (left &&& right))) .nil)


/-- Word64 bitwise OR rejects any argument count other than two. -/
theorem word64Or_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src (.arith .or (.wordT .w64))) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- Word64 bitwise OR simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_word64Or {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith .or (.wordT .w64))) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith .or (.wordT .w64))) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src (.arith .or (.wordT .w64))) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply word64Or_wrong_arity
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
              case word64 _ =>
                cases indexRel <;> try (simp_all)
                case con rel =>
                  rename_i sourceFields targetFields tag typeId
                  cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
                  split_ifs at resultShape <;> simp_all
                case word64 _ =>
                  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
                    FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
                    SemanticPrimitivesHOL.doAppNumericCore, ClosSem.doApp, ClosSem.applyNumeric,
                    ClosSem.doWordApp, ClosSem.doWordAppIntegral, ClosSem.applyWordOp,
                    SemanticPrimitivesHOL.wordArith, states, EvalResultRel.value (.cons (ValueRel.word64 _) .nil)]


/-- Word8 bitwise OR rejects any argument count other than two. -/
theorem word8Or_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src (.arith .or (.wordT .w8))) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- Word8 bitwise OR simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_word8Or {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith .or (.wordT .w8))) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith .or (.wordT .w8))) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src (.arith .or (.wordT .w8))) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply word8Or_wrong_arity
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
              case word8 left =>
                cases indexRel <;> try (simp_all)
                case con rel =>
                  rename_i sourceFields targetFields tag typeId
                  cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
                  split_ifs at resultShape <;> simp_all
                case word8 right =>
                  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
                    FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
                    SemanticPrimitivesHOL.doAppNumericCore, ClosSem.doApp, ClosSem.applyNumeric,
                    ClosSem.doWordApp, ClosSem.doWordAppIntegral, ClosSem.intToByte_toNat, ClosSem.applyWordOp,
                    SemanticPrimitivesHOL.wordArith, states]
                  exact .value (.cons (by simpa using (ValueRel.word8 (left ||| right))) .nil)


/-- Word64 bitwise XOR rejects any argument count other than two. -/
theorem word64Xor_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src (.arith .xor (.wordT .w64))) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- Word64 bitwise XOR simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_word64Xor {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith .xor (.wordT .w64))) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith .xor (.wordT .w64))) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src (.arith .xor (.wordT .w64))) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply word64Xor_wrong_arity
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
              case word64 _ =>
                cases indexRel <;> try (simp_all)
                case con rel =>
                  rename_i sourceFields targetFields tag typeId
                  cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
                  split_ifs at resultShape <;> simp_all
                case word64 _ =>
                  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
                    FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
                    SemanticPrimitivesHOL.doAppNumericCore, ClosSem.doApp, ClosSem.applyNumeric,
                    ClosSem.doWordApp, ClosSem.doWordAppIntegral, ClosSem.applyWordOp,
                    SemanticPrimitivesHOL.wordArith, states, EvalResultRel.value (.cons (ValueRel.word64 _) .nil)]


/-- Word8 bitwise XOR rejects any argument count other than two. -/
theorem word8Xor_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src (.arith .xor (.wordT .w8))) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- Word8 bitwise XOR simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_word8Xor {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith .xor (.wordT .w8))) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith .xor (.wordT .w8))) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src (.arith .xor (.wordT .w8))) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply word8Xor_wrong_arity
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
              case word8 left =>
                cases indexRel <;> try (simp_all)
                case con rel =>
                  rename_i sourceFields targetFields tag typeId
                  cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
                  split_ifs at resultShape <;> simp_all
                case word8 right =>
                  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
                    FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
                    SemanticPrimitivesHOL.doAppNumericCore, ClosSem.doApp, ClosSem.applyNumeric,
                    ClosSem.doWordApp, ClosSem.doWordAppIntegral, ClosSem.intToByte_toNat, ClosSem.applyWordOp,
                    SemanticPrimitivesHOL.wordArith, states]
                  exact .value (.cons (by simpa using (ValueRel.word8 (left ^^^ right))) .nil)


/-- The five supported word arithmetic operations simulate at either width.
This is proof-side infrastructure; HOL correspondence of the surrounding
relations remains under review. -/
theorem evaluate_wordArith {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (action : Arith) (width : WordSize)
    (supported : action = .add ∨ action = .sub ∨ action = .and ∨ action = .or ∨ action = .xor)
    (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith action (.wordT width))) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith action (.wordT width))) args] := by
  rcases supported with rfl | rfl | rfl | rfl | rfl
  · cases width with
    | w8 => exact evaluate_word8Add env names values source target trace args argsSim notTypeError
    | w64 => exact evaluate_word64Add env names values source target trace args argsSim notTypeError
  · cases width with
    | w8 => exact evaluate_word8Sub env names values source target trace args argsSim notTypeError
    | w64 => exact evaluate_word64Sub env names values source target trace args argsSim notTypeError
  · cases width with
    | w8 => exact evaluate_word8And env names values source target trace args argsSim notTypeError
    | w64 => exact evaluate_word64And env names values source target trace args argsSim notTypeError
  · cases width with
    | w8 => exact evaluate_word8Or env names values source target trace args argsSim notTypeError
    | w64 => exact evaluate_word64Or env names values source target trace args argsSim notTypeError
  · cases width with
    | w8 => exact evaluate_word8Xor env names values source target trace args argsSim notTypeError
    | w64 => exact evaluate_word64Xor env names values source target trace args argsSim notTypeError

end Flapjack.Compiler.Backend.FlatToClos

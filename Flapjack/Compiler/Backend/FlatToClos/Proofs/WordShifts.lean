import Flapjack.Compiler.Backend.FlatToClos.Proofs.IntegerExpressions
import Flapjack.Compiler.Backend.FlatToClos.Proofs.WordOperations

/-! Word shift expression simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- Word64 shift rejects any argument count other than one. -/
theorem word64Shift_wrong_arity {C F : Type} (state : FlatSem.State C F) (shift : Flapjack.Shift) (amount : Nat)
    (args : List FlatSem.Value) (wrong : args.length ≠ 1) :
    (FlatSem.applyResult state (.src (.shift .w64 shift amount)) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore, SemanticPrimitivesHOL.doAppBasic]
  | cons first rest =>
    cases rest with
    | nil => simp at wrong
    | cons second rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore, SemanticPrimitivesHOL.doAppBasic]

/-- Shifting a 64-bit word gives related words on both sides,
including the argument-evaluation error cases. -/
theorem evaluate_word64Shift {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (shift : Flapjack.Shift) (amount : Nat) (args : List FlatLang.Exp)
    (argSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.shift .w64 shift amount)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.shift .w64 shift amount)) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src (.shift .w64 shift amount)) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 1 := by
          by_contra wrong
          apply resultShape
          apply word64Shift_wrong_arity next shift amount
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
              SemanticPrimitivesHOL.doAppNumericCore, SemanticPrimitivesHOL.doAppBasic] at resultShape
            case con rel =>
              rename_i sourceFields targetFields tag typeId
              cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
              split_ifs at resultShape <;> simp_all
            case word64 word =>
              simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
                FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
                SemanticPrimitivesHOL.doAppNumericCore, SemanticPrimitivesHOL.doAppBasic,
                ClosSem.doApp, ClosSem.applyNumeric, ClosSem.doWordApp, ClosSem.doWordAppIntegral,
                states, EvalResultRel.value (.cons (ValueRel.word64 _) .nil)]

/-- Word8 shift rejects any argument count other than one. -/
theorem word8Shift_wrong_arity {C F : Type} (state : FlatSem.State C F) (shift : Flapjack.Shift) (amount : Nat)
    (args : List FlatSem.Value) (wrong : args.length ≠ 1) :
    (FlatSem.applyResult state (.src (.shift .w8 shift amount)) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore, SemanticPrimitivesHOL.doAppBasic]
  | cons first rest =>
    cases rest with
    | nil => simp at wrong
    | cons second rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore, SemanticPrimitivesHOL.doAppBasic]

/-- Shifting a 8-bit word gives related words on both sides,
including the argument-evaluation error cases. -/
theorem evaluate_word8Shift {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (shift : Flapjack.Shift) (amount : Nat) (args : List FlatLang.Exp)
    (argSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.shift .w8 shift amount)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.shift .w8 shift amount)) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src (.shift .w8 shift amount)) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 1 := by
          by_contra wrong
          apply resultShape
          apply word8Shift_wrong_arity next shift amount
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
              SemanticPrimitivesHOL.doAppNumericCore, SemanticPrimitivesHOL.doAppBasic] at resultShape
            case con rel =>
              rename_i sourceFields targetFields tag typeId
              cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
              split_ifs at resultShape <;> simp_all
            case word8 word =>
              simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
                FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
                SemanticPrimitivesHOL.doAppNumericCore, SemanticPrimitivesHOL.doAppBasic,
                ClosSem.doApp, ClosSem.applyNumeric, ClosSem.doWordApp, ClosSem.doWordAppIntegral, ClosSem.intToByte_toNat,
                states, EvalResultRel.value (.cons (ValueRel.word8 _) .nil)]

/-- Shifts at either supported word width preserve the proof-side evaluation
relation, including argument-evaluation errors. -/
theorem evaluate_wordShift {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (width : WordSize) (shift : Flapjack.Shift) (amount : Nat)
    (args : List FlatLang.Exp)
    (argSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.shift width shift amount)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.shift width shift amount)) args] := by
  cases width with
  | w8 => exact evaluate_word8Shift env names values source target trace shift amount args argSim notTypeError
  | w64 => exact evaluate_word64Shift env names values source target trace shift amount args argSim notTypeError

end Flapjack.Compiler.Backend.FlatToClos

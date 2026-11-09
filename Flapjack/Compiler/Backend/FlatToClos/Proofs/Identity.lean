import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases

/-! Identity-operation case of the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- The flat evaluator sequences a unary conversion after its operand. -/
theorem evaluate_flat_conversion {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state : FlatSem.State C F) (trace : BackendCommon.Tra) (sourceType targetType : AstHOL.PrimType)
    (argument : FlatLang.Exp) :
    FlatSem.evaluate env state [.app trace (.src (.fromTo sourceType targetType)) [argument]] =
      match FlatSem.evaluate env state [argument] with
      | (next, .err error) => (next, .err error)
      | (next, .val values) => FlatSem.applyResult next (.src (.fromTo sourceType targetType)) values.reverse := by
  rw [FlatSem.evaluate]
  simp only [List.reverse_singleton, (FlatSem.fixClock_evaluations env state [argument] argument []).1]
  cases run : FlatSem.evaluate env state [argument] with
  | mk next result => cases result <;> rfl

/-- The character-to-integer-to-byte conversion pair is erased by the
compiler; successful source conversion and the original closure value remain
related. -/
theorem evaluate_char_word_nop {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (outerTrace innerTrace : BackendCommon.Tra) (argument : FlatLang.Exp)
    (argumentSim : EvalSim env names values source target [argument])
    (notTypeError : (FlatSem.evaluate env source
      [.app outerTrace (.src (.fromTo .intT (.wordT .w8)))
        [.app innerTrace (.src (.fromTo .charT .intT)) [argument]]]).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target
      [.app outerTrace (.src (.fromTo .intT (.wordT .w8)))
        [.app innerTrace (.src (.fromTo .charT .intT)) [argument]]] := by
  unfold EvalSim at argumentSim ⊢
  simp only [compile, compileExps, compileExp, destNop] at argumentSim ⊢
  rw [evaluate_flat_conversion, evaluate_flat_conversion] at notTypeError ⊢
  cases flatRun : FlatSem.evaluate env source [argument] with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate [compileExp names argument] values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argumentSim notTypeError ⊢
      rcases argumentSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        have length := FlatSem.evaluate_singleton_length env source next argument _ flatRun
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | cons _ _ => simp at length
          | nil =>
            cases head <;>
              simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
                FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp_fromTo_core,
                SemanticPrimitivesHOL.doAppNumericCore] at notTypeError ⊢
            case char => exact ⟨states, .value (.cons (.word8 _) .nil)⟩
            case con rel =>
              rename_i sourceFields targetFields tag typeId
              cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
              split_ifs at notTypeError <;> simp_all

/-- The byte-to-integer-to-character pair is likewise erased while
preserving the closure representation of successful values. -/
theorem evaluate_word_char_nop {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (outerTrace innerTrace : BackendCommon.Tra) (argument : FlatLang.Exp)
    (argumentSim : EvalSim env names values source target [argument])
    (notTypeError : (FlatSem.evaluate env source
      [.app outerTrace (.src (.fromTo .intT .charT))
        [.app innerTrace (.src (.fromTo (.wordT .w8) .intT)) [argument]]]).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target
      [.app outerTrace (.src (.fromTo .intT .charT))
        [.app innerTrace (.src (.fromTo (.wordT .w8) .intT)) [argument]]] := by
  unfold EvalSim at argumentSim ⊢
  simp only [compile, compileExps, compileExp, destNop] at argumentSim ⊢
  rw [evaluate_flat_conversion, evaluate_flat_conversion] at notTypeError ⊢
  cases flatRun : FlatSem.evaluate env source [argument] with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate [compileExp names argument] values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argumentSim notTypeError ⊢
      rcases argumentSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        have length := FlatSem.evaluate_singleton_length env source next argument _ flatRun
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | cons _ _ => simp at length
          | nil =>
            cases head <;>
              simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
                FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp_fromTo_core,
                SemanticPrimitivesHOL.doAppNumericCore] at notTypeError ⊢
            case word8 byte =>
              have inRange : ¬((byte.toNat : Int) < 0 ∨ 255 < (byte.toNat : Int)) := by
                have := byte.isLt
                omega
              simp [inRange, states, EvalResultRel.value (.cons (ValueRel.char byte) .nil)]
            case con rel =>
              rename_i sourceFields targetFields tag typeId
              cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
              split_ifs at notTypeError <;> simp_all

end Flapjack.Compiler.Backend.FlatToClos

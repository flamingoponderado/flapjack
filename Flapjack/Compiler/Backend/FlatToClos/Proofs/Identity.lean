import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases

/-! Identity-operation case of the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- A unary flat identity operation has the same result as its operand. -/
theorem evaluate_flat_id {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state : FlatSem.State C F) (trace : BackendCommon.Tra) (argument : FlatLang.Exp) :
    FlatSem.evaluate env state [.app trace .id [argument]] = FlatSem.evaluate env state [argument] := by
  rw [FlatSem.evaluate]
  simp only [List.reverse_singleton, (FlatSem.fixClock_evaluations env state [argument] argument []).1]
  cases run : FlatSem.evaluate env state [argument] with
  | mk next result =>
    cases result with
    | err error => rfl
    | val values =>
      have length := FlatSem.evaluate_singleton_length env state next argument values run
      cases values with
      | nil => simp at length
      | cons first rest =>
        cases rest with
        | cons _ _ => simp at length
        | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat]

/-- Unary identity compilation preserves evaluation and the value relation. -/
theorem evaluate_id {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (argument : FlatLang.Exp)
    (argumentSim : EvalSim env names values source target [argument]) :
    EvalSim env names values source target [.app trace .id [argument]] := by
  unfold EvalSim at argumentSim ⊢
  simp only [compile, compileExps, compileExp, compileOp, arg1, List.reverse_singleton] at argumentSim ⊢
  rw [evaluate_flat_id]
  exact argumentSim

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

/-- Converting a byte character to an integer and then to a byte word
preserves its eight bits. -/
theorem char_word_roundtrip {C F : Type} (state : FlatSem.State C F) (byte : BitVec 8) :
    FlatSem.applyResult state (.src (.fromTo .charT .intT)) [.litv (.char byte)] =
      (state, .val [.litv (.intLit byte.toNat)]) ∧
    FlatSem.applyResult state (.src (.fromTo .intT (.wordT .w8))) [.litv (.intLit byte.toNat)] =
      (state, .val [.litv (.word8 byte)]) := by
  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
    FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
    SemanticPrimitivesHOL.doAppNumericCore]

/-- Converting a byte word to an integer and then to a character preserves
its eight bits and stays within the character bounds. -/
theorem word_char_roundtrip {C F : Type} (state : FlatSem.State C F) (byte : BitVec 8) :
    FlatSem.applyResult state (.src (.fromTo (.wordT .w8) .intT)) [.litv (.word8 byte)] =
      (state, .val [.litv (.intLit byte.toNat)]) ∧
    FlatSem.applyResult state (.src (.fromTo .intT .charT)) [.litv (.intLit byte.toNat)] =
      (state, .val [.litv (.char byte)]) := by
  have bound : byte.toNat ≤ 255 := by have := byte.isLt; omega
  have inRange : ¬((byte.toNat : Int) < 0 ∨ 255 < (byte.toNat : Int)) := by omega
  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
    FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
    SemanticPrimitivesHOL.doAppNumericCore, inRange]

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
  simp only [compile, compileExps, compileExp] at argumentSim ⊢
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
                FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
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
  simp only [compile, compileExps, compileExp] at argumentSim ⊢
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
                FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp,
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

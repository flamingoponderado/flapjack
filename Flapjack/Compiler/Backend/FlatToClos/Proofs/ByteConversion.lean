import Flapjack.Compiler.Backend.FlatToClos.Proofs.Conversions

/-! Integer-to-byte conversion for the proof-side flat-to-closure relation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- The closure remainder by 256 is the integer encoding of the low byte,
including for negative integers. -/
theorem intToByte_remainder (value : Int) :
    (BitVec.ofInt 8 value).toNat = (value.fmod 256).toNat ∧
    (0 : Int) ≤ value.fmod 256 := by
  simp [BitVec.toNat_ofInt, Int.fmod_eq_emod, Int.emod_nonneg]

/-- The emitted remainder operation returns the closure representation of
the source conversion result. -/
theorem intToByte_operation {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (value : Int) :
    ClosSem.evaluate [.op trace (.intOp .mod)
      [.op trace (.intOp (.const 256)) [], .var trace 0]] [.number value] state =
      (.val [.number (value.fmod 256)], state) ∧
    ValueRel (.litv (.word8 (BitVec.ofInt 8 value))) (.number (value.fmod 256)) := by
  have remainder := intToByte_remainder value
  constructor
  · simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric, ClosSem.doIntApp]
  · have rel := ValueRel.word8 (BitVec.ofInt 8 value)
    simpa [remainder.1, Int.toNat_of_nonneg remainder.2] using rel

/-- The emitted modulo expression evaluates its argument and propagates any
argument error before applying the remainder operation. -/
theorem evaluate_mod256_argument {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (expression : ClosLang.Exp) (env : List ClosSem.Value) :
    ClosSem.evaluate [.op trace (.intOp .mod)
      [.op trace (.intOp (.const 256)) [], expression]] env state =
      let run := ClosSem.evaluate [expression] env state
      match run with
      | (.err e, next) => (.err e, next)
      | (.val vs, next) =>
        match ClosSem.doApp (.intOp .mod) (vs.reverse ++ [.number 256]) next with
        | .err e => (.err e, next)
        | .val (v, last) => (.val [v], last) := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  simp only [ClosSem.evaluate, ClosSem.doApp, ClosSem.applyNumeric, ClosSem.doIntApp]
  cases run : ClosSem.evaluate [expression] env state with
  | mk result next => (cases result <;> simp [ClosSem.fixClock, run]); rfl

/-- The non-erased unary integer-to-byte lowering preserves the proof-side
simulation. The syntactic condition is discharged separately for each
source expression shape. -/
theorem evaluate_intToWord8_regular {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (argument : FlatLang.Exp)
    (compiled : compileExp names (.app trace (.src (.fromTo .intT (.wordT .w8))) [argument]) =
      .op trace (.intOp .mod) [.op trace (.intOp (.const 256)) [], compileExp names argument])
    (argSim : (FlatSem.evaluate env source [argument]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target [argument])
    (notTypeError : (FlatSem.evaluate env source
      [.app trace (.src (.fromTo .intT (.wordT .w8))) [argument]]).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.fromTo .intT (.wordT .w8))) [argument]] := by
  have argNotTypeError : (FlatSem.evaluate env source [argument]).2 ≠ .err (.abort .typeError) := by
    intro failed
    apply notTypeError
    rw [evaluate_flat_conversion]
    cases run : FlatSem.evaluate env source [argument] with
    | mk next result => simp_all
  have argSim := argSim argNotTypeError
  unfold EvalSim at argSim ⊢
  simp only [compile, compileExps, compiled] at ⊢
  simp only [compile, compileExps] at argSim
  rw [evaluate_flat_conversion, evaluate_mod256_argument] at ⊢
  rw [evaluate_flat_conversion] at notTypeError
  cases flatRun : FlatSem.evaluate env source [argument] with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate [compileExp names argument] values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argSim notTypeError ⊢
      rcases argSim with ⟨states, results⟩
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
            cases head <;> simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
              FlatSem.applyNumericProjection, FlatSem.flatToValue, FlatSem.valueToFlat,
              SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore] at notTypeError ⊢
            case con rel =>
              rename_i sourceFields targetFields tag typeId
              cases sourceFields <;> cases typeId <;> simp_all [SemanticPrimitivesHOL.boolValue]
              split_ifs at notTypeError <;> simp_all
            case int value =>
              have remainder := intToByte_remainder value
              have rel := ValueRel.word8 (BitVec.ofInt 8 value)
              simp [ClosSem.doApp, ClosSem.applyNumeric, ClosSem.doIntApp, states]
              exact .value (.cons (by simpa [remainder.1, Int.toNat_of_nonneg remainder.2] using rel) .nil)

/-- Outside the source no-op pattern, unary integer-to-byte conversion emits
an integer remainder. -/
theorem compile_intToWord8_regular (names : List (Option MlString)) (trace : BackendCommon.Tra)
    (argument : FlatLang.Exp)
    (regular : destNop (.src (.fromTo .intT (.wordT .w8))) [argument] = none) :
    compileExp names (.app trace (.src (.fromTo .intT (.wordT .w8))) [argument]) =
      .op trace (.intOp .mod) [.op trace (.intOp (.const 256)) [], compileExp names argument] := by
  cases argument <;> simp_all [destNop, compileExp, compileExps, compileOp, arg1]
  case app innerTrace op innerArgs =>
    cases op <;> try simp_all [compileExp, compileExps, compileOp, arg1]
    case src operation =>
      cases operation <;> try simp_all [compileExp, compileExps, compileOp, arg1]
      case fromTo sourceType targetType =>
        cases sourceType <;> cases targetType <;>
          simp_all [compileExp, compileExps, compileOp, arg1]
        case charT.intT =>
          cases innerArgs with
          | nil => simp [compileExp, compileExps, compileOp, arg1]
          | cons first rest =>
            cases rest with
            | nil => simp at regular
            | cons second rest => simp [compileExp, compileExps, compileOp, arg1]

/-- The byte no-op recognizer identifies exactly the character-to-integer
argument shape. -/
theorem destNop_intToWord8_some (argument x : FlatLang.Exp)
    (found : destNop (.src (.fromTo .intT (.wordT .w8))) [argument] = some x) :
    ∃ trace, argument = .app trace (.src (.fromTo .charT .intT)) [x] := by
  simp only [destNop] at found
  split at found <;> simp_all

/-- Unary integer-to-byte conversion simulates both the ordinary lowering and
the erased character-to-integer pattern. The latter uses the induction
hypothesis for its nested argument. -/
theorem evaluate_intToWord8_singleton {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (argument : FlatLang.Exp)
    (argSim : (FlatSem.evaluate env source [argument]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target [argument])
    (innerSim : ∀ innerTrace inner, argument = .app innerTrace (.src (.fromTo .charT .intT)) [inner] →
      (FlatSem.evaluate env source [inner]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target [inner])
    (notTypeError : (FlatSem.evaluate env source
      [.app trace (.src (.fromTo .intT (.wordT .w8))) [argument]]).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.fromTo .intT (.wordT .w8))) [argument]] := by
  cases found : destNop (.src (.fromTo .intT (.wordT .w8))) [argument] with
  | none =>
    exact evaluate_intToWord8_regular env names values source target trace argument
      (compile_intToWord8_regular names trace argument found) argSim notTypeError
  | some inner =>
    obtain ⟨innerTrace, shape⟩ := destNop_intToWord8_some argument inner found
    have innerNotTypeError : (FlatSem.evaluate env source [inner]).2 ≠ .err (.abort .typeError) := by
      intro failed
      apply notTypeError
      rw [shape, evaluate_flat_conversion, evaluate_flat_conversion]
      cases run : FlatSem.evaluate env source [inner] with
      | mk next result => simp_all
    have simulated := innerSim innerTrace inner shape innerNotTypeError
    subst argument
    exact evaluate_char_word_nop env names values source target trace innerTrace inner simulated notTypeError

/-- Integer-to-Word8 conversion rejects any argument count other than one. -/
theorem intToWord8_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 1) :
    (FlatSem.applyResult state (.src (.fromTo .intT (.wordT .w8))) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp at wrong
    | cons second rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- At a non-unary syntactic arity, the conversion can only propagate an
argument error under the source non-type-error hypothesis. -/
theorem evaluate_intToWord8_nonUnary {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp) (wrong : args.length ≠ 1)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.fromTo .intT (.wordT .w8))) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.fromTo .intT (.wordT .w8))) args] := by
  have compiled : compileExp names (.app trace (.src (.fromTo .intT (.wordT .w8))) args) =
      .let .none (compileExps names args).reverse (.var .none 0) := by
    cases args with
    | nil => rfl
    | cons first rest =>
      cases rest with
      | nil => simp at wrong
      | cons second rest =>
        cases h : (compileExps names rest).reverse <;>
          simp [compileExp, compileOp, arg1, compileExps, List.reverse_cons, h]
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compiled] at ⊢
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
        have resultShape : (FlatSem.applyResult next (.src (.fromTo .intT (.wordT .w8))) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length := FlatSem.evaluate_length env source next args.reverse sourceArgs flatRun
        have wrongValues : sourceArgs.reverse.length ≠ 1 := by
          intro one
          apply wrong
          simpa using length.symm.trans (by simpa using one)
        exact False.elim (resultShape (intToWord8_wrong_arity next sourceArgs.reverse wrongValues))

/-- Integer-to-Word8 conversion preserves the proof-side relation at every
arity, including the erased nested conversion. -/
theorem evaluate_intToWord8 {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (innerSim : ∀ innerTrace inner, args = [.app innerTrace (.src (.fromTo .charT .intT)) [inner]] →
      (FlatSem.evaluate env source [inner]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target [inner])
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.fromTo .intT (.wordT .w8))) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.fromTo .intT (.wordT .w8))) args] := by
  cases args with
  | nil => exact evaluate_intToWord8_nonUnary env names values source target trace [] (by simp) argsSim notTypeError
  | cons first rest =>
    cases rest with
    | nil =>
      apply evaluate_intToWord8_singleton env names values source target trace first (by simpa using argsSim)
      · intro innerTrace inner shape
        exact innerSim innerTrace inner (by simp [shape])
      · exact notTypeError
    | cons second rest =>
      exact evaluate_intToWord8_nonUnary env names values source target trace (first :: second :: rest)
        (by simp) argsSim notTypeError

end Flapjack.Compiler.Backend.FlatToClos

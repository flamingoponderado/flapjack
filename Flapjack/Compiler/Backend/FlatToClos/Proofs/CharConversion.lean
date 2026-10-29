import Flapjack.Compiler.Backend.FlatToClos.Proofs.ByteConversion

/-! Integer-to-character conversion for flat-to-closure lowering. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- The emitted bounds checks agree with the source conversion, including
its character exception. -/
theorem intToChar_body_related {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (value : Int)
    (states : StateRel source target) :
    let flat := FlatSem.applyResult source (.src (.fromTo .intT .charT)) [.litv (.intLit value)]
    let clos := ClosSem.evaluate
      [.ifThenElse trace (.op trace (.intOp .less)
        [.op .none (.intOp (.const 0)) [], .var trace 0])
        (.raise trace (.op trace (.blockOp (.cons 1)) []))
        (.ifThenElse trace (.op trace (.intOp .less)
          [.var trace 0, .op .none (.intOp (.const 255)) []])
          (.raise trace (.op trace (.blockOp (.cons 1)) [])) (.var trace 0))]
      (.number value :: env) target
    StateRel flat.1 clos.2 ∧ EvalResultRel flat.2 clos.1 := by
  by_cases low : value < 0 <;> by_cases high : 255 < value
  all_goals simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
    FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore,
    ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock, ClosSem.applyNumeric, ClosSem.doIntApp,
    ClosSem.boolValue, ClosSem.asBool, BackendCommon.trueTag, BackendCommon.falseTag, low, high, states]
  all_goals first | exact .raise (.con .nil) | skip
  have nonnegative : 0 ≤ value := by omega
  have inRange : value.toNat < 256 := by omega
  have related := ValueRel.char (BitVec.ofNat 8 value.toNat)
  have finalRel : ValueRel (.litv (.char (BitVec.ofNat 8 value.toNat))) (.number value) := by
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt inRange, Int.toNat_of_nonneg nonnegative] using related
  exact .value (.cons finalRel .nil)

/-- The non-erased unary integer-to-character lowering preserves the proof-side
simulation. The syntactic condition is discharged separately for each
source expression shape. -/
theorem evaluate_intToChar_regular {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (argument : FlatLang.Exp)
    (compiled : compileExp names (.app trace (.src (.fromTo .intT .charT)) [argument]) =
      .let trace [compileExp names argument] (.ifThenElse trace (.op trace (.intOp .less)
        [.op .none (.intOp (.const 0)) [], .var trace 0])
        (.raise trace (.op trace (.blockOp (.cons 1)) []))
        (.ifThenElse trace (.op trace (.intOp .less)
          [.var trace 0, .op .none (.intOp (.const 255)) []])
          (.raise trace (.op trace (.blockOp (.cons 1)) [])) (.var trace 0))))
    (argSim : (FlatSem.evaluate env source [argument]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target [argument])
    (notTypeError : (FlatSem.evaluate env source
      [.app trace (.src (.fromTo .intT .charT)) [argument]]).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.fromTo .intT .charT)) [argument]] := by
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
  rw [evaluate_flat_conversion, ClosSem.evaluate, ClosSem.fixClock_evaluate] at ⊢
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
              simpa [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
                FlatSem.applyNumericProjection, FlatSem.flatToValue, FlatSem.valueToFlat,
                SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore] using
                intToChar_body_related next nextTarget trace values value states

/-- Outside the source no-op pattern, unary integer-to-character conversion emits
the character range checks. -/
theorem compile_intToChar_regular (names : List (Option MlString)) (trace : BackendCommon.Tra)
    (argument : FlatLang.Exp)
    (regular : destNop (.src (.fromTo .intT .charT)) [argument] = none) :
    compileExp names (.app trace (.src (.fromTo .intT .charT)) [argument]) =
      .let trace [compileExp names argument] (.ifThenElse trace (.op trace (.intOp .less)
        [.op .none (.intOp (.const 0)) [], .var trace 0])
        (.raise trace (.op trace (.blockOp (.cons 1)) []))
        (.ifThenElse trace (.op trace (.intOp .less)
          [.var trace 0, .op .none (.intOp (.const 255)) []])
          (.raise trace (.op trace (.blockOp (.cons 1)) [])) (.var trace 0))) := by
  cases argument <;> simp_all [destNop, compileExp, compileExps, compileOp]
  case app innerTrace op innerArgs =>
    cases op <;> try simp_all [compileExp, compileExps, compileOp, arg1]
    case src operation =>
      cases operation <;> try simp_all [compileExp, compileExps, compileOp]
      case fromTo sourceType targetType =>
        cases sourceType <;> cases targetType <;>
          simp_all [compileExp, compileExps, compileOp, arg1]
        case wordT.intT width =>
          cases width with
          | w64 => simp [compileExp, compileExps, compileOp]
          | w8 =>
            cases innerArgs with
            | nil => simp [compileExp, compileExps, compileOp, arg1]
            | cons first rest =>
              cases rest with
              | nil => simp at regular
              | cons second rest => simp [compileExp, compileExps, compileOp, arg1]

/-- The character no-op recognizer identifies exactly the byte-to-integer
argument shape. -/
theorem destNop_intToChar_some (argument x : FlatLang.Exp)
    (found : destNop (.src (.fromTo .intT .charT)) [argument] = some x) :
    ∃ trace, argument = .app trace (.src (.fromTo (.wordT .w8) .intT)) [x] := by
  simp only [destNop] at found
  split at found <;> simp_all

/-- Unary integer-to-character conversion simulates both the ordinary lowering and
the erased byte-to-integer pattern. The latter uses the induction
hypothesis for its nested argument. -/
theorem evaluate_intToChar_singleton {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (argument : FlatLang.Exp)
    (argSim : (FlatSem.evaluate env source [argument]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target [argument])
    (innerSim : ∀ innerTrace inner, argument = .app innerTrace (.src (.fromTo (.wordT .w8) .intT)) [inner] →
      (FlatSem.evaluate env source [inner]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target [inner])
    (notTypeError : (FlatSem.evaluate env source
      [.app trace (.src (.fromTo .intT .charT)) [argument]]).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.fromTo .intT .charT)) [argument]] := by
  cases found : destNop (.src (.fromTo .intT .charT)) [argument] with
  | none =>
    exact evaluate_intToChar_regular env names values source target trace argument
      (compile_intToChar_regular names trace argument found) argSim notTypeError
  | some inner =>
    obtain ⟨innerTrace, shape⟩ := destNop_intToChar_some argument inner found
    have innerNotTypeError : (FlatSem.evaluate env source [inner]).2 ≠ .err (.abort .typeError) := by
      intro failed
      apply notTypeError
      rw [shape, evaluate_flat_conversion, evaluate_flat_conversion]
      cases run : FlatSem.evaluate env source [inner] with
      | mk next result => simp_all
    have simulated := innerSim innerTrace inner shape innerNotTypeError
    subst argument
    exact evaluate_word_char_nop env names values source target trace innerTrace inner simulated notTypeError

/-- Integer-to-character conversion rejects any argument count other than one. -/
theorem intToChar_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 1) :
    (FlatSem.applyResult state (.src (.fromTo .intT .charT)) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp at wrong
    | cons second rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore]

/-- At a non-unary syntactic arity, the conversion can only propagate an
argument error under the source non-type-error hypothesis. -/
theorem evaluate_intToChar_nonUnary {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp) (wrong : args.length ≠ 1)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.fromTo .intT .charT)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.fromTo .intT .charT)) args] := by
  have compiled : compileExp names (.app trace (.src (.fromTo .intT .charT)) args) =
      .let trace (compileExps names args).reverse (.ifThenElse trace (.op trace (.intOp .less)
        [.op .none (.intOp (.const 0)) [], .var trace 0])
        (.raise trace (.op trace (.blockOp (.cons 1)) []))
        (.ifThenElse trace (.op trace (.intOp .less)
          [.var trace 0, .op .none (.intOp (.const 255)) []])
          (.raise trace (.op trace (.blockOp (.cons 1)) [])) (.var trace 0))) := by
    cases args with
    | nil => rfl
    | cons first rest =>
      cases rest with
      | nil => simp at wrong
      | cons second rest => simp [compileExp, compileOp]
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
        have resultShape : (FlatSem.applyResult next (.src (.fromTo .intT .charT)) sourceArgs.reverse).2 ≠
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
        exact False.elim (resultShape (intToChar_wrong_arity next sourceArgs.reverse wrongValues))

/-- Integer-to-character conversion preserves the proof-side relation at every
arity, including the erased nested conversion. -/
theorem evaluate_intToChar {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (innerSim : ∀ innerTrace inner, args = [.app innerTrace (.src (.fromTo (.wordT .w8) .intT)) [inner]] →
      (FlatSem.evaluate env source [inner]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target [inner])
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.fromTo .intT .charT)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.fromTo .intT .charT)) args] := by
  cases args with
  | nil => exact evaluate_intToChar_nonUnary env names values source target trace [] (by simp) argsSim notTypeError
  | cons first rest =>
    cases rest with
    | nil =>
      apply evaluate_intToChar_singleton env names values source target trace first (by simpa using argsSim)
      · intro innerTrace inner shape
        exact innerSim innerTrace inner (by simp [shape])
      · exact notTypeError
    | cons second rest =>
      exact evaluate_intToChar_nonUnary env names values source target trace (first :: second :: rest)
        (by simp) argsSim notTypeError

end Flapjack.Compiler.Backend.FlatToClos

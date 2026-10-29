import Flapjack.Compiler.Backend.FlatToClos.Proofs.StringConstruction

/-! Byte-copy cases for the proof-side flat-to-closure simulation. These
lemmas are Flapjack infrastructure and have not been reviewed as HOL ports. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- The checked string-copy body produces the selected bytes when the
source offset and length are in range. -/
theorem evaluate_copyByteStr_inBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (bytes : List HolChar) (offset length : Int)
    (offsetValid : 0 ≤ offset) (lengthValid : 0 ≤ length)
    (bounds : offset + length ≤ bytes.length) :
    ClosSem.evaluate [copyByteStr trace]
      (.number length :: .number offset :: .byteVector bytes :: env) state =
      (.val [.byteVector ((bytes.drop offset.natAbs).take length.natAbs)], state) := by
  change ClosSem.evaluate
    [.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 0])
      (.raise trace (.op trace (.blockOp (.cons 3)) []))
      (.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))
        (.ifThenElse trace (.op trace (.memOp (.boundsCheckByte true))
          [.op trace (.intOp .add) [.var trace 0, .var trace 1], .var trace 2])
          (.op trace (.memOp (.copyByte true)) [.var trace 0, .var trace 1, .var trace 2])
          (.raise trace (.op trace (.blockOp (.cons 3)) []))))]
    (.number length :: .number offset :: .byteVector bytes :: env) state = _
  have offsetNotNegative : ¬offset < 0 := by omega
  have lengthNotNegative : ¬length < 0 := by omega
  have sumNonnegative : 0 ≤ offset + length := by omega
  have naturalBound : ¬bytes.length < (offset + length).natAbs := by omega
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp,
    ClosSem.applyMemory, ClosSem.applyNumeric, ClosSem.doIntApp,
    ClosSem.boolValue, ClosSem.asBool, BackendCommon.trueTag, BackendCommon.falseTag, copyArray,
    offsetNotNegative, lengthNotNegative, sumNonnegative, naturalBound, bounds]

/-- A negative offset or length, or a slice extending beyond the string,
raises the source's Subscript exception in the generated closure body. -/
theorem evaluate_copyByteStr_outOfBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (bytes : List HolChar) (offset length : Int)
    (bad : offset < 0 ∨ length < 0 ∨ (bytes.length : Int) < offset + length) :
    ClosSem.evaluate [copyByteStr trace]
      (.number length :: .number offset :: .byteVector bytes :: env) state =
      (.err (.raise (.block 3 [])), state) := by
  change ClosSem.evaluate
    [.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 0])
      (.raise trace (.op trace (.blockOp (.cons 3)) []))
      (.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))
        (.ifThenElse trace (.op trace (.memOp (.boundsCheckByte true))
          [.op trace (.intOp .add) [.var trace 0, .var trace 1], .var trace 2])
          (.op trace (.memOp (.copyByte true)) [.var trace 0, .var trace 1, .var trace 2])
          (.raise trace (.op trace (.blockOp (.cons 3)) []))))]
    (.number length :: .number offset :: .byteVector bytes :: env) state = _
  by_cases lengthNegative : length < 0
  · simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
      ClosSem.doIntApp, ClosSem.applyBlock, ClosSem.boolValue, ClosSem.asBool,
      BackendCommon.trueTag, lengthNegative]
  · by_cases offsetNegative : offset < 0
    · simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
        ClosSem.doIntApp, ClosSem.applyBlock, ClosSem.boolValue, ClosSem.asBool,
        BackendCommon.trueTag, BackendCommon.falseTag, lengthNegative, offsetNegative]
    · have beyond : ¬(0 ≤ offset + length ∧ offset + length ≤ (bytes.length : Int)) := by omega
      simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
        ClosSem.doIntApp, ClosSem.applyMemory, ClosSem.applyBlock, ClosSem.boolValue,
        ClosSem.asBool, BackendCommon.falseTag, lengthNegative,
        offsetNegative, beyond]

/-- String-to-string copying preserves the related state, the copied bytes,
and the Subscript exception. -/
theorem copyString_body_related {C F : Type} (source : FlatSem.State C F)
    (target : ClosSem.State C F) (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (value : MlString) (offset length : Int) (states : StateRel source target) :
    let flat := FlatSem.applyResult source (.src .copyStrStr)
      [.litv (.strLit value), .litv (.intLit offset), .litv (.intLit length)]
    let clos := ClosSem.evaluate [copyByteStr trace]
      (.number length :: .number offset :: .byteVector value.explode :: env) target
    StateRel flat.1 clos.2 ∧ EvalResultRel flat.2 clos.1 := by
  by_cases valid : 0 ≤ offset ∧ 0 ≤ length ∧ offset + length ≤ (value.explode.length : Int)
  · obtain ⟨offsetValid, lengthValid, bounds⟩ := valid
    have body := evaluate_copyByteStr_inBounds target trace env value.explode offset length
      offsetValid lengthValid bounds
    have offsetNotNegative : ¬offset < 0 := by omega
    have lengthNotNegative : ¬length < 0 := by omega
    have naturalBound : ¬value.explode.length < (offset + length).natAbs := by omega
    have valueRel : ValueRel
        (.litv (.strLit (.implode ((value.explode.drop offset.natAbs).take length.natAbs))))
        (.byteVector ((value.explode.drop offset.natAbs).take length.natAbs)) := by
      simpa using (ValueRel.string (.implode ((value.explode.drop offset.natAbs).take length.natAbs)))
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
      FlatSem.doAppData, FlatSem.doAppCopy, copyArray, offsetNotNegative, lengthNotNegative,
      naturalBound, body, states, EvalResultRel.value (.cons valueRel .nil)]
  · have bad : offset < 0 ∨ length < 0 ∨ (value.explode.length : Int) < offset + length := by omega
    have body := evaluate_copyByteStr_outOfBounds target trace env value.explode offset length bad
    have failed : copyArray (value.explode, offset) length none = none := by
      simp only [copyArray]
      split
      · rfl
      · rename_i h
        exfalso
        have offsetValid : 0 ≤ offset := by omega
        have lengthValid : 0 ≤ length := by omega
        have naturalAbs := Int.natAbs_of_nonneg (show 0 ≤ offset + length by omega)
        apply valid
        constructor
        · exact offsetValid
        constructor
        · exact lengthValid
        · omega
    have exception : ValueRel FlatSem.subscriptExnV (.block 3 []) := .con .nil
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
      FlatSem.doAppData, FlatSem.doAppCopy, failed, FlatSem.boundsFailure, body, states,
      EvalResultRel.raise exception]

/-- String copying rejects argument counts other than three. -/
theorem copyString_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 3) :
    (FlatSem.applyResult state (.src .copyStrStr) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy]
    | cons second rest =>
      cases rest with
      | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy]
      | cons third rest =>
        cases rest with
        | nil => simp at wrong
        | cons fourth rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy]

/-- String-copy expressions simulate arbitrary argument evaluation when the
source application does not abort with a type error. -/
theorem evaluate_copyString {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .copyStrStr) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .copyStrStr) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
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
        have resultShape : (FlatSem.applyResult next (.src .copyStrStr) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have argLength : sourceArgs.length = 3 := by
          by_contra wrong
          apply resultShape
          apply copyString_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at argLength
        | cons lengthRel tail =>
          cases tail with
          | nil => simp at argLength
          | cons offsetRel tail =>
            cases tail with
            | nil => simp at argLength
            | cons stringRel tail =>
              cases tail with
              | cons _ _ => simp at argLength
              | nil =>
                simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at resultShape
                cases stringRel <;>
                  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
                    FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at resultShape
                case string value =>
                  cases offsetRel <;> try simp at resultShape
                  case int offset =>
                    cases lengthRel <;> try simp at resultShape
                    case int length =>
                      simpa using copyString_body_related next nextTarget trace values value offset length states

end Flapjack.Compiler.Backend.FlatToClos

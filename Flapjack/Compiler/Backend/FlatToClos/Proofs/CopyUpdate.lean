import Flapjack.Compiler.Backend.FlatToClos.Proofs.Copy

/-! Checked byte-array copy updates for the proof-side simulation. These
lemmas are Flapjack infrastructure, not reviewed HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- The generated copy body writes the exact slice when both ranges fit. -/
theorem evaluate_copyByteAw8_inBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (src dst : List HolChar)
    (pointer : Nat) (flag : Bool) (offset length dstOffset : Int)
    (found : state.refs.lookup pointer = some (.byteArray dst))
    (offsetValid : 0 ≤ offset) (lengthValid : 0 ≤ length) (dstValid : 0 ≤ dstOffset)
    (srcBounds : offset + length ≤ src.length) (dstBounds : dstOffset + length ≤ dst.length) :
    ClosSem.evaluate [copyByteAw8 trace]
      (.number dstOffset :: .refPtr flag pointer :: .number length :: .number offset :: .byteVector src :: env) state =
      (.val [ClosSem.unitValue], { state with refs := state.refs.updateEq (pointer, .byteArray
        (dst.take dstOffset.natAbs ++ (src.drop offset.natAbs).take length.natAbs ++
          dst.drop (dstOffset + length).natAbs)) }) := by
  change ClosSem.evaluate
    [.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 2])
      (.raise trace (.op trace (.blockOp (.cons 3)) []))
      (.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 3])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))
        (.ifThenElse trace (.op trace (.memOp (.boundsCheckByte true))
          [.op trace (.intOp .add) [.var trace 2, .var trace 3], .var trace 4])
          (.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 0])
            (.raise trace (.op trace (.blockOp (.cons 3)) []))
            (.ifThenElse trace (.op trace (.memOp (.boundsCheckByte true))
              [.op trace (.intOp .add) [.var trace 2, .var trace 0], .var trace 1])
              (.op trace (.memOp (.copyByte false))
                [.var trace 0, .var trace 1, .var trace 2, .var trace 3, .var trace 4])
              (.raise trace (.op trace (.blockOp (.cons 3)) []))))
          (.raise trace (.op trace (.blockOp (.cons 3)) []))))]
    (.number dstOffset :: .refPtr flag pointer :: .number length :: .number offset :: .byteVector src :: env) state = _
  have offsetNot : ¬offset < 0 := by omega
  have lengthNot : ¬length < 0 := by omega
  have dstNot : ¬dstOffset < 0 := by omega
  have srcSum : 0 ≤ offset + length := by omega
  have srcNatural : ¬src.length < (offset + length).natAbs := by omega
  have dstCheck : 0 ≤ length + dstOffset ∧ length + dstOffset ≤ (dst.length : Int) := by omega
  have dstNatural : ¬dst.length < (length + dstOffset).natAbs := by omega
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
    ClosSem.doIntApp, ClosSem.applyMemory, ClosSem.boolValue, ClosSem.asBool,
    BackendCommon.trueTag, BackendCommon.falseTag, copyArray, found, offsetNot, lengthNot,
    dstNot, srcSum, srcNatural, dstNatural, srcBounds, dstCheck, Int.add_comm]


/-- A negative index or an out-of-range slice raises Subscript before any
store update. -/
theorem evaluate_copyByteAw8_outOfBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (src dst : List HolChar)
    (pointer : Nat) (flag : Bool) (offset length dstOffset : Int)
    (found : state.refs.lookup pointer = some (.byteArray dst))
    (bad : ¬(0 ≤ offset ∧ 0 ≤ length ∧ 0 ≤ dstOffset ∧
      offset + length ≤ (src.length : Int) ∧ dstOffset + length ≤ (dst.length : Int))) :
    ClosSem.evaluate [copyByteAw8 trace]
      (.number dstOffset :: .refPtr flag pointer :: .number length :: .number offset :: .byteVector src :: env) state =
      (.err (.raise (.block 3 [])), state) := by
  change ClosSem.evaluate
    [.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 2])
      (.raise trace (.op trace (.blockOp (.cons 3)) []))
      (.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 3])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))
        (.ifThenElse trace (.op trace (.memOp (.boundsCheckByte true))
          [.op trace (.intOp .add) [.var trace 2, .var trace 3], .var trace 4])
          (.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 0])
            (.raise trace (.op trace (.blockOp (.cons 3)) []))
            (.ifThenElse trace (.op trace (.memOp (.boundsCheckByte true))
              [.op trace (.intOp .add) [.var trace 2, .var trace 0], .var trace 1])
              (.op trace (.memOp (.copyByte false))
                [.var trace 0, .var trace 1, .var trace 2, .var trace 3, .var trace 4])
              (.raise trace (.op trace (.blockOp (.cons 3)) []))))
          (.raise trace (.op trace (.blockOp (.cons 3)) []))))]
    (.number dstOffset :: .refPtr flag pointer :: .number length :: .number offset :: .byteVector src :: env) state = _
  by_cases lengthNeg : length < 0
  · simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
      ClosSem.doIntApp, ClosSem.applyBlock, ClosSem.boolValue, ClosSem.asBool,
      BackendCommon.trueTag, lengthNeg]
  · by_cases offsetNeg : offset < 0
    · simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
        ClosSem.doIntApp, ClosSem.applyBlock, ClosSem.boolValue, ClosSem.asBool,
        BackendCommon.trueTag, BackendCommon.falseTag, lengthNeg, offsetNeg]
    · by_cases srcFits : offset + length ≤ (src.length : Int)
      · by_cases dstNeg : dstOffset < 0
        · have srcValid : 0 ≤ offset + length ∧ offset + length ≤ (src.length : Int) := by omega
          simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
            ClosSem.doIntApp, ClosSem.applyMemory, ClosSem.applyBlock, ClosSem.boolValue,
            ClosSem.asBool, BackendCommon.trueTag, BackendCommon.falseTag, lengthNeg,
            offsetNeg, srcValid, dstNeg]
        · have srcValid : 0 ≤ offset + length ∧ offset + length ≤ (src.length : Int) := by omega
          have dstInvalid : ¬(0 ≤ length + dstOffset ∧ length + dstOffset ≤ (dst.length : Int)) := by omega
          simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
            ClosSem.doIntApp, ClosSem.applyMemory, ClosSem.applyBlock, ClosSem.boolValue,
            ClosSem.asBool, BackendCommon.trueTag, BackendCommon.falseTag, lengthNeg,
            offsetNeg, srcValid, dstNeg, dstInvalid, found, Int.add_comm]
      · have srcInvalid : ¬(0 ≤ offset + length ∧ offset + length ≤ (src.length : Int)) := by omega
        simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
          ClosSem.doIntApp, ClosSem.applyMemory, ClosSem.applyBlock, ClosSem.boolValue,
          ClosSem.asBool, BackendCommon.falseTag, lengthNeg, offsetNeg, srcInvalid]


/-- Reading a related source byte-array slot is equivalent to reading a
byte vector with those contents, even when the source and destination alias. -/
theorem evaluate_copyByteAw8_ref {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (src dst : List HolChar)
    (srcPointer dstPointer : Nat) (srcFlag dstFlag : Bool) (offset length dstOffset : Int)
    (found : state.refs.lookup srcPointer = some (.byteArray src))
    (dstFound : state.refs.lookup dstPointer = some (.byteArray dst)) :
    ClosSem.evaluate [copyByteAw8 trace]
      (.number dstOffset :: .refPtr dstFlag dstPointer :: .number length :: .number offset ::
        .refPtr srcFlag srcPointer :: env) state =
    ClosSem.evaluate [copyByteAw8 trace]
      (.number dstOffset :: .refPtr dstFlag dstPointer :: .number length :: .number offset ::
        .byteVector src :: env) state := by
  change ClosSem.evaluate
    [.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 2])
      (.raise trace (.op trace (.blockOp (.cons 3)) []))
      (.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 3])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))
        (.ifThenElse trace (.op trace (.memOp (.boundsCheckByte true))
          [.op trace (.intOp .add) [.var trace 2, .var trace 3], .var trace 4])
          (.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 0])
            (.raise trace (.op trace (.blockOp (.cons 3)) []))
            (.ifThenElse trace (.op trace (.memOp (.boundsCheckByte true))
              [.op trace (.intOp .add) [.var trace 2, .var trace 0], .var trace 1])
              (.op trace (.memOp (.copyByte false))
                [.var trace 0, .var trace 1, .var trace 2, .var trace 3, .var trace 4])
              (.raise trace (.op trace (.blockOp (.cons 3)) []))))
          (.raise trace (.op trace (.blockOp (.cons 3)) []))))]
    (.number dstOffset :: .refPtr dstFlag dstPointer :: .number length :: .number offset :: .refPtr srcFlag srcPointer :: env) state = _
  change _ = ClosSem.evaluate
    [.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 2])
      (.raise trace (.op trace (.blockOp (.cons 3)) []))
      (.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 3])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))
        (.ifThenElse trace (.op trace (.memOp (.boundsCheckByte true))
          [.op trace (.intOp .add) [.var trace 2, .var trace 3], .var trace 4])
          (.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 0])
            (.raise trace (.op trace (.blockOp (.cons 3)) []))
            (.ifThenElse trace (.op trace (.memOp (.boundsCheckByte true))
              [.op trace (.intOp .add) [.var trace 2, .var trace 0], .var trace 1])
              (.op trace (.memOp (.copyByte false))
                [.var trace 0, .var trace 1, .var trace 2, .var trace 3, .var trace 4])
              (.raise trace (.op trace (.blockOp (.cons 3)) []))))
          (.raise trace (.op trace (.blockOp (.cons 3)) []))))]
    (.number dstOffset :: .refPtr dstFlag dstPointer :: .number length :: .number offset :: .byteVector src :: env) state
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
    ClosSem.doIntApp, ClosSem.applyMemory, found, dstFound]

/-- A failed range check makes the source copy fail before it writes. -/
theorem copyArray_update_none_of_invalid (src dst : List HolChar) (offset length dstOffset : Int)
    (bad : ¬(0 ≤ offset ∧ 0 ≤ length ∧ 0 ≤ dstOffset ∧
      offset + length ≤ (src.length : Int) ∧ dstOffset + length ≤ (dst.length : Int))) :
    copyArray (src, offset) length (some (dst, dstOffset)) = none := by
  by_cases sourceBad : offset < 0 ∨ length < 0 ∨ src.length < (offset + length).natAbs
  · simp [copyArray, sourceBad]
  · have offsetValid : 0 ≤ offset := by omega
    have lengthValid : 0 ≤ length := by omega
    have srcAbs := Int.natAbs_of_nonneg (show 0 ≤ offset + length by omega)
    have srcFits : offset + length ≤ (src.length : Int) := by omega
    have dstBad : dstOffset < 0 ∨ dst.length < (dstOffset + length).natAbs := by
      by_cases neg : dstOffset < 0
      · exact Or.inl neg
      · right
        have dstAbs := Int.natAbs_of_nonneg (show 0 ≤ dstOffset + length by omega)
        omega
    simp [copyArray, sourceBad, dstBad]

/-- String-to-byte-array copying preserves related states and results for
both successful writes and the Subscript exception. -/
theorem copyStringToByteArray_body_related {C F : Type} (source : FlatSem.State C F)
    (target : ClosSem.State C F) (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (value : MlString) (dst : List HolChar) (pointer : Nat) (flag : Bool)
    (offset length dstOffset : Int) (states : StateRel source target)
    (found : storeLookup pointer source.refs = some (.w8array dst)) :
    let flat := FlatSem.applyResult source (.src .copyStrAw8)
      [.litv (.strLit value), .litv (.intLit offset), .litv (.intLit length),
        .loc flag pointer, .litv (.intLit dstOffset)]
    let clos := ClosSem.evaluate [copyByteAw8 trace]
      (.number dstOffset :: .refPtr flag pointer :: .number length :: .number offset ::
        .byteVector value.explode :: env) target
    StateRel flat.1 clos.2 ∧ EvalResultRel flat.2 clos.1 := by
  have targetFound := lookup_byteArray states found
  have foundList : source.refs[pointer]? = some (.w8array dst) := by simpa [storeLookup] using found
  by_cases valid : 0 ≤ offset ∧ 0 ≤ length ∧ 0 ≤ dstOffset ∧
      offset + length ≤ (value.explode.length : Int) ∧ dstOffset + length ≤ (dst.length : Int)
  · obtain ⟨offsetValid, lengthValid, dstValid, srcFits, dstFits⟩ := valid
    let updated := dst.take dstOffset.natAbs ++ (value.explode.drop offset.natAbs).take length.natAbs ++
      dst.drop (dstOffset + length).natAbs
    have body := evaluate_copyByteAw8_inBounds target trace env value.explode dst pointer flag
      offset length dstOffset targetFound offsetValid lengthValid dstValid srcFits dstFits
    have sourceBad : ¬(offset < 0 ∨ length < 0 ∨ value.explode.length < (offset + length).natAbs) := by omega
    have destBad : ¬(dstOffset < 0 ∨ dst.length < (dstOffset + length).natAbs) := by omega
    have newStores := storeRel_setByteArray source.refs target.refs pointer dst updated states.2.2.2.1 foundList
    have newStates : StateRel { source with refs := source.refs.set pointer (.w8array updated) }
        { target with refs := target.refs.updateEq (pointer, .byteArray updated) } := by
      rcases states with ⟨maxApp, ffi, clock, _, globals, values, install⟩
      exact ⟨maxApp, ffi, clock, newStores, globals, values, install⟩
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
      FlatSem.doAppData, FlatSem.doAppCopy, storeLookup, foundList, copyArray, sourceBad, destBad,
      storeAssign, storeValueSameType, body, FlatSem.unitValue, ClosSem.unitValue,
      EvalResultRel.value (.cons (ValueRel.tuple .nil) .nil)]
    simpa [updated, List.append_assoc] using newStates
  · have body := evaluate_copyByteAw8_outOfBounds target trace env value.explode dst pointer flag
      offset length dstOffset targetFound valid
    have failed := copyArray_update_none_of_invalid value.explode dst offset length dstOffset valid
    have exception : ValueRel FlatSem.subscriptExnV (.block 3 []) := .con .nil
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
      FlatSem.doAppData, FlatSem.doAppCopy, found, failed, FlatSem.boundsFailure, body, states,
      EvalResultRel.raise exception]

/-- Byte-array copies preserve related stores and results. The source and
destination pointers may coincide; both reads use the original store. -/
theorem copyByteArrayToByteArray_body_related {C F : Type} (source : FlatSem.State C F)
    (target : ClosSem.State C F) (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (src dst : List HolChar) (srcPointer dstPointer : Nat) (srcFlag dstFlag : Bool)
    (offset length dstOffset : Int) (states : StateRel source target)
    (srcFound : storeLookup srcPointer source.refs = some (.w8array src))
    (dstFound : storeLookup dstPointer source.refs = some (.w8array dst)) :
    let flat := FlatSem.applyResult source (.src .copyAw8Aw8)
      [.loc srcFlag srcPointer, .litv (.intLit offset), .litv (.intLit length),
        .loc dstFlag dstPointer, .litv (.intLit dstOffset)]
    let clos := ClosSem.evaluate [copyByteAw8 trace]
      (.number dstOffset :: .refPtr dstFlag dstPointer :: .number length :: .number offset ::
        .refPtr srcFlag srcPointer :: env) target
    StateRel flat.1 clos.2 ∧ EvalResultRel flat.2 clos.1 := by
  have targetSrc := lookup_byteArray states srcFound
  have targetDst := lookup_byteArray states dstFound
  have closEq := evaluate_copyByteAw8_ref target trace env src dst srcPointer dstPointer
    srcFlag dstFlag offset length dstOffset targetSrc targetDst
  have flatEq : FlatSem.applyResult source (.src .copyAw8Aw8)
      [.loc srcFlag srcPointer, .litv (.intLit offset), .litv (.intLit length),
        .loc dstFlag dstPointer, .litv (.intLit dstOffset)] =
      FlatSem.applyResult source (.src .copyStrAw8)
      [.litv (.strLit (.implode src)), .litv (.intLit offset), .litv (.intLit length),
        .loc dstFlag dstPointer, .litv (.intLit dstOffset)] := by
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
      FlatSem.doAppData, FlatSem.doAppCopy, srcFound, dstFound]
    cases copyArray (src, offset) length (some (dst, dstOffset)) <;> simp
  rw [flatEq, closEq]
  simpa using copyStringToByteArray_body_related source target trace env (.implode src) dst
    dstPointer dstFlag offset length dstOffset states dstFound

/-- A string-to-byte-array copy requires exactly five arguments. -/
theorem copyStringToByteArray_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 5) :
    (FlatSem.applyResult state (.src .copyStrAw8) args).2 = .err (.abort .typeError) := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, rest⟩⟩⟩⟩⟩⟩
  all_goals simp_all [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
    FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy]

/-- The checked string-to-byte-array copy simulates argument evaluation,
range checks, and store updates whenever the source avoids a type error. -/
theorem evaluate_copyStringToByteArray {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .copyStrAw8) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .copyStrAw8) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src .copyStrAw8) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have argLength : sourceArgs.length = 5 := by
          by_contra wrong
          apply resultShape
          apply copyStringToByteArray_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at argLength
        | cons dstOffsetRel tail =>
          cases tail with
          | nil => simp at argLength
          | cons pointerRel tail =>
            cases tail with
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
                          cases pointerRel <;> try simp at resultShape
                          case loc flag pointer =>
                            cases dstOffsetRel <;> try simp at resultShape
                            case int dstOffset =>
                              cases found : storeLookup pointer next.refs with
                              | none => simp [found] at resultShape
                              | some entry =>
                                cases entry <;> simp [found] at resultShape
                                case w8array dst =>
                                  simpa using copyStringToByteArray_body_related next nextTarget trace values
                                    value dst pointer flag offset length dstOffset states found


/-- A byte-array-to-byte-array copy requires exactly five arguments. -/
theorem copyByteArrayToByteArray_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 5) :
    (FlatSem.applyResult state (.src .copyAw8Aw8) args).2 = .err (.abort .typeError) := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, rest⟩⟩⟩⟩⟩⟩
  all_goals simp_all [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
    FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy]

/-- The checked byte-array-to-byte-array copy simulates argument evaluation,
range checks, and store updates whenever the source avoids a type error. -/
theorem evaluate_copyByteArrayToByteArray {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .copyAw8Aw8) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .copyAw8Aw8) args] := by
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
        have resultShape : (FlatSem.applyResult next (.src .copyAw8Aw8) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have argLength : sourceArgs.length = 5 := by
          by_contra wrong
          apply resultShape
          apply copyByteArrayToByteArray_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at argLength
        | cons dstOffsetRel tail =>
          cases tail with
          | nil => simp at argLength
          | cons pointerRel tail =>
            cases tail with
            | nil => simp at argLength
            | cons lengthRel tail =>
              cases tail with
              | nil => simp at argLength
              | cons offsetRel tail =>
                cases tail with
                | nil => simp at argLength
                | cons srcPointerRel tail =>
                  cases tail with
                  | cons _ _ => simp at argLength
                  | nil =>
                    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at resultShape
                    cases srcPointerRel <;>
                      simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
                        FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at resultShape
                    case loc srcFlag srcPointer =>
                      cases offsetRel <;> try simp at resultShape
                      case int offset =>
                        cases lengthRel <;> try simp at resultShape
                        case int length =>
                          cases pointerRel <;> try simp at resultShape
                          case loc flag pointer =>
                            cases dstOffsetRel <;> try simp at resultShape
                            case int dstOffset =>
                              cases srcFound : storeLookup srcPointer next.refs with
                              | none => simp [srcFound] at resultShape
                              | some srcEntry =>
                                cases srcEntry <;> simp [srcFound] at resultShape
                                case w8array src =>
                                  cases dstFound : storeLookup pointer next.refs with
                                  | none => simp [dstFound] at resultShape
                                  | some dstEntry =>
                                    cases dstEntry <;> simp [dstFound] at resultShape
                                    case w8array dst =>
                                      simpa using copyByteArrayToByteArray_body_related next nextTarget trace values
                                        src dst srcPointer pointer srcFlag flag offset length dstOffset states srcFound dstFound

/-- The byte-copy and XOR operator family preserves the proof-side evaluator
simulation. This packages the five expression cases for a future general
operator theorem; it is not a reviewed port of HOL's `op_byte_copy`. -/
theorem evaluate_byteCopy {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp) (op : Flapjack.AstHOL.Op)
    (copyOp : op = .copyStrAw8 ∨ op = .copyAw8Str ∨ op = .copyAw8Aw8 ∨
      op = .copyStrStr ∨ op = .xorAw8StrUnsafe)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src op) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src op) args] := by
  rcases copyOp with rfl | rfl | rfl | rfl | rfl
  · exact evaluate_copyStringToByteArray env names values source target trace args argsSim notTypeError
  · exact evaluate_copyByteArray env names values source target trace args argsSim notTypeError
  · exact evaluate_copyByteArrayToByteArray env names values source target trace args argsSim notTypeError
  · exact evaluate_copyString env names values source target trace args argsSim notTypeError
  · exact evaluate_xorByteArray env names values source target trace args argsSim notTypeError

end Flapjack.Compiler.Backend.FlatToClos

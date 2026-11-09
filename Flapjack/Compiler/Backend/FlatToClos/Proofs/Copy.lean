import Flapjack.Compiler.Backend.FlatToClos.Proofs.StringConstruction
import Flapjack.Compiler.Backend.FlatToClos.Proofs.ArrayUpdate

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

/-- A byte-array reference and a byte vector containing the same bytes take
the same checked copy path. -/
theorem evaluate_copyByteStr_ref {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (pointer : Nat) (flag : Bool) (bytes : List HolChar) (offset length : Int)
    (found : state.refs.lookup pointer = some (.byteArray bytes)) :
    ClosSem.evaluate [copyByteStr trace]
      (.number length :: .number offset :: .refPtr flag pointer :: env) state =
    ClosSem.evaluate [copyByteStr trace]
      (.number length :: .number offset :: .byteVector bytes :: env) state := by
  change ClosSem.evaluate
    [.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 0])
      (.raise trace (.op trace (.blockOp (.cons 3)) []))
      (.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))
        (.ifThenElse trace (.op trace (.memOp (.boundsCheckByte true))
          [.op trace (.intOp .add) [.var trace 0, .var trace 1], .var trace 2])
          (.op trace (.memOp (.copyByte true)) [.var trace 0, .var trace 1, .var trace 2])
          (.raise trace (.op trace (.blockOp (.cons 3)) []))))]
    (.number length :: .number offset :: .refPtr flag pointer :: env) state = _
  change _ = ClosSem.evaluate
    [.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 0])
      (.raise trace (.op trace (.blockOp (.cons 3)) []))
      (.ifThenElse trace (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))
        (.ifThenElse trace (.op trace (.memOp (.boundsCheckByte true))
          [.op trace (.intOp .add) [.var trace 0, .var trace 1], .var trace 2])
          (.op trace (.memOp (.copyByte true)) [.var trace 0, .var trace 1, .var trace 2])
          (.raise trace (.op trace (.blockOp (.cons 3)) []))))]
    (.number length :: .number offset :: .byteVector bytes :: env) state
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
    ClosSem.doIntApp, ClosSem.applyMemory, found]

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

/-- A related byte-array slot yields the same copy result and exception as
copying the corresponding immutable string. -/
theorem copyByteArray_body_related {C F : Type} (source : FlatSem.State C F)
    (target : ClosSem.State C F) (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (pointer : Nat) (flag : Bool) (bytes : List HolChar) (offset length : Int)
    (states : StateRel source target)
    (found : storeLookup pointer source.refs = some (.w8array bytes)) :
    let flat := FlatSem.applyResult source (.src .copyAw8Str)
      [.loc flag pointer, .litv (.intLit offset), .litv (.intLit length)]
    let clos := ClosSem.evaluate [copyByteStr trace]
      (.number length :: .number offset :: .refPtr flag pointer :: env) target
    StateRel flat.1 clos.2 ∧ EvalResultRel flat.2 clos.1 := by
  have targetFound := lookup_byteArray states found
  have closEq := evaluate_copyByteStr_ref target trace env pointer flag bytes offset length targetFound
  have flatEq : FlatSem.applyResult source (.src .copyAw8Str)
      [.loc flag pointer, .litv (.intLit offset), .litv (.intLit length)] =
      FlatSem.applyResult source (.src .copyStrStr)
      [.litv (.strLit (.implode bytes)), .litv (.intLit offset), .litv (.intLit length)] := by
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
      FlatSem.doAppData, FlatSem.doAppCopy, found]
    cases copyArray (bytes, offset) length none <;> simp
  rw [flatEq, closEq]
  simpa using copyString_body_related source target trace env (.implode bytes) offset length states

/-- Successful XOR updates replace the corresponding byte-array slot on both
sides, preserving the proof-side state relation. -/
theorem xorByteArray_related {C F : Type} (source : FlatSem.State C F)
    (target : ClosSem.State C F) (pointer : Nat) (flag : Bool)
    (bytes updated : List HolChar) (value : MlString)
    (states : StateRel source target)
    (found : storeLookup pointer source.refs = some (.w8array bytes))
    (xor : xorBytes value.explode bytes = some updated) :
    ∃ targetNext,
      FlatSem.doAppCopy source .xorAw8StrUnsafe [.loc flag pointer, .litv (.strLit value)] =
        some (some ({ source with refs := source.refs.set pointer (.w8array updated) }, .val FlatSem.unitValue)) ∧
      ClosSem.applyMemory .xorByte [.refPtr flag pointer, .byteVector value.explode] target =
        some (ClosSem.unitValue, targetNext) ∧
      StateRel { source with refs := source.refs.set pointer (.w8array updated) } targetNext := by
  have targetFound := lookup_byteArray states found
  have foundList : source.refs[pointer]? = some (.w8array bytes) := by simpa [storeLookup] using found
  have newStores := storeRel_setByteArray source.refs target.refs pointer bytes updated states.2.2.2.1
    foundList
  refine ⟨{ target with refs := target.refs.updateEq (pointer, .byteArray updated) }, ?_, ?_, ?_⟩
  · simp [FlatSem.doAppCopy, foundList, xor, storeAssign, storeLookup, storeValueSameType]
  · simp [ClosSem.applyMemory, targetFound, xor]
  · rcases states with ⟨maxApp, ffi, clock, _, globals, values, install⟩
    exact ⟨maxApp, ffi, clock, newStores, globals, values, install⟩

end Flapjack.Compiler.Backend.FlatToClos

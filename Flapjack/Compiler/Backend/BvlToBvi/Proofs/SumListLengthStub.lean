import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileToListByte

/-! The byte-array list length-summing runtime stub. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- The sum stub returns its accumulator on the empty list. Untagged pending
BVI evaluator and dispatcher correspondence review. -/
theorem evaluate_sumListLength_nil {C F : Type} (n : Nat) (state : BviSem.BviState C F) :
    BviSem.evaluate [sumListLengthCode.2] [BvlSem.listToValue [], .number n] state =
      (.val [.number n], state) := by
  have testRun : BviSem.evaluate [.op (.blockOp (.tagLenEq 0 0)) [.var 0]]
      [BvlSem.listToValue [], .number n] state = (.val [BvlSem.boolValue true], state) := by
    simp [BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
      BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, BvlSem.listToValue,
      BviSem.fromBvl_toBvl, BvlSem.boolValue, BackendCommon.boolToTag, BackendCommon.nilTag]
  change BviSem.evaluate [.ifThenElse (.op (.blockOp (.tagLenEq 0 0)) [.var 0]) (.var 1) _] _ _ = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, testRun]
  change BviSem.evaluate [.var 1] [BvlSem.listToValue [], .number n] state = _
  simp [BviSem.evaluate]

/-- One byte-array length is added to the accumulator before the recursive
call. Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem evaluate_sumListLength_cons {C F : Type} (ptr : Nat) (bytes : List (BitVec 8))
    (tail : List Value) (n : Nat) (state final : BviSem.BviState C F) (result : Value)
    (lookup : state.refs.lookup ptr = some (.byteArray true bytes))
    (code : sptLookup sumListLengthLocation state.code = some sumListLengthCode)
    (clock : state.clock ≠ 0)
    (recursive : BviSem.evaluate [sumListLengthCode.2]
      [BvlSem.listToValue tail, .number (Int.ofNat (n + bytes.length))]
      (BviSem.decClock 1 state) = (.val [result], final)) :
    BviSem.evaluate [sumListLengthCode.2]
      [BvlSem.listToValue (.refPtr true ptr :: tail), .number n] state = (.val [result], final) := by
  let env : List Value := [BvlSem.listToValue (.refPtr true ptr :: tail), .number n]
  let head : Bvi.Exp := .op (.memOp .el) [.op (.intOp (.const 0)) [], .var 0]
  let readTail : Bvi.Exp := .op (.memOp .el) [.op (.intOp (.const 1)) [], .var 0]
  let lengthExp : Bvi.Exp := .op (.memOp .lengthByte) [head]
  let add : Bvi.Exp := .op (.intOp .add) [.var 1, lengthExp]
  have headRun : BviSem.evaluate [head] env state = (.val [.refPtr true ptr], state) := by
    apply evaluate_listElement 0 [.refPtr true ptr, BvlSem.listToValue tail] BackendCommon.consTag 0
    · decide
    · simp [env, BvlSem.listToValue]
    · rfl
  have tailRun : BviSem.evaluate [readTail] env state = (.val [BvlSem.listToValue tail], state) := by
    apply evaluate_listElement 1 [.refPtr true ptr, BvlSem.listToValue tail] BackendCommon.consTag 0
    · decide
    · simp [env, BvlSem.listToValue]
    · rfl
  have lengthRun : BviSem.evaluate [lengthExp] env state = (.val [.number bytes.length], state) := by
    dsimp [lengthExp]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, headRun]
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
      BvlSem.applyMemory, BviSem.toBvl, BviSem.fromBvl, lookup]
  have nRun : BviSem.evaluate [.var 1] env state = (.val [.number n], state) := by simp [env, BviSem.evaluate]
  have addRun : BviSem.evaluate [add] env state = (.val [.number (Int.ofNat (n + bytes.length))], state) := by
    have args := evaluate_pair (.var 1) lengthExp env state (.number n) (.number bytes.length) nRun lengthRun
    dsimp [add]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, args]
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
      BvlSem.applyNumeric, BvlSem.doIntApp, BviSem.fromBvl_toBvl, Int.add_comm]
  have argsRun := evaluate_pair readTail add env state (BvlSem.listToValue tail)
    (.number (Int.ofNat (n + bytes.length))) tailRun addRun
  have testRun : BviSem.evaluate [.op (.blockOp (.tagLenEq 0 0)) [.var 0]] env state =
      (.val [BvlSem.boolValue false], state) := by
    simp [env, BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
      BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, BvlSem.listToValue,
      BviSem.fromBvl_toBvl, BvlSem.boolValue, BackendCommon.boolToTag]
  change BviSem.evaluate [.ifThenElse (.op (.blockOp (.tagLenEq 0 0)) [.var 0]) (.var 1)
    (.call 0 (some sumListLengthLocation) [readTail, add] none)] env state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, testRun]
  change BviSem.evaluate [.call 0 (some sumListLengthLocation) [readTail, add] none] env state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
  simp only [BvlSem.findCode, code, sumListLengthCode, List.length_cons, List.length_nil, ite_true,
    Nat.zero_add, Nat.lt_one_iff, clock, if_false, BviSem.fixClock_evaluate]
  have recRun := recursive
  simp [sumListLengthCode] at recRun
  simp [recRun]

/-- Summing the lengths of the referenced arrays equals the length of their
concatenation. Untagged pending BVI evaluator and dispatcher review. -/
theorem evaluate_sumListLength {C F : Type} (ptrs : List Nat) (chunks : List (List (BitVec 8)))
    (n : Nat) (state : BviSem.BviState C F)
    (lookups : ptrs.map state.refs.lookup = chunks.map (fun bytes => some (.byteArray true bytes)))
    (code : sptLookup sumListLengthLocation state.code = some sumListLengthCode) :
    ∃ clock, BviSem.evaluate [sumListLengthCode.2]
      [BvlSem.listToValue (ptrs.map (Value.refPtr true)), .number n] (BviProps.incClock clock state) =
      (.val [.number (Int.ofNat (n + chunks.flatten.length))], state) := by
  induction ptrs generalizing chunks n with
  | nil =>
    cases chunks with
    | nil =>
      refine ⟨0, ?_⟩
      simpa [BviProps.incClock] using evaluate_sumListLength_nil n state
    | cons bytes rest => simp at lookups
  | cons ptr ptrs ih =>
    cases chunks with
    | nil => simp at lookups
    | cons bytes chunks =>
      simp only [List.map_cons, List.cons.injEq] at lookups
      obtain ⟨lookup, tailLookups⟩ := lookups
      obtain ⟨clock, recursive⟩ := ih chunks (n + bytes.length) tailLookups
      refine ⟨clock + 1, ?_⟩
      let start := BviProps.incClock (clock + 1) state
      have startLookup : start.refs.lookup ptr = some (.byteArray true bytes) := by
        simpa [start, BviProps.incClock] using lookup
      have startCode : sptLookup sumListLengthLocation start.code = some sumListLengthCode := by
        simpa [start, BviProps.incClock] using code
      have nonzero : start.clock ≠ 0 := by simp [start, BviProps.incClock]
      have clocks : BviSem.decClock 1 start = BviProps.incClock clock state := by
        simp [start, BviSem.decClock, BviProps.incClock]
      have step := evaluate_sumListLength_cons ptr bytes (ptrs.map (Value.refPtr true)) n start state
        (.number (Int.ofNat (n + bytes.length + chunks.flatten.length))) startLookup startCode nonzero
        (by simpa [clocks] using recursive)
      simpa [start, List.flatten, Nat.add_assoc] using step

/-- Source-shaped form for a successfully decoded list of array pointers. -/
theorem evaluate_sumListLength_decoded {C F : Type} (value : Value) (ptrs : List Nat)
    (chunks : List (List (BitVec 8))) (n : Nat) (state : BviSem.BviState C F)
    (decode : BvlSem.valueToList value = some (ptrs.map (Value.refPtr true)))
    (lookups : ptrs.map state.refs.lookup = chunks.map (fun bytes => some (.byteArray true bytes)))
    (code : sptLookup sumListLengthLocation state.code = some sumListLengthCode) :
    ∃ clock, BviSem.evaluate [sumListLengthCode.2] [value, .number n] (BviProps.incClock clock state) =
      (.val [.number (Int.ofNat (n + chunks.flatten.length))], state) := by
  rw [← valueToList_inverse value _ decode]
  exact evaluate_sumListLength ptrs chunks n state lookups code

/-- The call emitted by concatenation computes the required allocation size. -/
theorem evaluate_sumListLength_call {C F : Type} (value : Value) (ptrs : List Nat)
    (chunks : List (List (BitVec 8))) (env : List Value) (state : BviSem.BviState C F)
    (decode : BvlSem.valueToList value = some (ptrs.map (Value.refPtr true)))
    (lookups : ptrs.map state.refs.lookup = chunks.map (fun bytes => some (.byteArray true bytes)))
    (lookup : sptLookup sumListLengthLocation state.code = some sumListLengthCode) :
    ∃ clock, BviSem.evaluate [.call 0 (some sumListLengthLocation)
      [.var 0, .op (.intOp (.const 0)) []] none] (value :: env) (BviProps.incClock clock state) =
      (.val [.number (Int.ofNat chunks.flatten.length)], state) := by
  obtain ⟨clock, stub⟩ := evaluate_sumListLength_decoded value ptrs chunks 0 state decode lookups lookup
  refine ⟨clock + 1, ?_⟩
  let start := BviProps.incClock (clock + 1) state
  have varRun : BviSem.evaluate [.var 0] (value :: env) start = (.val [value], start) := by simp [BviSem.evaluate]
  have zeroRun : BviSem.evaluate [.op (.intOp (.const 0)) []] (value :: env) start = (.val [.number 0], start) := by
    apply evaluate_smallConst
    decide
  have argsRun := evaluate_pair (.var 0) (.op (.intOp (.const 0)) []) (value :: env) start value (.number 0) varRun zeroRun
  change BviSem.evaluate [.call 0 (some sumListLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none]
    (value :: env) start = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
  have code : sptLookup sumListLengthLocation start.code = some sumListLengthCode := by simpa [start, BviProps.incClock] using lookup
  have nonzero : start.clock ≠ 0 := by simp [start, BviProps.incClock]
  have clocks : BviSem.decClock 1 start = BviProps.incClock clock state := by
    simp [start, BviSem.decClock, BviProps.incClock]
  simp only [BvlSem.findCode, code, sumListLengthCode, List.length_cons, List.length_nil, ite_true,
    Nat.zero_add, Nat.lt_one_iff, nonzero, if_false, BviSem.fixClock_evaluate]
  simp [sumListLengthCode] at stub
  simp [clocks, stub]

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

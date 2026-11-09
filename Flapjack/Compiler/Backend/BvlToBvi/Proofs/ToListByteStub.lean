import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileFromListByte

/-! Byte-array to list runtime stub in BVL-to-BVI lowering. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- The byte-array reader returns the accumulator when its index is zero.
Untagged pending BVI evaluator and dispatcher review. -/
theorem evaluate_toListByte_zero {C F : Type} (acc : Value) (ptr : Nat) (flag : Bool)
    (state : BviSem.BviState C F) :
    BviSem.evaluate [toListByteCode.2] [acc, .number 0, .refPtr flag ptr] state = (.val [acc], state) := by
  have testRun : BviSem.evaluate [.op (.blockOp (.equalConst (.int 0))) [.var 1]]
      [acc, .number 0, .refPtr flag ptr] state = (.val [BvlSem.boolValue true], state) := by
    simp [BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
      BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, BviSem.fromBvl_toBvl,
      BvlSem.boolValue, BackendCommon.boolToTag]
  change BviSem.evaluate [.ifThenElse (.op (.blockOp (.equalConst (.int 0))) [.var 1]) (.var 0) _] _ _ = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, testRun]
  change BviSem.evaluate [.var 0] [acc, .number 0, .refPtr flag ptr] state = _
  simp [BviSem.evaluate]

/-- One nonzero byte-array reader iteration, with the recursive execution
supplied as induction hypothesis. Untagged pending BVI evaluator and
dispatcher review. -/
theorem evaluate_toListByte_step {C F : Type} (byte : BitVec 8) (index ptr : Nat)
    (flag mutableRef : Bool) (bytes : List (BitVec 8)) (acc : Value)
    (state final : BviSem.BviState C F) (result : Value)
    (lookup : state.refs.lookup ptr = some (.byteArray mutableRef bytes))
    (selected : bytes[index]? = some byte) (code : sptLookup toListByteLocation state.code = some toListByteCode)
    (clock : state.clock ≠ 0)
    (recursive : BviSem.evaluate [toListByteCode.2]
      [.block BackendCommon.consTag [.number byte.toNat, acc], .number index, .refPtr flag ptr]
      (BviSem.decClock 1 state) = (.val [result], final)) :
    BviSem.evaluate [toListByteCode.2] [acc, .number (Int.ofNat (index + 1)), .refPtr flag ptr] state =
      (.val [result], final) := by
  let input : List Value := [acc, .number (Int.ofNat (index + 1)), .refPtr flag ptr]
  let one : Bvi.Exp := .op (.intOp (.const 1)) []
  let dec : Bvi.Exp := .op (.intOp .sub) [one, .var 1]
  have oneRun : BviSem.evaluate [one] input state = (.val [.number 1], state) := by
    apply evaluate_smallConst
    decide
  have indexRun : BviSem.evaluate [.var 1] input state = (.val [.number (Int.ofNat (index + 1))], state) := by
    simp [input, BviSem.evaluate]
  have decArgs := evaluate_pair one (.var 1) input state (.number 1) (.number (Int.ofNat (index + 1))) oneRun indexRun
  have decRun : BviSem.evaluate [dec] input state = (.val [.number index], state) := by
    dsimp [dec]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, decArgs]
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyNumeric,
      BvlSem.doIntApp, BviSem.fromBvl_toBvl]
  let input2 := .number (Int.ofNat index) :: input
  let read : Bvi.Exp := .op (.memOp .derefByte) [.var 0, .var 3]
  have readArgs : BviSem.evaluate [.var 0, .var 3] input2 state = (.val [.number index, .refPtr flag ptr], state) := by
    apply evaluate_readOnly
    simp [input2, input, BviSem.evaluate]
  have readRun : BviSem.evaluate [read] input2 state = (.val [.number byte.toNat], state) := by
    dsimp [read]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, readArgs]
    have nonnegative : ¬ (index : Int) < 0 := Int.not_lt.mpr (Int.natCast_nonneg index)
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
      BviSem.toBvl, BviSem.fromBvl, lookup, nonnegative, selected]
  let input3 := .number (Int.ofNat byte.toNat) :: input2
  let cons : Bvi.Exp := .op (.blockOp (.cons 0)) [.var 2, .var 0]
  have consArgs : BviSem.evaluate [.var 2, .var 0] input3 state = (.val [acc, .number byte.toNat], state) := by
    apply evaluate_readOnly
    simp [input3, input2, input, BviSem.evaluate]
  have consRun : BviSem.evaluate [cons] input3 state = (.val [.block BackendCommon.consTag [.number byte.toNat, acc]], state) := by
    dsimp [cons]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, consArgs]
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
      BviSem.fromBvl_toBvl, BackendCommon.consTag]
  have callArgs : BviSem.evaluate [cons, .var 1, .var 4] input3 state =
      (.val [.block BackendCommon.consTag [.number byte.toNat, acc], .number index, .refPtr flag ptr], state) := by
    apply evaluate_readOnly
    constructor
    · exact consRun
    simp [input3, input2, input, BviSem.evaluate]
  have testRun : BviSem.evaluate [.op (.blockOp (.equalConst (.int 0))) [.var 1]] input state =
      (.val [BvlSem.boolValue false], state) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, indexRun]
    have nonzeroIndex : (0 : Int) ≠ (index : Int) + 1 := by omega
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
      BviSem.fromBvl_toBvl, BvlSem.boolValue, BackendCommon.boolToTag, nonzeroIndex]
  change BviSem.evaluate [.ifThenElse (.op (.blockOp (.equalConst (.int 0))) [.var 1]) (.var 0)
    (.let [dec] (.let [read] (.call 0 (some toListByteLocation) [cons, .var 1, .var 4] none)))] input state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, testRun]
  change BviSem.evaluate [.let [dec] (.let [read] (.call 0 (some toListByteLocation) [cons, .var 1, .var 4] none))] input state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, decRun]
  change BviSem.evaluate [.let [read] (.call 0 (some toListByteLocation) [cons, .var 1, .var 4] none)] input2 state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, readRun]
  change BviSem.evaluate [.call 0 (some toListByteLocation) [cons, .var 1, .var 4] none] input3 state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, callArgs]
  simp only [BvlSem.findCode, code, toListByteCode, List.length_cons, List.length_nil, ite_true,
    Nat.zero_add, Nat.lt_one_iff, clock, if_false, BviSem.fixClock_evaluate]
  have recRun := recursive
  simp [toListByteCode] at recRun
  simp [recRun]

/-- Reading the array backwards constructs the encoded list in its original
order. Untagged pending BVI evaluator and dispatcher review. -/
theorem evaluate_toListByte {C F : Type} (front rest : List (BitVec 8))
    (ptr : Nat) (flag mutableRef : Bool) (state : BviSem.BviState C F)
    (lookup : state.refs.lookup ptr = some (.byteArray mutableRef (front ++ rest)))
    (code : sptLookup toListByteLocation state.code = some toListByteCode) :
    ∃ clock, BviSem.evaluate [toListByteCode.2]
      [BvlSem.listToValue (rest.map (fun byte => .number byte.toNat)),
        .number front.length, .refPtr flag ptr] (BviProps.incClock clock state) =
      (.val [BvlSem.listToValue ((front ++ rest).map (fun byte => .number byte.toNat))], state) := by
  induction front using List.reverseRecOn generalizing rest with
  | nil =>
    refine ⟨0, ?_⟩
    simpa [BviProps.incClock] using
      evaluate_toListByte_zero (BvlSem.listToValue (rest.map (fun byte => .number byte.toNat))) ptr flag state
  | append_singleton front byte ih =>
    have recLookup : state.refs.lookup ptr = some (.byteArray mutableRef (front ++ byte :: rest)) := by
      simpa [List.append_assoc] using lookup
    obtain ⟨clock, recRun⟩ := ih (byte :: rest) recLookup
    refine ⟨clock + 1, ?_⟩
    let start := BviProps.incClock (clock + 1) state
    have startLookup : start.refs.lookup ptr = some (.byteArray mutableRef ((front ++ [byte]) ++ rest)) := by
      simpa [start, BviProps.incClock] using lookup
    have startCode : sptLookup toListByteLocation start.code = some toListByteCode := by
      simpa [start, BviProps.incClock] using code
    have nonzero : start.clock ≠ 0 := by simp [start, BviProps.incClock]
    have selected : ((front ++ [byte]) ++ rest)[front.length]? = some byte := by
      simp [List.append_assoc]
    have clockState : BviSem.decClock 1 start = BviProps.incClock clock state := by
      simp [start, BviSem.decClock, BviProps.incClock]
    have recursive : BviSem.evaluate [toListByteCode.2]
        [.block BackendCommon.consTag [.number byte.toNat,
          BvlSem.listToValue (rest.map (fun b => .number b.toNat))],
          .number front.length, .refPtr flag ptr] (BviSem.decClock 1 start) =
        (.val [BvlSem.listToValue ((front ++ byte :: rest).map (fun b => .number b.toNat))], state) := by
      rw [clockState]
      simpa [BvlSem.listToValue] using recRun
    have step := evaluate_toListByte_step byte front.length ptr flag mutableRef ((front ++ [byte]) ++ rest)
      (BvlSem.listToValue (rest.map (fun b => .number b.toNat))) start state _
      startLookup selected startCode nonzero recursive
    simpa [start, List.append_assoc] using step

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

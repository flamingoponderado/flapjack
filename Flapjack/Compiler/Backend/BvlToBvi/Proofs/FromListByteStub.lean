import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CopyByteAllocate

/-! Byte-list conversion runtime stub in BVL-to-BVI lowering. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- The byte-list writer returns its destination pointer when the input list
is empty. Untagged pending BVI evaluator and dispatcher review. -/
theorem evaluate_fromListByte_nil {C F : Type} (ptr : Nat) (flag : Bool) (index : Nat)
    (state : BviSem.BviState C F) :
    BviSem.evaluate [fromListByteCode.2] [BvlSem.listToValue [], .number index, .refPtr flag ptr] state =
      (.val [.refPtr flag ptr], state) := by
  have testRun : BviSem.evaluate [.op (.blockOp (.tagLenEq 0 0)) [.var 0]]
      [BvlSem.listToValue [], .number index, .refPtr flag ptr] state = (.val [BvlSem.boolValue true], state) := by
    simp [BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
      BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, BvlSem.listToValue,
      BviSem.fromBvl_toBvl, BvlSem.boolValue, BackendCommon.boolToTag, BackendCommon.nilTag]
  change BviSem.evaluate [.ifThenElse (.op (.blockOp (.tagLenEq 0 0)) [.var 0]) (.var 2) _] _ _ = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, testRun]
  change BviSem.evaluate [.var 2] [BvlSem.listToValue [], .number index, .refPtr flag ptr] state = _
  simp [BviSem.evaluate]

/-- A small constant expression evaluates without changing state. -/
theorem evaluate_smallConst {C F : Type} (n : Int) (env : List Value) (state : BviSem.BviState C F)
    (small : BackendCommon.smallEnoughInt n = true) :
    BviSem.evaluate [.op (.intOp (.const n)) []] env state = (.val [.number n], state) := by
  simp [BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, small]

/-- A generated block-element expression reads the requested element without
changing state. -/
theorem evaluate_listElement {C F : Type} (index : Nat) (fields : List Value) (tag position : Nat)
    (value : Value) (env : List Value) (state : BviSem.BviState C F)
    (small : BackendCommon.smallEnoughInt (Int.ofNat index) = true)
    (varLookup : env[position]? = some (.block tag fields)) (selected : fields[index]? = some value) :
    BviSem.evaluate [.op (.memOp .el) [.op (.intOp (.const (Int.ofNat index))) [], .var position]] env state =
      (.val [value], state) := by
  have constRun := evaluate_smallConst (Int.ofNat index) env state small
  have varRun : BviSem.evaluate [.var position] env state = (.val [.block tag fields], state) := by
    simp [BviSem.evaluate, varLookup]
  have args := evaluate_pair _ _ env state (.number (Int.ofNat index)) (.block tag fields) constRun varRun
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, args]
  have nonnegative : ¬ (index : Int) < 0 := Int.not_lt.mpr (Int.natCast_nonneg index)
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
    BviSem.fromBvl_toBvl, selected, nonnegative]

/-- A generated increment expression computes a natural successor. -/
theorem evaluate_increment {C F : Type} (position n : Nat) (env : List Value) (state : BviSem.BviState C F)
    (varLookup : env[position]? = some (.number n)) :
    BviSem.evaluate [.op (.intOp .add) [.var position, .op (.intOp (.const 1)) []]] env state =
      (.val [.number (Int.ofNat (n + 1))], state) := by
  have varRun : BviSem.evaluate [.var position] env state = (.val [.number n], state) := by
    simp [BviSem.evaluate, varLookup]
  have constRun : BviSem.evaluate [.op (.intOp (.const 1)) []] env state = (.val [.number 1], state) := by
    apply evaluate_smallConst
    decide
  have args := evaluate_pair _ _ env state (.number n) (.number 1) varRun constRun
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, args]
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyNumeric,
    BvlSem.doIntApp, BviSem.fromBvl_toBvl, Int.add_comm]

/-- One nonempty byte-list write and recursive stub call, with the recursive
execution supplied as induction hypothesis. Untagged pending BVI evaluator
and dispatcher correspondence review. -/
theorem evaluate_fromListByte_cons {C F : Type} (byte : BitVec 8) (tail : List Value)
    (ptr index : Nat) (flag mutableRef : Bool) (bytes : List (BitVec 8))
    (state final : BviSem.BviState C F) (result : Value)
    (lookup : state.refs.lookup ptr = some (.byteArray mutableRef bytes))
    (bound : index < bytes.length) (code : sptLookup fromListByteLocation state.code = some fromListByteCode)
    (clock : state.clock ≠ 0)
    (recursive : BviSem.evaluate [fromListByteCode.2]
      [BvlSem.listToValue tail, .number (Int.ofNat (index + 1)), .refPtr flag ptr]
      (BviSem.decClock 1 { state with refs := state.refs.updateEq (ptr, .byteArray mutableRef (bytes.set index byte)) }) =
        (.val [result], final)) :
    BviSem.evaluate [fromListByteCode.2]
      [BvlSem.listToValue (.number byte.toNat :: tail), .number index, .refPtr flag ptr] state =
      (.val [result], final) := by
  let input : List Value := [BvlSem.listToValue (.number byte.toNat :: tail), .number index, .refPtr flag ptr]
  let head : Bvi.Exp := .op (.memOp .el) [.op (.intOp (.const 0)) [], .var 0]
  let write : Bvi.Exp := .op (.memOp .updateByte) [head, .var 1, .var 2]
  let updated : BviSem.BviState C F := { state with refs := state.refs.updateEq (ptr, .byteArray mutableRef (bytes.set index byte)) }
  have headRun : BviSem.evaluate [head] input state = (.val [.number byte.toNat], state) := by
    apply evaluate_listElement 0 [ .number byte.toNat, BvlSem.listToValue tail ] BackendCommon.consTag 0
    · decide
    · simp [input, BvlSem.listToValue]
    · rfl
  have writeArgs : BviSem.evaluate [head, .var 1, .var 2] input state =
      (.val [.number byte.toNat, .number index, .refPtr flag ptr], state) := by
    apply evaluate_readOnly
    constructor
    · exact headRun
    simp [input, BviSem.evaluate]
  have writeRun : BviSem.evaluate [write] input state = (.val [BvlSem.unitValue], updated) := by
    dsimp [write]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, writeArgs]
    have notNegative : ¬ (index : Int) < 0 := Int.not_lt.mpr (Int.natCast_nonneg index)
    have notBound : ¬ bytes.length ≤ index := Nat.not_le_of_gt bound
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
      BviSem.toBvl, BviSem.fromBvl, lookup, notNegative, notBound, ClosSem.intToByte_toNat, updated]
  let input2 : List Value := BvlSem.unitValue :: input
  let readTail : Bvi.Exp := .op (.memOp .el) [.op (.intOp (.const 1)) [], .var 1]
  let increment : Bvi.Exp := .op (.intOp .add) [.var 2, .op (.intOp (.const 1)) []]
  have tailRun : BviSem.evaluate [readTail] input2 updated = (.val [BvlSem.listToValue tail], updated) := by
    apply evaluate_listElement 1 [.number byte.toNat, BvlSem.listToValue tail] BackendCommon.consTag 1
    · decide
    · simp [input2, input, BvlSem.listToValue]
    · rfl
  have incRun : BviSem.evaluate [increment] input2 updated = (.val [.number (Int.ofNat (index + 1))], updated) := by
    apply evaluate_increment
    simp [input2, input]
  have callArgs : BviSem.evaluate [readTail, increment, .var 3] input2 updated =
      (.val [BvlSem.listToValue tail, .number (Int.ofNat (index + 1)), .refPtr flag ptr], updated) := by
    apply evaluate_readOnly
    constructor
    · exact tailRun
    constructor
    · exact incRun
    simp [input2, input, BviSem.evaluate]
  have testRun : BviSem.evaluate [.op (.blockOp (.tagLenEq 0 0)) [.var 0]] input state =
      (.val [BvlSem.boolValue false], state) := by
    simp [input, BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
      BvlSem.doApp, BvlSem.applyBlock, BvlSem.listToValue, BviSem.fromBvl_toBvl,
      BvlSem.boolValue, BackendCommon.boolToTag]
  change BviSem.evaluate [.ifThenElse (.op (.blockOp (.tagLenEq 0 0)) [.var 0]) (.var 2)
    (.let [write] (.call 0 (some fromListByteLocation) [readTail, increment, .var 3] none))] input state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, testRun]
  change BviSem.evaluate [.let [write] (.call 0 (some fromListByteLocation) [readTail, increment, .var 3] none)] input state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, writeRun]
  change BviSem.evaluate [.call 0 (some fromListByteLocation) [readTail, increment, .var 3] none] input2 updated = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, callArgs]
  have updatedCode : sptLookup fromListByteLocation updated.code = some fromListByteCode := by simpa [updated] using code
  have nonzero : updated.clock ≠ 0 := by simpa [updated] using clock
  simp only [BvlSem.findCode, updatedCode, fromListByteCode, List.length_cons, List.length_nil, ite_true]
  simp only [Nat.zero_add, Nat.lt_one_iff, nonzero, if_false, BviSem.fixClock_evaluate]
  have recRun := recursive
  simp [fromListByteCode] at recRun
  simp [updated, recRun]

/-- Updating a finite-map entry with its existing value leaves the map unchanged. -/
theorem updateEq_existing {α β : Type} [DecidableEq α] (map : HolFiniteMapExact α β)
    (key : α) (value : β) (lookup : map.lookup key = some value) : map.updateEq (key, value) = map := by
  cases map
  simp only [HolFiniteMapExact.updateEq]
  congr 1
  funext index
  simp [FUPDATE_HOL]
  intro equal
  subst index
  exact lookup.symm

/-- The byte-list writer fills a suffix of the destination array, preserving
all untouched bytes. Untagged pending BVI evaluator and dispatcher review. -/
theorem evaluate_fromListByte {C F : Type} (newBytes before suffix : List (BitVec 8))
    (ptr : Nat) (flag mutableRef : Bool) (state : BviSem.BviState C F)
    (bound : newBytes.length ≤ suffix.length)
    (lookup : state.refs.lookup ptr = some (.byteArray mutableRef (before ++ suffix)))
    (code : sptLookup fromListByteLocation state.code = some fromListByteCode) :
    ∃ clock, BviSem.evaluate [fromListByteCode.2]
      [BvlSem.listToValue (newBytes.map (fun byte => .number byte.toNat)), .number before.length, .refPtr flag ptr]
      (BviProps.incClock clock state) =
      (.val [.refPtr flag ptr], { state with refs := state.refs.updateEq (ptr, .byteArray mutableRef (before ++ newBytes ++ suffix.drop newBytes.length)) }) := by
  induction newBytes generalizing before suffix state with
  | nil =>
    refine ⟨0, ?_⟩
    have same := updateEq_existing state.refs ptr (.byteArray mutableRef (before ++ suffix)) lookup
    simpa [BviProps.incClock, same] using evaluate_fromListByte_nil ptr flag before.length state
  | cons byte rest ih =>
    cases suffix with
    | nil => simp at bound
    | cons old suffix =>
      have restBound : rest.length ≤ suffix.length := by simp at bound; omega
      let updated : BviSem.BviState C F := { state with refs := state.refs.updateEq (ptr, .byteArray mutableRef ((before ++ old :: suffix).set before.length byte)) }
      have setEq : (before ++ old :: suffix).set before.length byte = before ++ byte :: suffix := by
        simp [List.set_append_right]
      have updatedLookup : updated.refs.lookup ptr = some (.byteArray mutableRef ((before ++ [byte]) ++ suffix)) := by
        simp [updated, setEq, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, List.append_assoc]
      have updatedCode : sptLookup fromListByteLocation updated.code = some fromListByteCode := by simpa [updated] using code
      obtain ⟨clock, recRun⟩ := ih (before ++ [byte]) suffix updated restBound updatedLookup updatedCode
      refine ⟨clock + 1, ?_⟩
      let start := BviProps.incClock (clock + 1) state
      have startLookup : start.refs.lookup ptr = some (.byteArray mutableRef (before ++ old :: suffix)) := by
        simpa [start, BviProps.incClock] using lookup
      have startCode : sptLookup fromListByteLocation start.code = some fromListByteCode := by
        simpa [start, BviProps.incClock] using code
      have nonzero : start.clock ≠ 0 := by simp [start, BviProps.incClock]
      have clockState : BviSem.decClock 1 { start with refs := start.refs.updateEq (ptr, .byteArray mutableRef ((before ++ old :: suffix).set before.length byte)) } =
          BviProps.incClock clock updated := by
        simp [start, updated, BviSem.decClock, BviProps.incClock]
      have recursive : BviSem.evaluate [fromListByteCode.2]
          [BvlSem.listToValue (rest.map (fun b => .number b.toNat)),
            .number (Int.ofNat (before.length + 1)), .refPtr flag ptr]
          (BviSem.decClock 1 { start with refs := start.refs.updateEq (ptr, .byteArray mutableRef ((before ++ old :: suffix).set before.length byte)) }) =
          (.val [.refPtr flag ptr],
            { state with refs := state.refs.updateEq (ptr, .byteArray mutableRef (before ++ (byte :: rest) ++ (old :: suffix).drop (byte :: rest).length)) }) := by
        rw [clockState]
        simpa [updated, setEq, updateEq_overwrite, List.append_assoc] using recRun
      have step := evaluate_fromListByte_cons byte (rest.map (fun b => .number b.toNat)) ptr before.length
        flag mutableRef (before ++ old :: suffix) start _ (.refPtr flag ptr)
        startLookup (by simp) startCode nonzero recursive
      simpa [start] using step

/-- Source-shaped byte-list writer result: the initial destination before the
write position is preserved and the decoded bytes fill its remaining suffix. -/
theorem evaluate_fromListByte_decoded {C F : Type} (value : Value) (newBytes bytes : List (BitVec 8))
    (ptr : Nat) (flag mutableRef : Bool) (state : BviSem.BviState C F)
    (decode : BvlSem.valueToList value = some (newBytes.map (fun byte => .number byte.toNat)))
    (bound : newBytes.length ≤ bytes.length)
    (lookup : state.refs.lookup ptr = some (.byteArray mutableRef bytes))
    (code : sptLookup fromListByteLocation state.code = some fromListByteCode) :
    ∃ clock, BviSem.evaluate [fromListByteCode.2]
      [value, .number (Int.ofNat (bytes.length - newBytes.length)), .refPtr flag ptr] (BviProps.incClock clock state) =
      (.val [.refPtr flag ptr], { state with refs := state.refs.updateEq (ptr, .byteArray mutableRef (bytes.take (bytes.length - newBytes.length) ++ newBytes)) }) := by
  let offset := bytes.length - newBytes.length
  have offsetBound : offset ≤ bytes.length := by simp [offset]
  have splitBytes : bytes.take offset ++ bytes.drop offset = bytes := List.take_append_drop offset bytes
  have suffixLength : (bytes.drop offset).length = newBytes.length := by
    simp [offset, List.length_drop]
    omega
  have suffixBound : newBytes.length ≤ (bytes.drop offset).length := by omega
  have splitLookup : state.refs.lookup ptr = some (.byteArray mutableRef (bytes.take offset ++ bytes.drop offset)) := by
    simpa [splitBytes] using lookup
  obtain ⟨clock, run⟩ := evaluate_fromListByte newBytes (bytes.take offset) (bytes.drop offset)
    ptr flag mutableRef state suffixBound splitLookup code
  refine ⟨clock, ?_⟩
  have noTail : (bytes.drop offset).drop newBytes.length = [] := by
    apply List.drop_eq_nil_of_le
    omega
  rw [← valueToList_inverse value _ decode]
  simpa [offset, offsetBound, noTail] using run

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

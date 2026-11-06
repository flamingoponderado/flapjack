import Flapjack.Compiler.Backend.BvlToBvi.Proofs.SumListLengthStub

/-! The byte-array concatenation runtime stub. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.SemanticPrimitivesHOL (copyArray)

/-- Concatenating an empty list returns the destination. Untagged pending
BVI evaluator and dispatcher correspondence review. -/
theorem evaluate_concatByte_nil {C F : Type} (n dst : Nat) (flag : Bool) (state : BviSem.BviState C F) :
    BviSem.evaluate [concatByteCode.2] [BvlSem.listToValue [], .number n, .refPtr flag dst] state =
      (.val [.refPtr flag dst], state) := by
  have testRun : BviSem.evaluate [.op (.blockOp (.tagLenEq 0 0)) [.var 0]]
      [BvlSem.listToValue [], .number n, .refPtr flag dst] state = (.val [BvlSem.boolValue true], state) := by
    simp [BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
      BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, BvlSem.listToValue,
      BviSem.fromBvl_toBvl, BvlSem.boolValue, BackendCommon.boolToTag, BackendCommon.nilTag]
  change BviSem.evaluate [.ifThenElse (.op (.blockOp (.tagLenEq 0 0)) [.var 0]) (.var 2) _] _ _ = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, testRun]
  change BviSem.evaluate [.var 2] [BvlSem.listToValue [], .number n, .refPtr flag dst] state = _
  simp [BviSem.evaluate]

/-- One concatenation iteration copies the head array into the destination
and recurses on the tail. Untagged pending evaluator and dispatcher review. -/
theorem evaluate_concatByte_cons {C F : Type} (src dst n : Nat) (flag dstFlag : Bool)
    (bytes dest copied : List (BitVec 8)) (tail : List Value)
    (state final : BviSem.BviState C F) (result : Value)
    (srcLookup : state.refs.lookup src = some (.byteArray true bytes))
    (dstLookup : state.refs.lookup dst = some (.byteArray dstFlag dest))
    (copy : copyArray (bytes, 0) (bytes.length : Int) (some (dest, (n : Int))) = some copied)
    (code : sptLookup concatByteLocation state.code = some concatByteCode)
    (clock : state.clock ≠ 0)
    (recursive : BviSem.evaluate [concatByteCode.2]
      [BvlSem.listToValue tail, .number (Int.ofNat (n + bytes.length)), .refPtr flag dst]
      (BviSem.decClock 1 { state with refs := state.refs.updateEq (dst, .byteArray dstFlag copied) }) =
        (.val [result], final)) :
    BviSem.evaluate [concatByteCode.2]
      [BvlSem.listToValue (.refPtr true src :: tail), .number n, .refPtr flag dst] state = (.val [result], final) := by
  let env : List Value := [BvlSem.listToValue (.refPtr true src :: tail), .number n, .refPtr flag dst]
  let head : Bvi.Exp := .op (.memOp .el) [.op (.intOp (.const 0)) [], .var 0]
  let len : Bvi.Exp := .op (.memOp .lengthByte) [.var 0]
  let write : Bvi.Exp := .op (.memOp (.copyByte false)) [.var 3, .var 4, .var 0, .op (.intOp (.const 0)) [], .var 1]
  let env2 := .refPtr true src :: env
  let env3 := .number (Int.ofNat bytes.length) :: env2
  let updated : BviSem.BviState C F := { state with refs := state.refs.updateEq (dst, .byteArray dstFlag copied) }
  let env4 := BvlSem.unitValue :: env3
  let readTail : Bvi.Exp := .op (.memOp .el) [.op (.intOp (.const 1)) [], .var 3]
  let add : Bvi.Exp := .op (.intOp .add) [.var 4, .var 1]
  have headRun : BviSem.evaluate [head] env state = (.val [.refPtr true src], state) := by
    apply evaluate_listElement 0 [.refPtr true src, BvlSem.listToValue tail] BackendCommon.consTag 0
    · decide
    · simp [env, BvlSem.listToValue]
    · rfl
  have lenRun : BviSem.evaluate [len] env2 state = (.val [.number bytes.length], state) := by
    simp [len, env2, BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
      BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, BviSem.fromBvl, srcLookup]
  have writeArgs : BviSem.evaluate [.var 3, .var 4, .var 0, .op (.intOp (.const 0)) [], .var 1] env3 state =
      (.val [.number n, .refPtr flag dst, .number bytes.length, .number 0, .refPtr true src], state) := by
    apply evaluate_readOnly
    simp [env3, env2, env, BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
      BviSem.doAppAux, BackendCommon.smallEnoughInt]
  have writeRun : BviSem.evaluate [write] env3 state = (.val [BvlSem.unitValue], updated) := by
    dsimp [write]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, writeArgs]
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
      BviSem.toBvl, BviSem.fromBvl, srcLookup, dstLookup, updated]
    rw [copy]
    rfl
  have tailRun : BviSem.evaluate [readTail] env4 updated = (.val [BvlSem.listToValue tail], updated) := by
    apply evaluate_listElement 1 [.refPtr true src, BvlSem.listToValue tail] BackendCommon.consTag 3
    · decide
    · simp [env4, env3, env2, env, BvlSem.listToValue]
    · rfl
  have addRun : BviSem.evaluate [add] env4 updated = (.val [.number (Int.ofNat (n + bytes.length))], updated) := by
    have args : BviSem.evaluate [.var 4, .var 1] env4 updated = (.val [.number n, .number bytes.length], updated) := by
      apply evaluate_readOnly
      simp [env4, env3, env2, env, BviSem.evaluate]
    dsimp [add]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, args]
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
      BvlSem.applyNumeric, BvlSem.doIntApp, BviSem.fromBvl_toBvl, Int.add_comm]
  have callArgs : BviSem.evaluate [readTail, add, .var 5] env4 updated =
      (.val [BvlSem.listToValue tail, .number (Int.ofNat (n + bytes.length)), .refPtr flag dst], updated) := by
    apply evaluate_readOnly
    constructor
    · exact tailRun
    constructor
    · exact addRun
    simp [env4, env3, env2, env, BviSem.evaluate]
  have testRun : BviSem.evaluate [.op (.blockOp (.tagLenEq 0 0)) [.var 0]] env state =
      (.val [BvlSem.boolValue false], state) := by
    simp [env, BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
      BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, BvlSem.listToValue,
      BviSem.fromBvl_toBvl, BvlSem.boolValue, BackendCommon.boolToTag]
  change BviSem.evaluate [.ifThenElse (.op (.blockOp (.tagLenEq 0 0)) [.var 0]) (.var 2)
    (.let [head] (.let [len] (.let [write] (.call 0 (some concatByteLocation) [readTail, add, .var 5] none))))] env state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, testRun]
  change BviSem.evaluate [.let [head] (.let [len] (.let [write] (.call 0 (some concatByteLocation) [readTail, add, .var 5] none)))] env state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, headRun]
  change BviSem.evaluate [.let [len] (.let [write] (.call 0 (some concatByteLocation) [readTail, add, .var 5] none))] env2 state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, lenRun]
  change BviSem.evaluate [.let [write] (.call 0 (some concatByteLocation) [readTail, add, .var 5] none)] env3 state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, writeRun]
  change BviSem.evaluate [.call 0 (some concatByteLocation) [readTail, add, .var 5] none] env4 updated = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, callArgs]
  have updatedCode : sptLookup concatByteLocation updated.code = some concatByteCode := by simpa [updated] using code
  have nonzero : updated.clock ≠ 0 := by simpa [updated] using clock
  simp only [BvlSem.findCode, updatedCode, concatByteCode, List.length_cons, List.length_nil, ite_true,
    Nat.zero_add, Nat.lt_one_iff, nonzero, if_false, BviSem.fixClock_evaluate]
  have recRun := recursive
  simp [concatByteCode] at recRun
  simp [updated, recRun]

/-- Copying a whole source array into a destination suffix preserves the
destination prefix and the untouched suffix. -/
theorem copyArray_whole_into_suffix {α : Type} (bytes before suffix : List α)
    (bound : bytes.length ≤ suffix.length) :
    copyArray (bytes, 0) (bytes.length : Int) (some (before ++ suffix, (before.length : Int))) =
      some (before ++ bytes ++ suffix.drop bytes.length) := by
  have natAbs : ((before.length : Int) + (bytes.length : Int)).natAbs = before.length + bytes.length := by
    have h := Int.natAbs_of_nonneg (show 0 ≤ (before.length : Int) + (bytes.length : Int) by omega)
    omega
  simp [copyArray, natAbs, List.drop_append, bound]

/-- Concatenation fills the destination suffix with the flattened source
arrays, preserving the prefix. Untagged pending evaluator and dispatcher review. -/
theorem evaluate_concatByte {C F : Type} (ptrs : List Nat) (chunks : List (List (BitVec 8)))
    (before suffix : List (BitVec 8)) (dst : Nat) (flag : Bool) (state : BviSem.BviState C F)
    (distinct : dst ∉ ptrs)
    (lookups : ptrs.map state.refs.lookup = chunks.map (fun bytes => some (.byteArray true bytes)))
    (dstLookup : state.refs.lookup dst = some (.byteArray true (before ++ suffix)))
    (size : chunks.flatten.length = suffix.length)
    (code : sptLookup concatByteLocation state.code = some concatByteCode) :
    ∃ clock, BviSem.evaluate [concatByteCode.2]
      [BvlSem.listToValue (ptrs.map (Value.refPtr true)), .number before.length, .refPtr flag dst]
      (BviProps.incClock clock state) =
      (.val [.refPtr flag dst],
        { state with refs := state.refs.updateEq (dst, .byteArray true (before ++ chunks.flatten)) }) := by
  induction ptrs generalizing chunks before suffix state with
  | nil =>
    cases chunks with
    | cons bytes chunks => simp at lookups
    | nil =>
      have empty : suffix = [] := by simpa using size.symm
      subst suffix
      have same := updateEq_existing state.refs dst (.byteArray true before) (by simpa using dstLookup)
      refine ⟨0, ?_⟩
      simpa [BviProps.incClock, same] using evaluate_concatByte_nil before.length dst flag state
  | cons ptr ptrs ih =>
    cases chunks with
    | nil => simp at lookups
    | cons bytes chunks =>
      simp only [List.map_cons, List.cons.injEq] at lookups
      obtain ⟨srcLookup, tailLookups⟩ := lookups
      have tailDistinct : dst ∉ ptrs := by
        intro member
        exact distinct (by simp [member])
      have bound : bytes.length ≤ suffix.length := by simp at size; omega
      let copied := before ++ bytes ++ suffix.drop bytes.length
      let updated : BviSem.BviState C F := { state with refs := state.refs.updateEq (dst, .byteArray true copied) }
      have updatedDst : updated.refs.lookup dst = some (.byteArray true ((before ++ bytes) ++ suffix.drop bytes.length)) := by
        simp [updated, copied, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, List.append_assoc]
      have updatedLookups : ptrs.map updated.refs.lookup = chunks.map (fun bs => some (.byteArray true bs)) := by
        rw [← tailLookups]
        apply List.map_congr_left
        intro key member
        have ne : key ≠ dst := by intro eq; subst key; exact tailDistinct member
        simp [updated, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne]
      have updatedSize : chunks.flatten.length = (suffix.drop bytes.length).length := by
        simp [List.length_drop] at size ⊢
        omega
      have updatedCode : sptLookup concatByteLocation updated.code = some concatByteCode := by simpa [updated] using code
      obtain ⟨clock, recRun⟩ := ih chunks (before ++ bytes) (suffix.drop bytes.length) updated
        tailDistinct updatedLookups updatedDst updatedSize updatedCode
      refine ⟨clock + 1, ?_⟩
      let start := BviProps.incClock (clock + 1) state
      have startSrc : start.refs.lookup ptr = some (.byteArray true bytes) := by simpa [start, BviProps.incClock] using srcLookup
      have startDst : start.refs.lookup dst = some (.byteArray true (before ++ suffix)) := by simpa [start, BviProps.incClock] using dstLookup
      have startCode : sptLookup concatByteLocation start.code = some concatByteCode := by simpa [start, BviProps.incClock] using code
      have nonzero : start.clock ≠ 0 := by simp [start, BviProps.incClock]
      have clocks : BviSem.decClock 1 { start with refs := start.refs.updateEq (dst, .byteArray true copied) } =
          BviProps.incClock clock updated := by simp [start, updated, BviSem.decClock, BviProps.incClock]
      have recursive : BviSem.evaluate [concatByteCode.2]
          [BvlSem.listToValue (ptrs.map (Value.refPtr true)), .number (Int.ofNat (before.length + bytes.length)), .refPtr flag dst]
          (BviSem.decClock 1 { start with refs := start.refs.updateEq (dst, .byteArray true copied) }) =
          (.val [.refPtr flag dst], { state with refs := state.refs.updateEq (dst, .byteArray true (before ++ (bytes :: chunks).flatten)) }) := by
        rw [clocks]
        simpa [updated, updateEq_overwrite, List.append_assoc] using recRun
      have step := evaluate_concatByte_cons ptr dst before.length flag true bytes (before ++ suffix) copied
        (ptrs.map (Value.refPtr true)) start _ (.refPtr flag dst) startSrc startDst
        (by simpa [copied] using copyArray_whole_into_suffix bytes before suffix bound) startCode nonzero recursive
      simpa [start] using step

/-- Source-shaped form of the concatenation stub for an encoded list. -/
theorem evaluate_concatByte_decoded {C F : Type} (value : Value) (ptrs : List Nat)
    (chunks : List (List (BitVec 8))) (before suffix : List (BitVec 8))
    (dst : Nat) (flag : Bool) (state : BviSem.BviState C F)
    (decode : BvlSem.valueToList value = some (ptrs.map (Value.refPtr true)))
    (distinct : dst ∉ ptrs)
    (lookups : ptrs.map state.refs.lookup = chunks.map (fun bytes => some (.byteArray true bytes)))
    (dstLookup : state.refs.lookup dst = some (.byteArray true (before ++ suffix)))
    (size : chunks.flatten.length = suffix.length)
    (code : sptLookup concatByteLocation state.code = some concatByteCode) :
    ∃ clock, BviSem.evaluate [concatByteCode.2]
      [value, .number before.length, .refPtr flag dst] (BviProps.incClock clock state) =
      (.val [.refPtr flag dst],
        { state with refs := state.refs.updateEq (dst, .byteArray true (before ++ chunks.flatten)) }) := by
  rw [← valueToList_inverse value _ decode]
  exact evaluate_concatByte ptrs chunks before suffix dst flag state distinct lookups dstLookup size code

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

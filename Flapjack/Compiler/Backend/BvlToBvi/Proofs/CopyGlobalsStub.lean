import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileMemory

/-! Global-array copying stub used when allocating globals. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- One iteration copies the indexed global before evaluating the
continuation. Untagged pending evaluator and dispatcher review. -/
theorem evaluate_copyGlobals_iteration {C F : Type} (src dst index : Nat) (srcFlag dstFlag : Bool)
    (source dest : List Value) (value : Value) (state final : BviSem.BviState C F)
    (srcLookup : state.refs.lookup src = some (.valueArray source))
    (dstLookup : state.refs.lookup dst = some (.valueArray dest))
    (selected : source[index]? = some value) (bound : index < dest.length)
    (continuation : BviSem.evaluate
      [.ifThenElse (.op (.blockOp .equal) [.op (.intOp (.const 0)) [], .var 3]) (.var 0)
        (.call 0 (some copyGlobalsLocation) [.var 1, .var 2,
          .op (.intOp .sub) [.op (.intOp (.const 1)) [], .var 3]] none)]
      (BvlSem.unitValue :: [.refPtr dstFlag dst, .refPtr srcFlag src, .number index])
      { state with refs := state.refs.updateEq (dst, .valueArray (dest.set index value)) } =
        (.val [BvlSem.unitValue], final)) :
    BviSem.evaluate [copyGlobalsCode.2] [.refPtr dstFlag dst, .refPtr srcFlag src, .number index] state =
      (.val [BvlSem.unitValue], final) := by
  let env : List Value := [.refPtr dstFlag dst, .refPtr srcFlag src, .number index]
  let read : Bvi.Exp := .op (.memOp .el) [.var 2, .var 1]
  let write : Bvi.Exp := .op (.memOp .update) [read, .var 2, .var 0]
  let updated : BviSem.BviState C F := { state with refs := state.refs.updateEq (dst, .valueArray (dest.set index value)) }
  have readArgs : BviSem.evaluate [.var 2, .var 1] env state = (.val [.number index, .refPtr srcFlag src], state) := by
    apply evaluate_readOnly
    simp [env, BviSem.evaluate]
  have readRun : BviSem.evaluate [read] env state = (.val [value], state) := by
    dsimp [read]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, readArgs]
    have nonnegative : ¬ (index : Int) < 0 := Int.not_lt.mpr (Int.natCast_nonneg index)
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
      BviSem.toBvl, BviSem.fromBvl, srcLookup, nonnegative, selected]
  have writeArgs : BviSem.evaluate [read, .var 2, .var 0] env state =
      (.val [value, .number index, .refPtr dstFlag dst], state) := by
    apply evaluate_readOnly
    constructor
    · exact readRun
    simp [env, BviSem.evaluate]
  have writeRun : BviSem.evaluate [write] env state = (.val [BvlSem.unitValue], updated) := by
    dsimp [write]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, writeArgs]
    have nonnegative : ¬ (index : Int) < 0 := Int.not_lt.mpr (Int.natCast_nonneg index)
    have inBounds : ¬ dest.length ≤ index := Nat.not_le_of_gt bound
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
      BviSem.toBvl, BviSem.fromBvl, dstLookup, nonnegative, inBounds, updated]
  change BviSem.evaluate [.let [write] _] env state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, writeRun]
  exact continuation

/-- The stub's termination test compares its current index with zero. -/
theorem evaluate_copyGlobals_test {C F : Type} (src dst index : Nat) (srcFlag dstFlag : Bool)
    (state : BviSem.BviState C F) :
    BviSem.evaluate [.op (.blockOp .equal) [.op (.intOp (.const 0)) [], .var 3]]
      [BvlSem.unitValue, .refPtr dstFlag dst, .refPtr srcFlag src, .number index] state =
      (.val [BvlSem.boolValue (decide (index = 0))], state) := by
  let env : List Value := [BvlSem.unitValue, .refPtr dstFlag dst, .refPtr srcFlag src, .number index]
  have zeroRun : BviSem.evaluate [.op (.intOp (.const 0)) []] env state = (.val [.number 0], state) := by
    apply evaluate_smallConst
    decide
  have varRun : BviSem.evaluate [.var 3] env state = (.val [.number index], state) := by simp [env, BviSem.evaluate]
  have args := evaluate_pair _ _ env state (.number 0) (.number index) zeroRun varRun
  change BviSem.evaluate [.op (.blockOp .equal) [.op (.intOp (.const 0)) [], .var 3]] env state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, args]
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
    BvlSem.doEq, BviSem.fromBvl_toBvl]

/-- At index zero, the copying stub updates the first destination cell and
returns without a recursive call. -/
theorem evaluate_copyGlobals_zero {C F : Type} (src dst : Nat) (srcFlag dstFlag : Bool)
    (source dest : List Value) (value : Value) (state : BviSem.BviState C F)
    (srcLookup : state.refs.lookup src = some (.valueArray source))
    (dstLookup : state.refs.lookup dst = some (.valueArray dest))
    (selected : source[0]? = some value) (bound : 0 < dest.length) :
    BviSem.evaluate [copyGlobalsCode.2] [.refPtr dstFlag dst, .refPtr srcFlag src, .number 0] state =
      (.val [BvlSem.unitValue], { state with refs := state.refs.updateEq (dst, .valueArray (dest.set 0 value)) }) := by
  let updated : BviSem.BviState C F := { state with refs := state.refs.updateEq (dst, .valueArray (dest.set 0 value)) }
  apply evaluate_copyGlobals_iteration src dst 0 srcFlag dstFlag source dest value state updated srcLookup dstLookup selected bound
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, evaluate_copyGlobals_test]
  change BviSem.evaluate [.var 0] _ updated = _
  simp [BviSem.evaluate]

/-- At a positive index, the stub copies that element and recurses on its
predecessor. Untagged pending evaluator and dispatcher review. -/
theorem evaluate_copyGlobals_succ {C F : Type} (src dst index : Nat) (srcFlag dstFlag : Bool)
    (source dest : List Value) (value : Value) (state final : BviSem.BviState C F)
    (srcLookup : state.refs.lookup src = some (.valueArray source))
    (dstLookup : state.refs.lookup dst = some (.valueArray dest))
    (selected : source[index + 1]? = some value) (bound : index + 1 < dest.length)
    (code : sptLookup copyGlobalsLocation state.code = some copyGlobalsCode) (clock : state.clock ≠ 0)
    (recursive : BviSem.evaluate [copyGlobalsCode.2] [.refPtr dstFlag dst, .refPtr srcFlag src, .number index]
      (BviSem.decClock 1 { state with refs := state.refs.updateEq (dst, .valueArray (dest.set (index + 1) value)) }) =
        (.val [BvlSem.unitValue], final)) :
    BviSem.evaluate [copyGlobalsCode.2] [.refPtr dstFlag dst, .refPtr srcFlag src, .number (Int.ofNat (index + 1))] state =
      (.val [BvlSem.unitValue], final) := by
  let updated : BviSem.BviState C F := { state with refs := state.refs.updateEq (dst, .valueArray (dest.set (index + 1) value)) }
  let env : List Value := [BvlSem.unitValue, .refPtr dstFlag dst, .refPtr srcFlag src, .number (Int.ofNat (index + 1))]
  apply evaluate_copyGlobals_iteration src dst (index + 1) srcFlag dstFlag source dest value state final srcLookup dstLookup selected bound
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, evaluate_copyGlobals_test]
  change BviSem.evaluate [.call 0 (some copyGlobalsLocation) [.var 1, .var 2,
    .op (.intOp .sub) [.op (.intOp (.const 1)) [], .var 3]] none] env updated = _
  let dec : Bvi.Exp := .op (.intOp .sub) [.op (.intOp (.const 1)) [], .var 3]
  have decRun : BviSem.evaluate [dec] env updated = (.val [.number index], updated) := by
    have oneRun : BviSem.evaluate [.op (.intOp (.const 1)) []] env updated = (.val [.number 1], updated) := by
      apply evaluate_smallConst
      decide
    have indexRun : BviSem.evaluate [.var 3] env updated = (.val [.number (Int.ofNat (index + 1))], updated) := by
      simp [env, BviSem.evaluate]
    have args := evaluate_pair _ _ env updated (.number 1) (.number (Int.ofNat (index + 1))) oneRun indexRun
    dsimp [dec]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, args]
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyNumeric,
      BvlSem.doIntApp, BviSem.fromBvl_toBvl]
  have callArgs : BviSem.evaluate [.var 1, .var 2, dec] env updated =
      (.val [.refPtr dstFlag dst, .refPtr srcFlag src, .number index], updated) := by
    apply evaluate_readOnly
    constructor
    · simp [env, BviSem.evaluate]
    constructor
    · simp [env, BviSem.evaluate]
    constructor
    · exact decRun
    constructor
  change BviSem.evaluate [.call 0 (some copyGlobalsLocation) [.var 1, .var 2, dec] none] env updated = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, callArgs]
  have updatedCode : sptLookup copyGlobalsLocation updated.code = some copyGlobalsCode := by simpa [updated] using code
  have nonzero : updated.clock ≠ 0 := by simpa [updated] using clock
  simp only [BvlSem.findCode, updatedCode, copyGlobalsCode, List.length_cons, List.length_nil, ite_true,
    Nat.zero_add, Nat.lt_one_iff, nonzero, if_false, BviSem.fixClock_evaluate]
  have recRun := recursive
  simp [copyGlobalsCode] at recRun
  simp [updated, recRun]

/-- Updating the next element and then copying the preceding prefix is the
same as copying the larger prefix in one operation. -/
theorem copyGlobals_prefix_step {α : Type} (source dest : List α) (index : Nat) (value : α)
    (selected : source[index + 1]? = some value) (bound : index + 1 < dest.length) :
    source.take (index + 1) ++ (dest.set (index + 1) value).drop (index + 1) =
      source.take (index + 2) ++ dest.drop (index + 2) := by
  have dropped : (dest.drop (index + 1)).set 0 value = value :: dest.drop (index + 2) := by
    have nonempty : dest.drop (index + 1) ≠ [] := by
      intro empty
      have len := congrArg List.length empty
      simp [List.length_drop] at len
      omega
    cases h : dest.drop (index + 1) with
    | nil => exact (nonempty h).elim
    | cons head tail =>
      have rest : tail = dest.drop (index + 2) := by
        have eq := congrArg (List.drop 1) h
        simpa [List.drop_drop, Nat.add_assoc] using eq.symm
      simp [rest]
  rw [List.drop_set]
  simp only [lt_self_iff_false, ite_false, Nat.sub_self, dropped]
  have takeStep : source.take (index + 2) = source.take (index + 1) ++ [value] := by
    rw [show index + 2 = (index + 1) + 1 by omega, List.take_add_one, selected]
    rfl
  rw [takeStep]
  simp [List.append_assoc]

/-- The copy-globals stub copies the prefix through the supplied index,
leaving the remaining destination cells intact. Untagged pending evaluator
and dispatcher correspondence review. -/
theorem evaluate_copyGlobals {C F : Type} (index src dst : Nat) (srcFlag dstFlag : Bool)
    (source dest : List Value) (state : BviSem.BviState C F)
    (distinct : src ≠ dst)
    (srcLookup : state.refs.lookup src = some (.valueArray source))
    (dstLookup : state.refs.lookup dst = some (.valueArray dest))
    (srcBound : index < source.length) (dstBound : index < dest.length)
    (code : sptLookup copyGlobalsLocation state.code = some copyGlobalsCode) :
    ∃ clock, BviSem.evaluate [copyGlobalsCode.2]
      [.refPtr dstFlag dst, .refPtr srcFlag src, .number index] (BviProps.incClock clock state) =
      (.val [BvlSem.unitValue],
        { state with refs := state.refs.updateEq (dst, .valueArray (source.take (index + 1) ++ dest.drop (index + 1))) }) := by
  induction index generalizing dest state with
  | zero =>
    let value := source[0]
    have selected : source[0]? = some value := by simp [value, srcBound]
    have setEq : dest.set 0 value = source.take 1 ++ dest.drop 1 := by
      have nonempty : dest ≠ [] := by cases dest <;> simp_all
      rw [List.set_eq_take_append_cons_drop]
      simp [List.take_add_one, selected, nonempty]
    refine ⟨0, ?_⟩
    simpa [BviProps.incClock, setEq] using
      evaluate_copyGlobals_zero src dst srcFlag dstFlag source dest value state srcLookup dstLookup selected dstBound
  | succ index ih =>
    let value := source[index + 1]
    have selected : source[index + 1]? = some value := by simp [value, srcBound]
    let updated : BviSem.BviState C F := { state with refs := state.refs.updateEq (dst, .valueArray (dest.set (index + 1) value)) }
    have updatedSrc : updated.refs.lookup src = some (.valueArray source) := by
      simpa [updated, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, distinct] using srcLookup
    have updatedDst : updated.refs.lookup dst = some (.valueArray (dest.set (index + 1) value)) := by
      simp [updated, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    have updatedCode : sptLookup copyGlobalsLocation updated.code = some copyGlobalsCode := by simpa [updated] using code
    obtain ⟨clock, recRun⟩ := ih (dest.set (index + 1) value) updated updatedSrc updatedDst
      (by omega) (by simp; omega) updatedCode
    refine ⟨clock + 1, ?_⟩
    let start := BviProps.incClock (clock + 1) state
    have startSrc : start.refs.lookup src = some (.valueArray source) := by simpa [start, BviProps.incClock] using srcLookup
    have startDst : start.refs.lookup dst = some (.valueArray dest) := by simpa [start, BviProps.incClock] using dstLookup
    have startCode : sptLookup copyGlobalsLocation start.code = some copyGlobalsCode := by simpa [start, BviProps.incClock] using code
    have nonzero : start.clock ≠ 0 := by simp [start, BviProps.incClock]
    have clocks : BviSem.decClock 1 { start with refs := start.refs.updateEq (dst, .valueArray (dest.set (index + 1) value)) } =
        BviProps.incClock clock updated := by simp [start, updated, BviSem.decClock, BviProps.incClock]
    have recursive : BviSem.evaluate [copyGlobalsCode.2] [.refPtr dstFlag dst, .refPtr srcFlag src, .number index]
        (BviSem.decClock 1 { start with refs := start.refs.updateEq (dst, .valueArray (dest.set (index + 1) value)) }) =
        (.val [BvlSem.unitValue], { state with refs := state.refs.updateEq (dst, .valueArray (source.take (index + 2) ++ dest.drop (index + 2))) }) := by
      rw [clocks]
      simpa [updated, updateEq_overwrite, copyGlobals_prefix_step source dest index value selected dstBound] using recRun
    have step := evaluate_copyGlobals_succ src dst index srcFlag dstFlag source dest value start _
      startSrc startDst selected dstBound startCode nonzero recursive
    simpa [start] using step

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

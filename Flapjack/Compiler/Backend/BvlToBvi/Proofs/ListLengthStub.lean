import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileConsExtend

/-! List-length runtime stub used by BVL-to-BVI lowering. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Successful list decoding identifies the original encoded list. -/
theorem valueToList_inverse (value : Value) (values : List Value)
    (decode : BvlSem.valueToList value = some values) : BvlSem.listToValue values = value := by
  cases value with
  | block tag fields =>
    cases fields with
    | nil =>
      simp only [BvlSem.valueToList] at decode
      split at decode
      · rename_i equal
        simp only [Option.some.injEq] at decode
        subst values
        subst tag
        rfl
      · contradiction
    | cons head tail =>
      cases tail with
      | nil => simp [BvlSem.valueToList] at decode
      | cons next rest =>
        cases rest with
        | cons other rest => simp [BvlSem.valueToList] at decode
        | nil =>
          simp only [BvlSem.valueToList] at decode
          split at decode
          · rename_i equal
            cases nextDecode : BvlSem.valueToList next with
            | none => simp [nextDecode] at decode
            | some vs =>
              simp [nextDecode] at decode
              subst values
              have ih := valueToList_inverse next vs nextDecode
              subst tag
              simp [BvlSem.listToValue, ih]
          · contradiction
  | _ => simp [BvlSem.valueToList] at decode
termination_by sizeOf value

/-- The list-length stub returns the accumulator on an empty list. Untagged
pending BVI evaluator and dispatcher correspondence review. -/
theorem evaluate_listLength_nil {C F : Type} (state : BviSem.BviState C F) (n : Nat) :
    BviSem.evaluate [listLengthCode.2] [BvlSem.listToValue [], .number n] state =
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

/-- Sequential evaluation of two state-preserving expressions. -/
theorem evaluate_pair {C F : Type} (first second : Bvi.Exp) (env : List Value)
    (state : BviSem.BviState C F) (x y : Value)
    (firstRun : BviSem.evaluate [first] env state = (.val [x], state))
    (secondRun : BviSem.evaluate [second] env state = (.val [y], state)) :
    BviSem.evaluate [first, second] env state = (.val [x, y], state) := by
  change BviSem.evaluateTuple (first :: [second], env, state) = _
  rw [BviSem.evaluateCons]
  simp [BviSem.evaluateTuple, firstRun, secondRun, Flapjack.holHd]

/-- One nonempty list-length iteration, with the recursive evaluation supplied
as induction hypothesis. Untagged pending BVI evaluator and dispatcher review. -/
theorem evaluate_listLength_cons {C F : Type} (head : Value) (tail : List Value)
    (state final : BviSem.BviState C F) (n : Nat) (result : Value)
    (lookup : sptLookup listLengthLocation state.code = some listLengthCode)
    (clock : state.clock ≠ 0)
    (recursive : BviSem.evaluate [listLengthCode.2]
      [BvlSem.listToValue tail, .number (Int.ofNat (n + 1))] (BviSem.decClock 1 state) = (.val [result], final)) :
    BviSem.evaluate [listLengthCode.2] [BvlSem.listToValue (head :: tail), .number n] state =
      (.val [result], final) := by
  let env : List Value := [BvlSem.listToValue (head :: tail), .number n]
  let const1 : Bvi.Exp := .op (.intOp (.const 1)) []
  let readTail : Bvi.Exp := .op (.memOp .el) [const1, .var 0]
  let increment : Bvi.Exp := .op (.intOp .add) [.var 1, const1]
  have constRun : BviSem.evaluate [const1] env state = (.val [.number 1], state) := by
    simp [const1, BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
      BviSem.doAppAux, BackendCommon.smallEnoughInt]
  have var0 : BviSem.evaluate [.var 0] env state = (.val [BvlSem.listToValue (head :: tail)], state) := by
    simp [env, BviSem.evaluate]
  have var1 : BviSem.evaluate [.var 1] env state = (.val [.number n], state) := by
    simp [env, BviSem.evaluate]
  have readRun : BviSem.evaluate [readTail] env state = (.val [BvlSem.listToValue tail], state) := by
    have args := evaluate_pair const1 (.var 0) env state (.number 1) (BvlSem.listToValue (head :: tail)) constRun var0
    dsimp [readTail]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, args]
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
      BvlSem.listToValue, BviSem.fromBvl_toBvl]
  have incRun : BviSem.evaluate [increment] env state = (.val [.number (Int.ofNat (n + 1))], state) := by
    have args := evaluate_pair (.var 1) const1 env state (.number n) (.number 1) var1 constRun
    dsimp [increment]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, args]
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyNumeric,
      BvlSem.doIntApp, BviSem.fromBvl_toBvl, Int.add_comm]
  have argsRun := evaluate_pair readTail increment env state (BvlSem.listToValue tail)
    (.number (Int.ofNat (n + 1))) readRun incRun
  have testRun : BviSem.evaluate [.op (.blockOp (.tagLenEq 0 0)) [.var 0]] env state =
      (.val [BvlSem.boolValue false], state) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, var0]
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
      BvlSem.listToValue, BviSem.fromBvl_toBvl, BvlSem.boolValue, BackendCommon.boolToTag]
  change BviSem.evaluate [.ifThenElse (.op (.blockOp (.tagLenEq 0 0)) [.var 0]) (.var 1)
    (.call 0 (some listLengthLocation) [readTail, increment] none)] env state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, testRun]
  change BviSem.evaluate [.call 0 (some listLengthLocation) [readTail, increment] none] env state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
  simp only [BvlSem.findCode, lookup, listLengthCode, List.length_cons, List.length_nil, ite_true]
  simp only [Nat.zero_add, Nat.lt_one_iff, clock, if_false, BviSem.fixClock_evaluate]
  have recRun := recursive
  simp [listLengthCode] at recRun
  simp [recRun]

/-- The list-length stub returns the accumulator plus the decoded list length,
using a sufficient clock increment. Untagged pending BVI evaluator and
dispatcher correspondence review. -/
theorem evaluate_listLength {C F : Type} (values : List Value) (n : Nat)
    (state : BviSem.BviState C F)
    (lookup : sptLookup listLengthLocation state.code = some listLengthCode) :
    ∃ clock, BviSem.evaluate [listLengthCode.2] [BvlSem.listToValue values, .number n]
      (BviProps.incClock clock state) = (.val [.number (Int.ofNat (n + values.length))], state) := by
  induction values generalizing n with
  | nil =>
    refine ⟨0, ?_⟩
    simpa [BviProps.incClock] using evaluate_listLength_nil state n
  | cons head tail ih =>
    obtain ⟨clock, recursive⟩ := ih (n + 1)
    refine ⟨clock + 1, ?_⟩
    have code : sptLookup listLengthLocation (BviProps.incClock (clock + 1) state).code = some listLengthCode := by
      simpa [BviProps.incClock] using lookup
    have nonzero : (BviProps.incClock (clock + 1) state).clock ≠ 0 := by
      simp [BviProps.incClock]
    have clocks : BviSem.decClock 1 (BviProps.incClock (clock + 1) state) = BviProps.incClock clock state := by
      simp [BviSem.decClock, BviProps.incClock]
    have step := evaluate_listLength_cons head tail (BviProps.incClock (clock + 1) state) state n
      (.number (Int.ofNat (n + 1 + tail.length))) code nonzero (by simpa [clocks] using recursive)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step

/-- The stub computes the length of any successfully decoded BVL list. -/
theorem evaluate_listLength_decoded {C F : Type} (value : Value) (values : List Value) (n : Nat)
    (state : BviSem.BviState C F) (lookup : sptLookup listLengthLocation state.code = some listLengthCode)
    (decode : BvlSem.valueToList value = some values) :
    ∃ clock, BviSem.evaluate [listLengthCode.2] [value, .number n] (BviProps.incClock clock state) =
      (.val [.number (Int.ofNat (n + values.length))], state) := by
  rw [← valueToList_inverse value values decode]
  exact evaluate_listLength values n state lookup

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

import Flapjack.Compiler.Backend.BvlToBvi.Proofs.ListLengthStub

/-! List-to-block lowering in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Sequential evaluation of a pair, allowing the second expression to change state. -/
theorem evaluate_pair_threaded {C F : Type} (first second : Bvi.Exp) (env : List Value)
    (state next final : BviSem.BviState C F) (x y : Value)
    (firstRun : BviSem.evaluate [first] env state = (.val [x], next))
    (secondRun : BviSem.evaluate [second] env next = (.val [y], final)) :
    BviSem.evaluate [first, second] env state = (.val [x, y], final) := by
  change BviSem.evaluateTuple (first :: [second], env, state) = _
  rw [BviSem.evaluateCons]
  simp [BviSem.evaluateTuple, firstRun, secondRun, Flapjack.holHd]

/-- The generated list-length call returns the length of a decoded list.
Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem evaluate_listLength_call {C F : Type} (value : Value) (values : List Value)
    (env : List Value) (state : BviSem.BviState C F)
    (lookup : sptLookup listLengthLocation state.code = some listLengthCode)
    (decode : BvlSem.valueToList value = some values) :
    ∃ clock, BviSem.evaluate [.call 0 (some listLengthLocation)
      [.var 0, .op (.intOp (.const 0)) []] none] (value :: env) (BviProps.incClock clock state) =
      (.val [.number (Int.ofNat values.length)], state) := by
  obtain ⟨clock, stub⟩ := evaluate_listLength_decoded value values 0 state lookup decode
  refine ⟨clock + 1, ?_⟩
  let start := BviProps.incClock (clock + 1) state
  have varRun : BviSem.evaluate [.var 0] (value :: env) start = (.val [value], start) := by simp [BviSem.evaluate]
  have zeroRun : BviSem.evaluate [.op (.intOp (.const 0)) []] (value :: env) start = (.val [.number 0], start) := by
    simp [BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
      BackendCommon.smallEnoughInt]
  have argsRun := evaluate_pair (.var 0) (.op (.intOp (.const 0)) []) (value :: env) start value (.number 0) varRun zeroRun
  change BviSem.evaluate [.call 0 (some listLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none]
    (value :: env) start = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
  have code : sptLookup listLengthLocation start.code = some listLengthCode := by simpa [start, BviProps.incClock] using lookup
  have nonzero : start.clock ≠ 0 := by simp [start, BviProps.incClock]
  have clocks : BviSem.decClock 1 start = BviProps.incClock clock state := by
    simp [start, BviSem.decClock, BviProps.incClock]
  simp only [BvlSem.findCode, code, listLengthCode, List.length_cons, List.length_nil, ite_true,
    Nat.zero_add, Nat.lt_one_iff, nonzero, if_false, BviSem.fixClock_evaluate]
  have stubRun := stub
  simp [listLengthCode] at stubRun
  simp [clocks, stubRun]

/-- The generated list-to-block body computes the block using the list-length
stub. Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem evaluate_fromListBody {C F : Type} (tag : Nat) (value : Value) (values : List Value)
    (env : List Value) (state : BviSem.BviState C F)
    (lookup : sptLookup listLengthLocation state.code = some listLengthCode)
    (decode : BvlSem.valueToList value = some values) :
    ∃ clock, BviSem.evaluate [.op (.blockOp (.fromList tag))
      [.var 0, .call 0 (some listLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none]]
      (value :: env) (BviProps.incClock clock state) = (.val [.block tag values], state) := by
  obtain ⟨clock, lengthRun⟩ := evaluate_listLength_call value values env state lookup decode
  refine ⟨clock, ?_⟩
  have varRun : BviSem.evaluate [.var 0] (value :: env) (BviProps.incClock clock state) =
      (.val [value], BviProps.incClock clock state) := by simp [BviSem.evaluate]
  have argsRun : BviSem.evaluate [.var 0, .call 0 (some listLengthLocation)
        [.var 0, .op (.intOp (.const 0)) []] none] (value :: env) (BviProps.incClock clock state) =
      (.val [value, .number (Int.ofNat values.length)], state) := by
    exact evaluate_pair_threaded _ _ _ _ _ _ _ _ varRun lengthRun
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, decode]

/-- List-to-block conversion satisfies pass simulation given operand
simulation. Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_fromList {C F : Type} (tag : Nat) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.blockOp (.fromList tag)) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.blockOp (.fromList tag)) arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      cases reversed : values.reverse with
      | nil =>
        simp [BvlSem.doApp, BvlSem.applyBlock, reversed] at run
        exact (notTypeError run.1.symm).elim
      | cons value rest =>
        cases rest with
        | cons second tail =>
          simp [BvlSem.doApp, BvlSem.applyBlock, reversed] at run
          exact (notTypeError run.1.symm).elim
        | nil =>
          cases decode : BvlSem.valueToList value with
          | none =>
            simp [BvlSem.doApp, BvlSem.applyBlock, reversed, decode] at run
            exact (notTypeError run.1.symm).elim
          | some elements =>
            simp [BvlSem.doApp, BvlSem.applyBlock, reversed, decode] at run
            rcases run with ⟨rfl, rfl⟩
            have valuesEq : values = [value] := by simpa using congrArg List.reverse reversed
            rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
            have valuesLength := BvlSem.evaluate_length arguments env source middle values argsRun
            have codeLength := compileListSource_length n arguments
            rw [argsCompile] at codeLength
            have codeNonempty : argsCode ≠ [] := by intro eq; simp [eq, valuesEq] at codeLength valuesLength; omega
            have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
            have lowered : compileOp (.blockOp (.fromList tag)) argsCode =
                .let argsCode (.op (.blockOp (.fromList tag)) [.var 0,
                  .call 0 (some listLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none]) := by
              cases argsCode with
              | nil => exact (codeNonempty rfl).elim
              | cons head tail => rfl
            simp [compileListSource, compileSingSource, argsCompile, nilRight, lowered] at compiled
            rcases compiled with ⟨rfl, rfl, rfl⟩
            have shape : BvlHandle.Proofs.handleOk arguments := by simpa [BvlHandle.Proofs.handleOk] using handlers
            obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
              argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                argsCompile related sourceOk envOk installed shape global
            have stubLookup : sptLookup listLengthLocation targetNext.code = some listLengthCode := relatedNext.2.2.2.2.2.2.2.2.1
            have targetDecode : BvlSem.valueToList (adjustBv newRelocate value) =
                some (elements.map (adjustBv newRelocate)) := by
              simpa [decode] using valueToList_adjust newRelocate value
            obtain ⟨extra, bodyRun⟩ := evaluate_fromListBody tag (adjustBv newRelocate value)
              (elements.map (adjustBv newRelocate)) (env.map (adjustBv newRelocate)) targetNext stubLookup targetDecode
            have shifted := BviProps.evaluate_inv_clock argsCode (env.map (adjustBv newRelocate))
              (BviProps.incClock clock target) targetNext (.val (values.map (adjustBv newRelocate))) extra
              (by simpa [mapSimulationResult] using targetArgs) (by simp)
            rw [BviProps.incClock_add] at shifted
            refine ⟨targetNext, newRelocate, extra + clock, ?_, relatedNext, envEq, refsEq⟩
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, shifted]
            simp only [valuesEq, List.map_cons, List.map_nil, List.cons_append, List.nil_append, mapSimulationResult]
            simpa [adjustBv_block] using bodyRun

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

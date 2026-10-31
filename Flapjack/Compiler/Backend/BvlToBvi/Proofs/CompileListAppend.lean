import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileEqualConst

/-! Encoded list append in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Relocation commutes with decoding a BVL list, including decoding failure. -/
theorem valueToList_adjust (relocate : Nat → Nat) (value : Value) :
    BvlSem.valueToList (adjustBv relocate value) =
      (BvlSem.valueToList value).map (List.map (adjustBv relocate)) := by
  cases value with
  | block tag fields =>
    cases fields with
    | nil => simp [adjustBv_block, BvlSem.valueToList]
    | cons head tail =>
      cases tail with
      | nil => simp [adjustBv_block, BvlSem.valueToList]
      | cons next rest =>
        cases rest with
        | nil =>
          simp [adjustBv_block, BvlSem.valueToList, valueToList_adjust relocate next]
          split <;> simp_all
          cases BvlSem.valueToList next <;> rfl
        | cons other rest => simp [adjustBv_block, BvlSem.valueToList]
  | _ => simp [adjustBv, BvlSem.valueToList]
termination_by sizeOf value

/-- Relocating an encoded list is the encoding of its relocated elements. -/
theorem listToValue_adjust (relocate : Nat → Nat) (values : List Value) :
    adjustBv relocate (BvlSem.listToValue values) = BvlSem.listToValue (values.map (adjustBv relocate)) := by
  induction values with
  | nil => simp [BvlSem.listToValue, adjustBv_block]
  | cons value rest ih => simp [BvlSem.listToValue, adjustBv_block, ih]

/-- List append commutes with value relocation. Untagged pending BVI
 dispatcher correspondence review. -/
theorem doListAppend_target {C F : Type} (left right : Value) (xs ys : List Value)
    (relocate : Nat → Nat) (target : BviSem.BviState C F)
    (leftDecode : BvlSem.valueToList left = some xs) (rightDecode : BvlSem.valueToList right = some ys) :
    BviSem.doApp (.blockOp .listAppend) [adjustBv relocate left, adjustBv relocate right] target =
      .val (adjustBv relocate (BvlSem.listToValue (xs ++ ys)), target) := by
  have leftTarget := valueToList_adjust relocate left
  have rightTarget := valueToList_adjust relocate right
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
    BvlSem.applyBlock, BviSem.fromBvl_toBvl, leftTarget, rightTarget, leftDecode, rightDecode,
    listToValue_adjust]

/-- List append satisfies pass simulation given operand simulation. Untagged
pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_listAppend {C F : Type} (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.blockOp .listAppend) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.blockOp .listAppend) arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
      have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
      simp [compileListSource, compileSingSource, argsCompile, nilRight, compileOp] at compiled
      rcases compiled with ⟨rfl, rfl, rfl⟩
      have shape : BvlHandle.Proofs.handleOk arguments := by simpa [BvlHandle.Proofs.handleOk] using handlers
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      cases reversed : values.reverse with
      | nil =>
        simp [BvlSem.doApp, BvlSem.applyBlock, reversed] at run
        exact (notTypeError run.1.symm).elim
      | cons left tail =>
        cases tail with
        | nil =>
          simp [BvlSem.doApp, BvlSem.applyBlock, reversed] at run
          exact (notTypeError run.1.symm).elim
        | cons right rest =>
          cases rest with
          | cons third tail =>
            simp [BvlSem.doApp, BvlSem.applyBlock, reversed] at run
            exact (notTypeError run.1.symm).elim
          | nil =>
            cases leftDecode : BvlSem.valueToList left with
            | none =>
              simp [BvlSem.doApp, BvlSem.applyBlock, reversed, leftDecode] at run
              exact (notTypeError run.1.symm).elim
            | some xs =>
              cases rightDecode : BvlSem.valueToList right with
              | none =>
                simp [BvlSem.doApp, BvlSem.applyBlock, reversed, leftDecode, rightDecode] at run
                exact (notTypeError run.1.symm).elim
              | some ys =>
                simp [BvlSem.doApp, BvlSem.applyBlock, reversed, leftDecode, rightDecode] at run
                rcases run with ⟨rfl, rfl⟩
                obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
                  argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                    argsCompile related sourceOk envOk installed shape global
                refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
                rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
                simp only [mapSimulationResult]
                rw [← List.map_reverse, reversed]
                simp only [List.map_cons, List.map_nil]
                rw [doListAppend_target left right xs ys newRelocate targetNext leftDecode rightDecode]

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

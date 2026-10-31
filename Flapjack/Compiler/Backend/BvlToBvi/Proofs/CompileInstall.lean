import Flapjack.Compiler.Backend.BvlToBvi.Proofs.InstallStateRel
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileFfi

/-! Code-installation simulation for BVL-to-BVI lowering. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- BVL installation can fail only with a type error. -/
theorem doInstall_error {C F R : Type} (args : List Value) (state : BvlSem.State C F)
    (error : Flapjack.SemanticPrimitivesHOL.ErrorResult R)
    (run : BvlSem.doInstall args state = .err error) : error = .abort .typeError := by
  unfold BvlSem.doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals split at run <;> simp_all

/-- Installation satisfies pass simulation given operand simulation.
Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_install {C F : Type} (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) : simulation [.op .install arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error .install arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      cases application : BvlSem.doInstall (R := Value) values.reverse middle with
      | err error =>
        have typeError := doInstall_error values.reverse middle error application
        subst error
        simp [BvlSem.doApp, application] at run
        exact (notTypeError run.1.symm).elim
      | val pair =>
        rcases pair with ⟨result, last⟩
        obtain ⟨byteValue, wordValue, bytes, words, valuesReverse, bytesDecode, wordsDecode⟩ :=
          install_operand_shape values.reverse middle last result application
        simp [BvlSem.doApp, application] at run
        rcases run with ⟨rfl, rfl⟩
        have valuesEq : values = [wordValue, byteValue] := by simpa using congrArg List.reverse valuesReverse
        rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
        have valuesLength := BvlSem.evaluate_length arguments env source middle values argsRun
        have codeLength := compileListSource_length n arguments
        rw [argsCompile] at codeLength
        change argsCode.length = arguments.length at codeLength
        have twoArgs : argsCode.length = 2 := by simp [valuesEq] at valuesLength; omega
        have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
        simp [compileListSource, compileSingSource, argsCompile, nilRight, compileOp, twoArgs] at compiled
        rcases compiled with ⟨rfl, rfl, rfl⟩
        have shape : BvlHandle.Proofs.handleOk arguments := by simpa [BvlHandle.Proofs.handleOk] using handlers
        obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
          argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
            argsCompile related sourceOk envOk installed shape global
        have application' : BvlSem.doInstall (R := Value) [byteValue, wordValue] middle = .val (result, last) := by
          simpa [valuesReverse] using application
        obtain ⟨targetBytes, targetWords, installedTarget, decodedBytes, decodedWords, targetApplication, _, _, targetEq⟩ :=
          install_target_transfer_of_related newRelocate middle last targetNext byteValue wordValue result relatedNext application'
        have finalRel := stateRel_install_success newRelocate middle last targetNext byteValue wordValue result relatedNext application'
        rw [targetEq] at targetApplication
        have lengthCode : sptLookup listLengthLocation targetNext.code = some listLengthCode := relatedNext.2.2.2.2.2.2.2.2.1
        obtain ⟨extra, bodyRun⟩ := evaluate_installBody (adjustBv newRelocate byteValue) (adjustBv newRelocate wordValue)
          targetBytes targetWords (env.map (adjustBv newRelocate)) targetNext _ (adjustBv newRelocate result)
          (valueToBytes_adjust_some newRelocate byteValue targetBytes decodedBytes)
          (valueToWords_adjust_some newRelocate wordValue targetWords decodedWords) lengthCode targetApplication
        have shifted := BviProps.evaluate_inv_clock argsCode (env.map (adjustBv newRelocate))
          (BviProps.incClock clock target) targetNext (.val (values.map (adjustBv newRelocate))) extra
          (by simpa [mapSimulationResult] using targetArgs) (by simp)
        rw [BviProps.incClock_add] at shifted
        refine ⟨_, newRelocate, extra + clock, ?_, finalRel, envEq, refsEq⟩
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, shifted]
        simp only [mapSimulationResult, valuesEq, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
        exact bodyRun

/-- Every BVL operation satisfies pass simulation given operand simulation.
Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_op {C F : Type} (op : ClosLang.Op) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) : simulation [.op op arguments] env source := by
  cases op with
  | label index => exact simulation_label index arguments env source argsIH
  | ffi name => exact simulation_ffi name arguments env source argsIH
  | intOp op => exact simulation_intOp op arguments env source argsIH
  | wordOp op => exact simulation_wordOp op arguments env source argsIH
  | blockOp op => exact simulation_blockOp op arguments env source argsIH
  | globOp op => exact simulation_globOp op arguments env source argsIH
  | memOp op => exact simulation_memOp op arguments env source argsIH
  | install => exact simulation_install arguments env source argsIH
  | thunkOp op => exact simulation_thunkOp op arguments env source argsIH

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

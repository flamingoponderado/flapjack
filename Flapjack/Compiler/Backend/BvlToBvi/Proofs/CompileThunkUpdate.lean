import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileDynamicGlobal

/-! Thunk updates in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- The update restriction is preserved for well-formed values under heap
relocation. This is infrastructure for thunk operation simulation. -/
theorem badThunkUpdate_stateRel {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (mode : AstHOL.ThunkMode) (value : Value) (related : stateRel relocate source target)
    (ok : bvOk source.refs value) :
    BvlSem.badThunkUpdate mode (adjustBv relocate value) target.refs ↔
      BvlSem.badThunkUpdate mode value source.refs := by
  cases value with
  | refPtr flag ptr =>
    have present : source.refs.lookup ptr ≠ none := by simpa [bvOk] using ok
    cases lookup : source.refs.lookup ptr with
    | none => exact (present lookup).elim
    | some cell =>
      have targetLookup := related.1.2.2 ptr cell lookup
      cases flag <;> cases cell <;> simp [adjustRef] at targetLookup <;>
        simp [BvlSem.badThunkUpdate, BvlSem.destThunk, adjustBv, lookup, targetLookup]
  | _ => simp [BvlSem.badThunkUpdate, BvlSem.destThunk, adjustBv]

/-- Updating an unevaluated thunk preserves the pass simulation given operand
simulation. Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_updateThunk {C F : Type} (mode : AstHOL.ThunkMode) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.thunkOp (.updateThunk mode)) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.thunkOp (.updateThunk mode)) arguments env source middle error argsIH argsRun
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
        simp [BvlSem.doApp, reversed] at run
        exact (notTypeError run.1.symm).elim
      | cons first tail =>
        cases tail with
        | nil =>
          simp [BvlSem.doApp, reversed] at run
          exact (notTypeError run.1.symm).elim
        | cons value rest =>
          cases rest with
          | cons third tail =>
            simp [BvlSem.doApp, reversed] at run
            exact (notTypeError run.1.symm).elim
          | nil =>
            cases first with
            | refPtr flag ptr =>
              cases flag with
              | true =>
                simp [BvlSem.doApp, reversed] at run
                exact (notTypeError run.1.symm).elim
              | false =>
                by_cases bad : BvlSem.badThunkUpdate mode value middle.refs
                · simp [BvlSem.doApp, reversed, bad] at run
                  exact (notTypeError run.1.symm).elim
                · cases lookup : middle.refs.lookup ptr with
                  | none =>
                    simp [BvlSem.doApp, reversed, bad, lookup] at run
                    exact (notTypeError run.1.symm).elim
                  | some cell =>
                    cases cell with
                    | thunk thunkMode oldValue =>
                      cases thunkMode with
                      | evaluated =>
                        simp [BvlSem.doApp, reversed, bad, lookup] at run
                        exact (notTypeError run.1.symm).elim
                      | notEvaluated =>
                        simp [BvlSem.doApp, reversed, bad, lookup] at run
                        rcases run with ⟨rfl, rfl⟩
                        obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
                          argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                            argsCompile related sourceOk envOk installed shape global
                        have preserved := evaluateOk arguments env source (.val values) middle argsRun sourceOk envOk
                        have valueOk : bvOk middle.refs value := by
                          apply (bvOkList_iff _ _).1 preserved.2.1 value
                          have : value ∈ values.reverse := by simp [reversed]
                          simpa using this
                        have targetBad : ¬ BvlSem.badThunkUpdate mode (adjustBv newRelocate value) targetNext.refs := by
                          simpa [badThunkUpdate_stateRel newRelocate middle targetNext mode value relatedNext valueOk] using bad
                        have targetLookup := stateRel_thunk newRelocate middle targetNext ptr .notEvaluated oldValue relatedNext lookup
                        have present : middle.refs.lookup ptr ≠ none := by rw [lookup]; simp
                        have relatedWrite := stateRel_updateExisting newRelocate middle targetNext ptr
                          (.thunk mode value) relatedNext present
                        refine ⟨{ targetNext with refs := targetNext.refs.updateEq (newRelocate ptr,
                          .thunk mode (adjustBv newRelocate value)) }, newRelocate, clock, ?_, ?_, envEq, refsEq⟩
                        · rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
                          simp only [mapSimulationResult]
                          rw [← List.map_reverse, reversed]
                          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
                            BviSem.toBvl, BviSem.fromBvl, adjustBv, BvlSem.unitValue, adjustValues,
                            targetBad, targetLookup]
                        · simpa [adjustRef] using relatedWrite
                    | _ =>
                      all_goals
                        simp [BvlSem.doApp, reversed, bad, lookup] at run
                        exact (notTypeError run.1.symm).elim
            | _ =>
              all_goals
                simp [BvlSem.doApp, reversed] at run
                exact (notTypeError run.1.symm).elim

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

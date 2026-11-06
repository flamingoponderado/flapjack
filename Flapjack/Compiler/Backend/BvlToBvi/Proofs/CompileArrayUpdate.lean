import Flapjack.Compiler.Backend.BvlToBvi.Proofs.RefUpdate

/-! Array updates in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- A valid array write updates the corresponding relocated target cell.
Untagged pending BVI dispatcher correspondence review. -/
theorem doArrayUpdate_target {C F : Type} (flag : Bool) (ptr : Nat) (fields : List Value)
    (index : Int) (value : Value) (relocate : Nat → Nat) (source : BvlSem.State (Nat × C) F)
    (target : BviSem.BviState C F) (related : stateRel relocate source target)
    (lookup : source.refs.lookup ptr = some (.valueArray fields))
    (valid : ¬ (index < 0 ∨ index.toNat ≥ fields.length)) :
    BviSem.doApp (.memOp .update)
      [adjustBv relocate (.refPtr flag ptr), adjustBv relocate (.number index), adjustBv relocate value] target =
      .val (adjustBv relocate BvlSem.unitValue,
        { target with refs := target.refs.updateEq (relocate ptr, .valueArray
          ((fields.set index.toNat value).map (adjustBv relocate))) }) := by
  have targetLookup := stateRel_valueArray relocate source target ptr fields related lookup
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
    BvlSem.applyMemory, BviSem.toBvl, BviSem.fromBvl, adjustBv, BvlSem.unitValue,
    adjustValues, targetLookup, valid, List.map_set]

/-- Array writes satisfy pass simulation given the operand simulation.
Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_arrayUpdate {C F : Type} (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.memOp .update) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.memOp .update) arguments env source middle error argsIH argsRun
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
        simp [BvlSem.doApp, BvlSem.applyMemory, reversed] at run
        exact (notTypeError run.1.symm).elim
      | cons first tail =>
        cases tail with
        | nil =>
          simp [BvlSem.doApp, BvlSem.applyMemory, reversed] at run
          exact (notTypeError run.1.symm).elim
        | cons second rest =>
          cases rest with
          | nil =>
            cases first <;> cases second <;> simp [BvlSem.doApp, BvlSem.applyMemory, reversed] at run <;>
              exact (notTypeError run.1.symm).elim
          | cons value rest =>
            cases rest with
            | cons fourth tail =>
              simp [BvlSem.doApp, BvlSem.applyMemory, reversed] at run
              exact (notTypeError run.1.symm).elim
            | nil =>
              cases first with
              | refPtr flag ptr =>
                cases second with
                | number index =>
                  cases lookup : middle.refs.lookup ptr with
                  | none =>
                    simp [BvlSem.doApp, BvlSem.applyMemory, reversed, lookup] at run
                    exact (notTypeError run.1.symm).elim
                  | some cell =>
                    cases cell with
                    | valueArray fields =>
                      by_cases valid : index < 0 ∨ index.toNat ≥ fields.length
                      · simp [BvlSem.doApp, BvlSem.applyMemory, reversed, lookup, valid] at run
                        exact (notTypeError run.1.symm).elim
                      · simp [BvlSem.doApp, BvlSem.applyMemory, reversed, lookup, valid] at run
                        rcases run with ⟨rfl, rfl⟩
                        obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
                          argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                            argsCompile related sourceOk envOk installed shape global
                        have present : middle.refs.lookup ptr ≠ none := by rw [lookup]; simp
                        have relatedWrite := stateRel_updateExisting newRelocate middle targetNext ptr
                          (.valueArray (fields.set index.toNat value)) relatedNext present
                        refine ⟨{ targetNext with refs := targetNext.refs.updateEq (newRelocate ptr,
                          .valueArray ((fields.set index.toNat value).map (adjustBv newRelocate))) },
                          newRelocate, clock, ?_, ?_, envEq, refsEq⟩
                        · rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
                          simp only [mapSimulationResult]
                          rw [← List.map_reverse, reversed]
                          simp only [List.map_cons, List.map_nil]
                          rw [doArrayUpdate_target flag ptr fields index value newRelocate middle targetNext relatedNext lookup valid]
                        · simpa [adjustRef] using relatedWrite
                    | _ =>
                      all_goals
                        simp [BvlSem.doApp, BvlSem.applyMemory, reversed, lookup] at run
                        exact (notTypeError run.1.symm).elim
                | _ =>
                  all_goals
                    simp [BvlSem.doApp, BvlSem.applyMemory, reversed] at run
                    exact (notTypeError run.1.symm).elim
              | _ =>
                all_goals
                  cases second <;> simp [BvlSem.doApp, BvlSem.applyMemory, reversed] at run <;>
                    exact (notTypeError run.1.symm).elim

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

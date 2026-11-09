import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileArrayUpdate

/-! Byte-array updates in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- A valid byte write updates the corresponding relocated target cell.
Untagged pending BVI dispatcher correspondence review. -/
theorem doByteUpdate_target {C F : Type} (flag mutableRef : Bool) (ptr : Nat) (fields : List (BitVec 8))
    (index byte : Int) (byteValue : BitVec 8) (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (related : stateRel relocate source target)
    (lookup : source.refs.lookup ptr = some (.byteArray mutableRef fields))
    (valid : ¬ (index < 0 ∨ index.toNat ≥ fields.length))
    (decoded : ClosSem.intToByte byte = some byteValue) :
    BviSem.doApp (.memOp .updateByte)
      [adjustBv relocate (.refPtr flag ptr), adjustBv relocate (.number index), adjustBv relocate (.number byte)] target =
      .val (adjustBv relocate BvlSem.unitValue,
        { target with refs := target.refs.updateEq (relocate ptr, .byteArray mutableRef
          (fields.set index.toNat byteValue)) }) := by
  have targetLookup := stateRel_byteArray relocate source target mutableRef fields ptr related lookup
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
    BvlSem.applyMemory, BviSem.toBvl, BviSem.fromBvl, adjustBv, BvlSem.unitValue,
    adjustValues, targetLookup, valid, decoded]

/-- Byte-array writes satisfy pass simulation given the operand simulation.
Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_byteArrayUpdate {C F : Type} (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.memOp .updateByte) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.memOp .updateByte) arguments env source middle error argsIH argsRun
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
              cases value with
              | number byte =>
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
                      | byteArray mutableRef fields =>
                        by_cases valid : index < 0 ∨ index.toNat ≥ fields.length
                        · simp [BvlSem.doApp, BvlSem.applyMemory, reversed, lookup, valid] at run
                          exact (notTypeError run.1.symm).elim
                        · cases decoded : ClosSem.intToByte byte with
                          | none =>
                            simp [BvlSem.doApp, BvlSem.applyMemory, reversed, lookup, valid, decoded] at run
                            exact (notTypeError run.1.symm).elim
                          | some byteValue =>
                            simp [BvlSem.doApp, BvlSem.applyMemory, reversed, lookup, valid, decoded] at run
                            rcases run with ⟨rfl, rfl⟩
                            obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
                              argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                                argsCompile related sourceOk envOk installed shape global
                            have present : middle.refs.lookup ptr ≠ none := by rw [lookup]; simp
                            have relatedWrite := stateRel_updateExisting newRelocate middle targetNext ptr
                              (.byteArray mutableRef (fields.set index.toNat byteValue)) relatedNext present
                            refine ⟨{ targetNext with refs := targetNext.refs.updateEq (newRelocate ptr,
                              .byteArray mutableRef (fields.set index.toNat byteValue)) },
                              newRelocate, clock, ?_, ?_, envEq, refsEq⟩
                            · rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
                              simp only [mapSimulationResult]
                              rw [← List.map_reverse, reversed]
                              simp only [List.map_cons, List.map_nil]
                              rw [doByteUpdate_target flag mutableRef ptr fields index byte byteValue newRelocate middle targetNext relatedNext lookup valid decoded]
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

              | _ =>
                all_goals
                  cases first <;> cases second <;>
                    simp [BvlSem.doApp, BvlSem.applyMemory, reversed] at run <;>
                    exact (notTypeError run.1.symm).elim

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

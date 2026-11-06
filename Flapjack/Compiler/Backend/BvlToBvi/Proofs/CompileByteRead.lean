import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileByteUpdate

/-! Byte-array reads in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Reading a related byte array gives the same integer. Untagged pending
BVI dispatcher correspondence review. -/
theorem doByteRead_target {C F : Type} (flag mutableRef : Bool) (ptr : Nat) (fields : List (BitVec 8))
    (index : Int) (byte : BitVec 8) (relocate : Nat → Nat) (source : BvlSem.State (Nat × C) F)
    (target : BviSem.BviState C F) (related : stateRel relocate source target)
    (lookup : source.refs.lookup ptr = some (.byteArray mutableRef fields))
    (nonnegative : ¬ index < 0) (selected : fields[index.toNat]? = some byte) :
    BviSem.doApp (.memOp .derefByte)
      [adjustBv relocate (.refPtr flag ptr), adjustBv relocate (.number index)] target =
      .val (adjustBv relocate (.number byte.toNat), target) := by
  have targetLookup := stateRel_byteArray relocate source target mutableRef fields ptr related lookup
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
    BvlSem.applyMemory, BviSem.toBvl, BviSem.fromBvl, adjustBv, targetLookup, nonnegative, selected]

/-- Byte-array reads satisfy pass simulation given the operand
simulation. Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_byteRead {C F : Type} (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.memOp .derefByte) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.memOp .derefByte) arguments env source middle error argsIH argsRun
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
          | cons third tail =>
            simp [BvlSem.doApp, BvlSem.applyMemory, reversed] at run
            exact (notTypeError run.1.symm).elim
          | nil =>
            cases second with
            | number index =>
              cases first with
              | refPtr flag ptr =>
                cases lookup : middle.refs.lookup ptr with
                | none =>
                  simp [BvlSem.doApp, BvlSem.applyMemory, reversed, lookup] at run
                  exact (notTypeError run.1.symm).elim
                | some cell =>
                  cases cell with
                  | byteArray mutableRef fields =>
                    by_cases nonnegative : index < 0
                    · simp [BvlSem.doApp, BvlSem.applyMemory, reversed, lookup, nonnegative] at run
                      exact (notTypeError run.1.symm).elim
                    · cases selected : fields[index.toNat]? with
                      | none =>
                        simp [BvlSem.doApp, BvlSem.applyMemory, reversed, lookup, nonnegative, selected] at run
                        exact (notTypeError run.1.symm).elim
                      | some value =>
                        simp [BvlSem.doApp, BvlSem.applyMemory, reversed, lookup, nonnegative, selected] at run
                        rcases run with ⟨rfl, rfl⟩
                        obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
                          argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                            argsCompile related sourceOk envOk installed shape global
                        refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
                        rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
                        simp only [mapSimulationResult]
                        rw [← List.map_reverse, reversed]
                        simp only [List.map_cons, List.map_nil]
                        rw [doByteRead_target flag mutableRef ptr fields index value newRelocate middle targetNext relatedNext lookup nonnegative selected]
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
                cases first <;> simp [BvlSem.doApp, BvlSem.applyMemory, reversed] at run <;>
                  exact (notTypeError run.1.symm).elim

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

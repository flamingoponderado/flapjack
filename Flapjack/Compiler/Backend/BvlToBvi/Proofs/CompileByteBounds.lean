import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileArrayBounds

/-! Byte-array bounds checks in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Relocation preserves byte-array bounds. Untagged pending BVI dispatcher review. -/
theorem doByteBounds_target {C F : Type} (loose flag mutableRef : Bool) (ptr : Nat) (fields : List (BitVec 8))
    (index : Int) (relocate : Nat → Nat) (source : BvlSem.State (Nat × C) F)
    (target : BviSem.BviState C F) (related : stateRel relocate source target)
    (lookup : source.refs.lookup ptr = some (.byteArray mutableRef fields)) :
    BviSem.doApp (.memOp (.boundsCheckByte loose))
      [adjustBv relocate (.refPtr flag ptr), adjustBv relocate (.number index)] target =
      .val (adjustBv relocate (BvlSem.boolValue (decide (0 ≤ index ∧ if loose then index ≤ Int.ofNat fields.length else index < Int.ofNat fields.length))), target) := by
  have targetLookup := stateRel_byteArray relocate source target mutableRef fields ptr related lookup
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
    BvlSem.applyMemory, BviSem.toBvl, BviSem.fromBvl, adjustBv, adjustBv_bool, targetLookup]

/-- Byte-array bounds checks satisfy pass simulation given the operand
simulation. Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_byteBounds {C F : Type} (loose : Bool) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.memOp (.boundsCheckByte loose)) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.memOp (.boundsCheckByte loose)) arguments env source middle error argsIH argsRun
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
                    simp [BvlSem.doApp, BvlSem.applyMemory, reversed, lookup] at run
                    rcases run with ⟨rfl, rfl⟩
                    obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
                      argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                        argsCompile related sourceOk envOk installed shape global
                    refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
                    rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
                    simp only [mapSimulationResult]
                    rw [← List.map_reverse, reversed]
                    simp only [List.map_cons, List.map_nil]
                    rw [doByteBounds_target loose flag mutableRef ptr fields index newRelocate middle targetNext relatedNext lookup]
                    simp
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

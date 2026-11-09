import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileBlockBounds

/-! Reference-backed array length in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Related value-array references have the same length. Untagged pending
BVI dispatcher correspondence review. -/
theorem doArrayLength_target {C F : Type} (flag : Bool) (ptr : Nat) (values : List Value)
    (relocate : Nat → Nat) (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (related : stateRel relocate source target)
    (lookup : source.refs.lookup ptr = some (.valueArray values)) :
    BviSem.doApp (.memOp .length) [adjustBv relocate (.refPtr flag ptr)] target =
      .val (adjustBv relocate (.number values.length), target) := by
  have targetLookup := stateRel_valueArray relocate source target ptr values related lookup
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
    BvlSem.applyMemory, BviSem.toBvl, BviSem.fromBvl, adjustBv, targetLookup]

/-- Array length satisfies pass simulation given the operand simulation.
Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_arrayLength {C F : Type} (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.memOp .length) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.memOp .length) arguments env source middle error argsIH argsRun
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
      | cons value rest =>
        cases rest with
        | cons second tail =>
          simp [BvlSem.doApp, BvlSem.applyMemory, reversed] at run
          exact (notTypeError run.1.symm).elim
        | nil =>
          cases value with
          | refPtr flag ptr =>
            cases lookup : middle.refs.lookup ptr with
            | none =>
              simp [BvlSem.doApp, BvlSem.applyMemory, reversed, lookup] at run
              exact (notTypeError run.1.symm).elim
            | some cell =>
              cases cell with
              | valueArray fields =>
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
                rw [doArrayLength_target flag ptr fields newRelocate middle targetNext relatedNext lookup]
              | _ =>
                all_goals
                  simp [BvlSem.doApp, BvlSem.applyMemory, reversed, lookup] at run
                  exact (notTypeError run.1.symm).elim
          | _ =>
            all_goals
              simp [BvlSem.doApp, BvlSem.applyMemory, reversed] at run
              exact (notTypeError run.1.symm).elim


/-- Related byte-array references have the same length. Untagged pending
BVI dispatcher correspondence review. -/
theorem doByteArrayLength_target {C F : Type} (flag mutableRef : Bool) (ptr : Nat) (values : List (BitVec 8))
    (relocate : Nat → Nat) (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (related : stateRel relocate source target)
    (lookup : source.refs.lookup ptr = some (.byteArray mutableRef values)) :
    BviSem.doApp (.memOp .lengthByte) [adjustBv relocate (.refPtr flag ptr)] target =
      .val (adjustBv relocate (.number values.length), target) := by
  have targetLookup := stateRel_byteArray relocate source target mutableRef values ptr related lookup
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
    BvlSem.applyMemory, BviSem.toBvl, BviSem.fromBvl, adjustBv, targetLookup]

/-- Byte-array length satisfies pass simulation given the operand simulation.
Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_byteArrayLength {C F : Type} (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.memOp .lengthByte) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.memOp .lengthByte) arguments env source middle error argsIH argsRun
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
      | cons value rest =>
        cases rest with
        | cons second tail =>
          simp [BvlSem.doApp, BvlSem.applyMemory, reversed] at run
          exact (notTypeError run.1.symm).elim
        | nil =>
          cases value with
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
                rw [doByteArrayLength_target flag mutableRef ptr fields newRelocate middle targetNext relatedNext lookup]
              | _ =>
                all_goals
                  simp [BvlSem.doApp, BvlSem.applyMemory, reversed, lookup] at run
                  exact (notTypeError run.1.symm).elim
          | _ =>
            all_goals
              simp [BvlSem.doApp, BvlSem.applyMemory, reversed] at run
              exact (notTypeError run.1.symm).elim

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

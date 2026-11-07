import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileFromList

/-! Fixed-index block and array reads in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- A fixed-index block read commutes with relocation. Untagged pending BVI
 dispatcher correspondence review. -/
theorem doBlockElemAt_target {C F : Type} (index tag : Nat) (fields : List Value)
    (value : Value) (relocate : Nat → Nat) (target : BviSem.BviState C F)
    (selected : fields[index]? = some value) :
    BviSem.doApp (.blockOp (.elemAt index)) [adjustBv relocate (.block tag fields)] target =
      .val (adjustBv relocate value, target) := by
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
    BvlSem.applyBlock, BviSem.fromBvl_toBvl, adjustBv_block, selected]

/-- A fixed-index reference-array read commutes with relocation. Untagged
pending BVI dispatcher correspondence review. -/
theorem doArrayElemAt_target {C F : Type} (index : Nat) (flag : Bool) (ptr : Nat)
    (fields : List Value) (value : Value) (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (related : stateRel relocate source target) (lookup : source.refs.lookup ptr = some (.valueArray fields))
    (selected : fields[index]? = some value) :
    BviSem.doApp (.blockOp (.elemAt index)) [adjustBv relocate (.refPtr flag ptr)] target =
      .val (adjustBv relocate value, target) := by
  have targetLookup := stateRel_valueArray relocate source target ptr fields related lookup
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
    BvlSem.applyBlock, BviSem.toBvl, BviSem.fromBvl, adjustBv, targetLookup, selected]

/-- Fixed-index reads satisfy pass simulation given operand simulation.
Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_elemAt {C F : Type} (index : Nat) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.blockOp (.elemAt index)) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.blockOp (.elemAt index)) arguments env source middle error argsIH argsRun
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
      | cons input rest =>
        cases rest with
        | cons second tail =>
          simp [BvlSem.doApp, BvlSem.applyBlock, reversed] at run
          exact (notTypeError run.1.symm).elim
        | nil =>
          cases input with
          | block tag fields =>
            cases selected : fields[index]? with
            | none =>
              simp [BvlSem.doApp, BvlSem.applyBlock, reversed, selected] at run
              exact (notTypeError run.1.symm).elim
            | some value =>
              simp [BvlSem.doApp, BvlSem.applyBlock, reversed, selected] at run
              rcases run with ⟨rfl, rfl⟩
              obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
                argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                  argsCompile related sourceOk envOk installed shape global
              refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
              rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
              simp only [mapSimulationResult]
              rw [← List.map_reverse, reversed]
              simp only [List.map_cons, List.map_nil]
              rw [doBlockElemAt_target index tag fields value newRelocate targetNext selected]
          | refPtr flag ptr =>
            cases lookup : middle.refs.lookup ptr with
            | none =>
              simp [BvlSem.doApp, BvlSem.applyBlock, reversed, lookup] at run
              exact (notTypeError run.1.symm).elim
            | some cell =>
              cases cell with
              | valueArray fields =>
                cases selected : fields[index]? with
                | none =>
                  simp [BvlSem.doApp, BvlSem.applyBlock, reversed, lookup, selected] at run
                  exact (notTypeError run.1.symm).elim
                | some value =>
                  simp [BvlSem.doApp, BvlSem.applyBlock, reversed, lookup, selected] at run
                  rcases run with ⟨rfl, rfl⟩
                  obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
                    argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                      argsCompile related sourceOk envOk installed shape global
                  refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
                  rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
                  simp only [mapSimulationResult]
                  rw [← List.map_reverse, reversed]
                  simp only [List.map_cons, List.map_nil]
                  rw [doArrayElemAt_target index flag ptr fields value newRelocate middle targetNext relatedNext lookup selected]
              | _ =>
                all_goals
                  simp [BvlSem.doApp, BvlSem.applyBlock, reversed, lookup] at run
                  exact (notTypeError run.1.symm).elim
          | _ =>
            all_goals
              simp [BvlSem.doApp, BvlSem.applyBlock, reversed] at run
              exact (notTypeError run.1.symm).elim

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

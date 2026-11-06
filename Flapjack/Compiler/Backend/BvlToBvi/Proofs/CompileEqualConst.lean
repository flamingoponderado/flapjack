import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileEquality

/-! Constant equality in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- A successful constant comparison is preserved by relocation. Untagged
pending BVI dispatcher correspondence review. -/
theorem doEqualConst_target {C F : Type} (part : ClosLang.ConstPart) (value result : Value)
    (relocate : Nat → Nat) (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (related : stateRel relocate source target)
    (run : BvlSem.applyBlock (.equalConst part) [value] source = some (result, source)) :
    BviSem.doApp (.blockOp (.equalConst part)) [adjustBv relocate value] target =
      .val (adjustBv relocate result, target) := by
  cases part with
  | con tag fields => cases value <;> simp [BvlSem.applyBlock] at run
  | int number =>
    cases value with
    | number actual =>
      simp [BvlSem.applyBlock] at run
      subst result
      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
        BvlSem.applyBlock, BviSem.fromBvl_toBvl, adjustBv, adjustBv_bool]
    | _ => simp [BvlSem.applyBlock] at run
  | w64 number =>
    cases value with
    | word64 actual =>
      simp [BvlSem.applyBlock] at run
      subst result
      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
        BvlSem.applyBlock, BviSem.fromBvl_toBvl, adjustBv, adjustBv_bool]
    | _ => simp [BvlSem.applyBlock] at run
  | str text =>
    cases value with
    | refPtr flag ptr =>
      cases lookup : source.refs.lookup ptr with
      | none => simp [BvlSem.applyBlock, lookup] at run
      | some cell =>
        cases cell with
        | byteArray mutableRef bytes =>
          cases mutableRef with
          | false => simp [BvlSem.applyBlock, lookup] at run
          | true =>
            simp [BvlSem.applyBlock, lookup] at run
            subst result
            have targetLookup := stateRel_byteArray relocate source target true bytes ptr related lookup
            simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
              BvlSem.applyBlock, BviSem.toBvl, BviSem.fromBvl, adjustBv, adjustBv_bool, targetLookup]
        | _ => simp [BvlSem.applyBlock, lookup] at run
    | _ => simp [BvlSem.applyBlock] at run

/-- Constant comparison satisfies pass simulation given operand simulation.
Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_equalConst {C F : Type} (part : ClosLang.ConstPart) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.blockOp (.equalConst part)) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.blockOp (.equalConst part)) arguments env source middle error argsIH argsRun
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
        cases part <;> simp [BvlSem.doApp, BvlSem.applyBlock, reversed] at run <;>
          exact (notTypeError run.1.symm).elim
      | cons value rest =>
        cases rest with
        | cons second tail =>
          cases part <;> simp [BvlSem.doApp, BvlSem.applyBlock, reversed] at run <;>
            exact (notTypeError run.1.symm).elim
        | nil =>
          cases application : BvlSem.applyBlock (.equalConst part) [value] middle with
          | none =>
            simp [BvlSem.doApp, reversed, application] at run
            exact (notTypeError run.1.symm).elim
          | some pair =>
            rcases pair with ⟨result, last⟩
            have unchanged : last = middle := by
              cases part <;> cases value <;> simp [BvlSem.applyBlock] at application <;>
                repeat' first | split at application | contradiction
              all_goals simp_all
            subst last
            simp [BvlSem.doApp, reversed, application] at run
            rcases run with ⟨rfl, rfl⟩
            obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
              argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                argsCompile related sourceOk envOk installed shape global
            refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
            simp only [mapSimulationResult]
            rw [← List.map_reverse, reversed]
            simp only [List.map_cons, List.map_nil]
            rw [doEqualConst_target part value result newRelocate middle targetNext relatedNext application]

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

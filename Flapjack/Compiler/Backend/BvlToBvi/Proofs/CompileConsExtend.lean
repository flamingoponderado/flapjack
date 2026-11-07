import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileListAppend

/-! Block extension in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Block extension commutes with relocation, including failed bounds and
shape checks. The returned source and target state components are omitted. -/
theorem consExtend_adjust {C F D E : Type} (tag : Nat) (args : List Value) (relocate : Nat → Nat)
    (source : BvlSem.State C F) (target : BvlSem.State D E) :
    (BvlSem.applyBlock (.consExtend tag) (args.map (adjustBv relocate)) target).map Prod.fst =
      ((BvlSem.applyBlock (.consExtend tag) args source).map Prod.fst).map (adjustBv relocate) := by
  cases args with
  | nil => simp [BvlSem.applyBlock]
  | cons first args =>
    cases args with
    | nil => cases first <;> simp [BvlSem.applyBlock, adjustBv, adjustBv_block]
    | cons second args =>
      cases args with
      | nil => cases first <;> cases second <;> simp [BvlSem.applyBlock, adjustBv, adjustBv_block]
      | cons third args =>
        cases args with
        | nil => cases first <;> cases second <;> cases third <;> simp [BvlSem.applyBlock, adjustBv, adjustBv_block]
        | cons fourth rest =>
          cases first <;> cases second <;> cases third <;> cases fourth <;>
            simp [BvlSem.applyBlock, adjustBv, adjustBv_block, List.map_append,
              List.map_drop, List.map_take, apply_ite]
          split <;> omega

/-- Successful block extension leaves its state unchanged. -/
theorem consExtend_state {C F : Type} (tag : Nat) (args : List Value)
    (source next : BvlSem.State C F) (value : Value)
    (run : BvlSem.applyBlock (.consExtend tag) args source = some (value, next)) : next = source := by
  unfold BvlSem.applyBlock at run
  repeat' first | split at run | contradiction
  all_goals simp_all

/-- Successful block extension is preserved by relocation. Untagged pending
BVI dispatcher correspondence review. -/
theorem doConsExtend_target {C F : Type} (tag : Nat) (args : List Value) (result : Value)
    (relocate : Nat → Nat) (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (run : BvlSem.applyBlock (.consExtend tag) args source = some (result, source)) :
    BviSem.doApp (.blockOp (.consExtend tag)) (args.map (adjustBv relocate)) target =
      .val (adjustBv relocate result, target) := by
  have adjusted := consExtend_adjust tag args relocate source (BviSem.toBvl target)
  rw [run] at adjusted
  simp only [Option.map_some] at adjusted
  cases targetRun : BvlSem.applyBlock (.consExtend tag) (args.map (adjustBv relocate)) (BviSem.toBvl target) with
  | none => simp [targetRun] at adjusted
  | some pair =>
    obtain ⟨value, next⟩ := pair
    have unchanged := consExtend_state tag _ _ _ value targetRun
    subst next
    simp [targetRun] at adjusted
    subst value
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
      targetRun, BviSem.fromBvl_toBvl]

/-- Block extension satisfies pass simulation given operand simulation.
Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_consExtend {C F : Type} (tag : Nat) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.blockOp (.consExtend tag)) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.blockOp (.consExtend tag)) arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
      have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
      simp [compileListSource, compileSingSource, argsCompile, nilRight, compileOp] at compiled
      rcases compiled with ⟨rfl, rfl, rfl⟩
      have shape : BvlHandle.Proofs.handleOk arguments := by simpa [BvlHandle.Proofs.handleOk] using handlers
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      cases application : BvlSem.applyBlock (.consExtend tag) values.reverse middle with
      | none =>
        simp [BvlSem.doApp, application] at run
        exact (notTypeError run.1.symm).elim
      | some pair =>
        rcases pair with ⟨result, last⟩
        have unchanged := consExtend_state tag values.reverse middle last result application
        subst last
        simp [BvlSem.doApp, application] at run
        rcases run with ⟨rfl, rfl⟩
        obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
          argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
            argsCompile related sourceOk envOk installed shape global
        refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
        simp only [mapSimulationResult]
        rw [← List.map_reverse, doConsExtend_target tag values.reverse result newRelocate middle targetNext application]
        simp

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

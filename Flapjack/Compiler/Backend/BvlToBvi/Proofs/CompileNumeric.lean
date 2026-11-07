import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileInt

/-! Integer-operation relocation for BVL-to-BVI. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Integer primitives commute with value relocation, including failed
type checks and the source's Boolean results. This is a Flapjack helper. -/
theorem doIntApp_adjust (op : ClosLang.IntOp) (values : List Value) (relocate : Nat → Nat) :
    BvlSem.doIntApp op (values.map (adjustBv relocate)) =
      (BvlSem.doIntApp op values).map (adjustBv relocate) := by
  cases values with
  | nil => cases op <;> simp [BvlSem.doIntApp, adjustBv]
  | cons first rest =>
    cases rest with
    | nil => cases op <;> cases first <;> simp [BvlSem.doIntApp, adjustBv, adjustBv_bool]
    | cons second rest =>
      cases rest with
      | nil => cases op <;> cases first <;> cases second <;>
          simp [BvlSem.doIntApp, adjustBv, adjustBv_bool, apply_ite]
      | cons third rest => cases op <;> simp [BvlSem.doIntApp]

/-- Non-constant integer operations delegate to the BVL numeric dispatcher
and leave the target state unchanged. Untagged pending BVI dispatcher review. -/
theorem doIntApp_target {C F : Type} (op : ClosLang.IntOp) (values : List Value)
    (relocate : Nat → Nat) (state : BviSem.BviState C F)
    (notConst : ∀ n, op ≠ .const n) :
    BviSem.doApp (.intOp op) (values.map (adjustBv relocate)) state =
      match BvlSem.doIntApp op values with
      | none => .err (.abort .typeError)
      | some value => .val (adjustBv relocate value, state) := by
  have adjusted := doIntApp_adjust op values relocate
  cases sourceRun : BvlSem.doIntApp op values <;> cases op <;>
    simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
      BvlSem.doApp, BvlSem.applyNumeric, BviSem.fromBvl_toBvl]

/-- Non-constant integer operations preserve evaluation under the operand
simulation. Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_intOp_nonconst {C F : Type} (op : ClosLang.IntOp)
    (arguments : List Bvl.Exp) (env : List Value) (source : BvlSem.State (Nat × C) F)
    (notConst : ∀ n, op ≠ .const n) (argsIH : simulation arguments env source) :
    simulation [.op (.intOp op) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.intOp op) arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
      have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
      have lowered : compileOp (.intOp op) argsCode = .op (.intOp op) argsCode := by
        cases op <;> simp_all [compileOp]
      simp [compileListSource, compileSingSource, argsCompile, nilRight, lowered] at compiled
      rcases compiled with ⟨rfl, rfl, rfl⟩
      have shape : BvlHandle.Proofs.handleOk arguments := by simpa [BvlHandle.Proofs.handleOk] using handlers
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      cases numeric : BvlSem.doIntApp op values.reverse with
      | none =>
        simp [BvlSem.doApp, BvlSem.applyNumeric, numeric] at run
        exact (notTypeError run.1.symm).elim
      | some value =>
        simp [BvlSem.doApp, BvlSem.applyNumeric, numeric] at run
        rcases run with ⟨rfl, rfl⟩
        obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
          argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
            argsCompile related sourceOk envOk installed shape global
        refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
        simp only [mapSimulationResult]
        have targetNumeric := doIntApp_target op values.reverse newRelocate targetNext notConst
        rw [numeric] at targetNumeric
        simp only at targetNumeric
        rw [← List.map_reverse, targetNumeric]
        rfl

/-- All integer operations satisfy the BVL-to-BVI simulation given the
operand simulation. Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_intOp {C F : Type} (op : ClosLang.IntOp)
    (arguments : List Bvl.Exp) (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.intOp op) arguments] env source := by
  cases op with
  | const value => exact simulation_const value arguments env source argsIH
  | _ => apply simulation_intOp_nonconst _ arguments env source <;> simp_all

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

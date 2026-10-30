import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileNumeric

/-! Word-operation relocation for BVL-to-BVI. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Word primitives commute with relocation, including byte decoding and
floating-point results. This is Flapjack infrastructure. -/
theorem doWordApp_adjust (op : ClosLang.WordOp) (values : List Value) (relocate : Nat → Nat) :
    BvlSem.doWordApp op (values.map (adjustBv relocate)) =
      (BvlSem.doWordApp op values).map (adjustBv relocate) := by
  cases values with
  | nil => cases op <;> simp [BvlSem.doWordApp, BvlSem.doWordAppIntegral]
  | cons first rest =>
    cases rest with
    | nil =>
      cases op <;> cases first <;>
        try simp [BvlSem.doWordApp, BvlSem.doWordAppIntegral, adjustBv]
      all_goals try (cases ‹AstHOL.WordSize› <;> simp_all [adjustBv, ClosSem.intToByte])
      all_goals try (cases ‹Bool› <;> simp_all [adjustBv, ClosSem.intToByte])
    | cons second rest =>
      cases rest with
      | nil =>
        cases op <;> cases first <;> cases second <;>
          try simp [BvlSem.doWordApp, BvlSem.doWordAppIntegral, adjustBv, adjustBv_bool]
        all_goals try (cases ‹AstHOL.WordSize› <;> simp_all [adjustBv, ClosSem.intToByte, apply_ite])
        all_goals try (cases ‹AstHOL.Test› <;> simp_all [adjustBv_bool])
      | cons third rest =>
        cases rest with
        | nil =>
          cases op <;> try simp [BvlSem.doWordApp, BvlSem.doWordAppIntegral]
          case fpTop operation =>
            cases first <;> try simp [adjustBv]
            case word64 a =>
              cases second <;> try simp [adjustBv]
              case word64 b =>
                cases third <;> simp [adjustBv]
        | cons fourth rest => cases op <;> simp [BvlSem.doWordApp, BvlSem.doWordAppIntegral]

/-- Word operations delegate to the BVL dispatcher and leave the target
state unchanged. Untagged pending BVI dispatcher correspondence review. -/
theorem doWordApp_target {C F : Type} (op : ClosLang.WordOp) (values : List Value)
    (relocate : Nat → Nat) (state : BviSem.BviState C F) :
    BviSem.doApp (.wordOp op) (values.map (adjustBv relocate)) state =
      match BvlSem.doWordApp op values with
      | none => .err (.abort .typeError)
      | some value => .val (adjustBv relocate value, state) := by
  have adjusted := doWordApp_adjust op values relocate
  cases sourceRun : BvlSem.doWordApp op values <;>
    simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
      BvlSem.doApp, BvlSem.applyNumeric, BviSem.fromBvl_toBvl]

/-- Word operations preserve evaluation under the operand simulation.
Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_wordOp {C F : Type} (op : ClosLang.WordOp)
    (arguments : List Bvl.Exp) (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.wordOp op) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.wordOp op) arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
      have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
      simp [compileListSource, compileSingSource, argsCompile, nilRight, compileOp] at compiled
      rcases compiled with ⟨rfl, rfl, rfl⟩
      have shape : BvlHandle.Proofs.handleOk arguments := by simpa [BvlHandle.Proofs.handleOk] using handlers
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      cases numeric : BvlSem.doWordApp op values.reverse with
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
        have targetNumeric := doWordApp_target op values.reverse newRelocate targetNext
        rw [numeric] at targetNumeric
        simp only at targetNumeric
        rw [← List.map_reverse, targetNumeric]
        rfl

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

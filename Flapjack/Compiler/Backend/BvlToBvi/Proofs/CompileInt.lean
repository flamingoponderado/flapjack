module

public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileOpError

@[expose] public section

/-! Integer-constant lowering for BVL-to-BVI. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

namespace CompileIntCarrier
/-- Canonical BVI reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end CompileIntCarrier

/-- Compiling an integer evaluates to that integer without changing the BVI state. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_int_thm"
  (fmap_as_finite_support := [refs])]
theorem evaluate_compileInt {C F : Type} (value : Int) (env : List Value)
    (state : BviSem.BviState C F) :
    BviSem.evaluate [compileInt value] env state = (.val [.number value], state) := by
  by_cases small : -268435457 ≤ value ∧ value ≤ 268435457
  · simp [compileInt, small, BviSem.evaluate, BviSem.fixClock, BviSem.doApp,
      BviSem.doAppFallback, BviSem.doAppAux, BackendCommon.smallEnoughInt]
  · simp [compileInt, small, BviSem.evaluate, BviSem.fixClock, BviSem.doApp,
      BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
      BvlSem.doBuildConst, BvlSem.doBuild, BvlSem.doPart, BviSem.fromBvl, BviSem.toBvl]

/-- Integer-constant lowering preserves evaluation for any operand list;
nonempty successful operand lists are source type errors. Untagged until
BVI evaluator correspondence is reviewed. -/
theorem simulation_const {C F : Type} (value : Int) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.intOp (.const value)) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.intOp (.const value)) arguments env source middle error argsIH argsRun
    | val values =>
      have length := BvlSem.evaluate_length arguments env source middle values argsRun
      cases arguments with
      | nil =>
        intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
        simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyNumeric, BvlSem.doIntApp] at run
        rcases run with ⟨rfl, rfl⟩
        simp [compileListSource, compileSingSource, compileOp, smartAppend] at compiled
        rcases compiled with ⟨rfl, rfl, rfl⟩
        refine ⟨target, relocate, 0, ?_, related, rfl, ?_⟩
        · simpa [BviProps.incClock, mapSimulationResult, adjustBv] using
            evaluate_compileInt value (env.map (adjustBv relocate)) target
        · intro key present
          rfl
      | cons first rest =>
        intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
        have nonempty : values ≠ [] := by intro eq; simp [eq] at length
        have reversed : values.reverse ≠ [] := by simpa using nonempty
        rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
        cases h : values.reverse with
        | nil => exact (reversed h).elim
        | cons firstValue restValues =>
          simp [h, BvlSem.doApp, BvlSem.applyNumeric, BvlSem.doIntApp] at run
          exact (notTypeError run.1.symm).elim

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

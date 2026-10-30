import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileWord

/-! Label-operation simulation for BVL-to-BVI. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- A nullary label operation returns the relocated code pointer whenever
the source code entry exists. Untagged pending BVI evaluator review. -/
theorem simulation_label_empty {C F : Type} (label : Nat) (env : List Value)
    (source : BvlSem.State (Nat × C) F) : simulation [.op (.label label) []] env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  cases lookup : sptLookup label source.code with
  | none =>
    simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, lookup] at run
    exact (notTypeError run.1.symm).elim
  | some pair =>
    rcases pair with ⟨arity, body⟩
    have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, codeRel⟩ := related
    obtain ⟨name, compiledCode⟩ := codeRel label arity body lookup
    rcases bodyCompile : compileSingSource name body with ⟨converted, auxCode, finalName⟩
    simp only [bodyCompile] at compiledCode
    have targetLookup := compiledCode.1
    simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, lookup] at run
    rcases run with ⟨rfl, rfl⟩
    simp [compileListSource, compileSingSource, compileOp, smartAppend] at compiled
    rcases compiled with ⟨rfl, rfl, rfl⟩
    refine ⟨target, relocate, 0, ?_, related, rfl, ?_⟩
    · simp [BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
        BviSem.doAppAux, BviProps.incClock, targetLookup, mapSimulationResult, adjustBv]
    · intro key present
      rfl

/-- Label operations satisfy the pass simulation given their operand-list
simulation. Untagged pending BVI evaluator review. -/
theorem simulation_label {C F : Type} (label : Nat) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) : simulation [.op (.label label) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.label label) arguments env source middle error argsIH argsRun
    | val values =>
      have length := BvlSem.evaluate_length arguments env source middle values argsRun
      cases arguments with
      | nil => exact simulation_label_empty label env source
      | cons first rest =>
        intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
        have nonempty : values ≠ [] := by intro eq; simp [eq] at length
        have reversed : values.reverse ≠ [] := by simpa using nonempty
        rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
        cases h : values.reverse with
        | nil => exact (reversed h).elim
        | cons firstValue restValues =>
          simp [h, BvlSem.doApp] at run
          exact (notTypeError run.1.symm).elim

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

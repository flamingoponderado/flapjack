module

public import Flapjack.Compiler.Backend.FlatToClos.Proofs.IntegerExpressions

@[expose] public section

/-! Simulation of tests which reject every successful argument list. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- Every primitive test compiles to a closure operation applied to its arguments. -/
theorem compile_test_op (trace : BackendCommon.Tra) (test : Test) (typ : PrimType) :
    ∃ targetOp, ∀ xs, compileOp trace (.src (.test test typ)) xs = .op trace targetOp xs := by
  cases test <;> cases typ <;> try (rename_i size; cases size)
  all_goals exact ⟨_, by intro xs; rfl⟩

/-- A rejected test needs no target-operation hypothesis. -/
theorem evaluate_rejectedPrimitiveTest {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (test : Test) (typ : PrimType)
    (rejects : ∀ a b, FlatSem.doTest test typ a b = .typeError)
    (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.test test typ)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.test test typ)) args] := by
  obtain ⟨targetOp, compiled⟩ := compile_test_op trace test typ
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compileExp, destNop, compiled] at ⊢
  simp only [compile, compileExps_reverse] at argsSim
  rw [FlatSem.evaluate, ClosSem.evaluate, closFix]
  simp only [flatFix]
  cases flatRun : FlatSem.evaluate env source args.reverse with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate (compileExps names args).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argsSim ⊢
      rcases argsSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        rename_i sourceArgs targetArgs
        have resultShape : (FlatSem.applyResult next (.src (.test test typ)) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        exfalso
        apply resultShape
        cases sourceArgs.reverse with
        | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric]
        | cons first rest =>
          cases rest with
          | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric]
          | cons second rest =>
            cases rest with
            | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, rejects]
            | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric]

/-- Alternate ordering accepts string operands only. -/
theorem altCompare_rejects_nonString (cmp : Opb) (typ : PrimType) (notString : typ ≠ .strT)
    (a b : FlatSem.Value) : FlatSem.doTest (.altCompare cmp) typ a b = .typeError := by
  cases typ <;> simp_all [FlatSem.doTest]

/-- Boolean and 64-bit word ordering reject every pair of source operands. -/
theorem compare_rejects_invalid (cmp : Opb) (typ : PrimType)
    (invalid : typ = .boolT ∨ typ = .wordT .w64) (a b : FlatSem.Value) :
    FlatSem.doTest (.compare cmp) typ a b = .typeError := by
  rcases invalid with rfl | rfl <;> simp [FlatSem.doTest]

end Flapjack.Compiler.Backend.FlatToClos

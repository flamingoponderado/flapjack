module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.Equality
public import Flapjack.Compiler.Backend.SourceEval.Proofs.PrimitiveType
public import Flapjack.SemanticPrimitivesHOL.Test

@[expose] public section

/-! Primitive comparison preservation for the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- Successful primitive comparisons agree on related operands. HOL proves this
step inline in the `do_app_sim` comparison case; it has no separate HOL declaration. -/
theorem doTest_simulation (es : EvalOracleState) (test : Test) (typ : PrimType) (x y x' y' : Value) (b : Bool)
    (run : doTest test typ x y = .val b) (left : ValueRel es x x') (right : ValueRel es y y') :
    doTest test typ x' y' = .val b := by
  cases test with
  | equal =>
    have sameX := (valueRel_checkType es x x' typ left).1
    have sameY := (valueRel_checkType es y y' typ right).1
    cases typ with
    | float64T =>
      cases left <;> cases right <;> simp_all [doTest, checkType]
    | _ =>
      simp only [doTest] at run ⊢
      rw [← sameX, ← sameY]
      split at run <;> simp_all
      exact (doEq_simulation es).1 x y x' y' b ⟨run, left, right⟩
  | compare cmp =>
    cases left <;> cases right <;> cases typ <;> simp_all [doTest]
  | altCompare cmp =>
    cases left <;> cases right <;> cases typ <;> simp_all [doTest]


end Flapjack.Compiler.Backend.SourceEval.Proofs

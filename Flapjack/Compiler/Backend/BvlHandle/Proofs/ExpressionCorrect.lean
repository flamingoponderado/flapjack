import Flapjack.Compiler.Backend.BvlHandle.Proofs.CompileCases
import Flapjack.Compiler.Backend.BvlHandle.Proofs.SimplifyFull
import Flapjack.Compiler.Backend.BvlHandle.Proofs.ConstantComposition
import Flapjack.Compiler.Backend.BvlConst.Proofs.Simulation

/-! End-to-end expression preservation for the executed BVL handler stage. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Flapjack.Compiler.Backend.BvlSem

/-- The constant, handler-simplification, and handler-compilation pipeline
preserves every non-type-error BVL expression evaluation. This remains
untagged pending review of the underlying evaluator and its HOL carriers. -/
theorem evaluate_compileExpression {C F : Type} (limit : Nat) (expression : Bvl.Exp)
    (env : List Value) (state final : State C F)
    (result : SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluate [expression] env state = (result, final))
    (notType : result ≠ .err (.abort .typeError)) :
    evaluate [compileExpression limit env.length expression] env state = (result, final) := by
  have folded : evaluate [BvlConst.compileSing [] expression] env state = (result, final) := by
    exact BvlConst.Proofs.evaluate_compileSing expression env state final result run notType
  have simplified : evaluate [handleSimp (BvlConst.compileSing [] expression)] env state = (result, final) := by
    rw [evaluate_handleSimp, folded]
  have safe : (evaluate [handleSimp (BvlConst.compileSing [] expression)] env state).1 ≠
      .err (.abort .typeError) := by simp [simplified, notType]
  have correct := compileSingCorrect_all limit (handleSimp (BvlConst.compileSing [] expression))
    C F env env [] state (envRel_refl _ env) safe
  simpa [compileExpression, simplified] using correct.1

/-- The production expression compiler returns a preserving result for any
initial fuel, including when the bounded traversal retries. -/
theorem evaluate_compileExpFuel {C F : Type} (fuel limit : Nat) (expression : Bvl.Exp)
    (env : List Value) (state final : State C F)
    (result : SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluate [expression] env state = (result, final))
    (notType : result ≠ .err (.abort .typeError)) :
    ∃ output, compileExpFuel fuel limit env.length expression = some output ∧
      evaluate [output] env state = (result, final) :=
  ⟨compileExpression limit env.length expression,
    compileExpFuel_eq_source fuel limit env.length expression,
    evaluate_compileExpression limit expression env state final result run notType⟩

/-- The executable entry point preserves expression evaluation when
sequence splitting is disabled. -/
theorem evaluate_compileAnyFuel_noSplit {C F : Type} (fuel limit : Nat) (expression : Bvl.Exp)
    (env : List Value) (state final : State C F)
    (result : SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluate [expression] env state = (result, final))
    (notType : result ≠ .err (.abort .typeError)) :
    ∃ output, compileAnyFuel fuel false limit env.length expression = some output ∧
      evaluate [output] env state = (result, final) := by
  refine ⟨compileExpression limit env.length expression, ?_,
    evaluate_compileExpression limit expression env state final result run notType⟩
  simp [compileAnyFuel_eq_source]

end Flapjack.Compiler.Backend.BvlHandle.Proofs

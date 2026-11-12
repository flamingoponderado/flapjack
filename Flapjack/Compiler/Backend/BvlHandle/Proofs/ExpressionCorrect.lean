module

public import Flapjack.Compiler.Backend.BvlHandle.Proofs.CompileCases
public import Flapjack.Compiler.Backend.BvlHandle.Proofs.SimplifyFull
public import Flapjack.Compiler.Backend.BvlHandle.Proofs.ConstantComposition
public import Flapjack.Compiler.Backend.BvlConst.Proofs.Simulation
public import Flapjack.Compiler.Backend.BvlHandle.SourceCompile

@[expose] public section


/-! End-to-end expression preservation for the executed BVL handler stage. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Flapjack.Compiler.Backend.BvlSem

namespace ExpressionCorrectCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
    (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end ExpressionCorrectCarrier

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
    simpa [BvlConst.compileExp_eq, BvlSem.evaluateTuple] using
      BvlConst.Proofs.evaluate_compileSing expression env state final result ⟨run, notType⟩
  have simplified : evaluate [handleSimp (BvlConst.compileSing [] expression)] env state = (result, final) := by
    rw [evaluate_handleSimp, folded]
  have safe : (evaluate [handleSimp (BvlConst.compileSing [] expression)] env state).1 ≠
      .err (.abort .typeError) := by simp [simplified, notType]
  have correct := compileSingCorrect_all limit (handleSimp (BvlConst.compileSing [] expression))
    C F env env [] state (envRel_refl _ env) safe
  simpa [compileExpression, simplified] using correct.1

/-- The source expression compiler preserves every non-type-error evaluation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "compile_correct" 478
  (fmap_as_finite_support := [refs])]
theorem compileExpression_correct {C F : Type} (x : Bvl.Exp) (env : List Value)
    (s1 : Flapjack.Compiler.Backend.BvlSem.State C F)
    (res : SemanticPrimitivesHOL.Result (List Value) Value)
    (s2 : Flapjack.Compiler.Backend.BvlSem.State C F) (k l : Nat)
    (premises : evaluateTuple ([x], env, s1) = (res, s2) ∧
      res ≠ .err (.abort .typeError) ∧ k = env.length) :
    evaluateTuple ([compileExp l k x], env, s1) = (res, s2) := by
  rcases premises with ⟨run, safe, rfl⟩
  exact evaluate_compileExpression l x env s1 s2 res run safe

end Flapjack.Compiler.Backend.BvlHandle.Proofs

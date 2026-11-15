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
  simp only [evaluateTuple] at run ⊢
  have folded : evaluate [BvlConst.compileSing [] x] env s1 = (res, s2) := by
    simpa [BvlConst.compileExp_eq, BvlSem.evaluateTuple] using
      BvlConst.Proofs.evaluate_compileSing x env s1 s2 res ⟨run, safe⟩
  have simplified : evaluate [handleSimp (BvlConst.compileSing [] x)] env s1 = (res, s2) := by
    rw [evaluate_handleSimp, folded]
  have simplifiedSafe : (evaluate [handleSimp (BvlConst.compileSing [] x)] env s1).1 ≠
      .err (.abort .typeError) := by simp [simplified, safe]
  have correct := compileSingCorrect_all l (handleSimp (BvlConst.compileSing [] x))
    C F env env [] s1 (envRel_refl _ env) simplifiedSafe
  simpa [compileExp, compileExpression, simplified] using correct.1

end Flapjack.Compiler.Backend.BvlHandle.Proofs

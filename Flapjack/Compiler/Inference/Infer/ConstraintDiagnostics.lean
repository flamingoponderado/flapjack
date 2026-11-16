module

public import Flapjack.Compiler.Inference.Infer.Constraint
public import Flapjack.Compiler.Inference.Infer.Diagnostics

@[expose] public section

/-! Executable rendering for a failed well-formed unification constraint. -/
namespace Flapjack.Compiler.Inference.Infer.Constraint
open Flapjack.Compiler.Inference.Unify Flapjack.Compiler.Inference.Infer.HOLState
  Flapjack.Compiler.Inference.Infer.Operations Flapjack.Compiler.Inference.Infer.Diagnostics
  Flapjack.Translator.Monadic.MonadBase Flapjack.HOL.Transfer.Fmsp
  Flapjack.Basis.Pure.MlString Flapjack.Misc.Location

/-- The located executable mismatch renderer wraps the exact bytes of the
    source-shaped mismatch message in the compiler's diagnostic framing. -/
private theorem renderMismatchMessage (input : List HolChar) (loc : Locs) (env : Env) (a b : InferT) :
    renderTypeMismatch input (.located loc (.typeMismatchEnv env.infT a b)) =
      some ((ofString "### ERROR: type error\n").explode ++
        (mismatchMessage ⟨some loc, env.infT⟩ a b).explode ++
        (ofString " at ").explode ++ sourceLocation input (some loc) ++
        (ofString "\nProgram exited with nonzero exit code.\n").explode) := by
  simpa [mismatchMessage] using renderTypeMismatch_message input loc env.infT a b

/-- For well-formed substitutions, a located executable constraint either
    returns the same updated state as the source-shaped model or produces an
    error whose mismatch renderer uses the model's message. This does not
    establish the compiler's framing, location printer, or dispatcher against HOL. -/
theorem locatedConstraintCorresponds (fuel : Nat) (a b : InferT) (s : State)
    (loc : Locs) (env : Env) (input : List HolChar) (hw : cwfs s.subst) :
    match cunifyModel s.subst a b with
    | none =>
      let left := tWalkstar (sp2fm s.subst) a
      let right := tWalkstar (sp2fm s.subst) b
      Core.withLoc loc env (Core.constrain fuel a b) s =
        .error (.located loc (.typeMismatchEnv env.infT left right)) ∧
      addConstraintModel ⟨some loc, env.infT⟩ a b (ofExecutable s) =
        (.failure (some loc, mismatchMessage ⟨some loc, env.infT⟩ left right), ofExecutable s) ∧
      renderTypeMismatch input (.located loc (.typeMismatchEnv env.infT left right)) =
        some ((ofString "### ERROR: type error\n").explode ++
          (mismatchMessage ⟨some loc, env.infT⟩ left right).explode ++
          (ofString " at ").explode ++ sourceLocation input (some loc) ++
          (ofString "\nProgram exited with nonzero exit code.\n").explode)
    | some subst =>
      Core.withLoc loc env (Core.constrain fuel a b) s = .ok ((), { s with subst }) ∧
      addConstraintModel ⟨some loc, env.infT⟩ a b (ofExecutable s) =
        (.success (), ofExecutable { s with subst }) := by
  have result := constrainCorresponds fuel a b s ⟨some loc, env.infT⟩ hw
  cases found : cunifyModel s.subst a b with
  | none =>
    simp only [found] at result ⊢
    refine ⟨?_, result.2, renderMismatchMessage input loc env _ _⟩
    simp [Core.withLoc, result.1]
  | some subst =>
    simp only [found] at result ⊢
    exact ⟨by simp [Core.withLoc, result.1], result.2⟩

end Flapjack.Compiler.Inference.Infer.Constraint

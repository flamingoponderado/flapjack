module

public import Flapjack.Compiler.Inference.Infer.Constraint
public import Flapjack.Compiler.Inference.Unify.Source.Soundness

@[expose] public section

/-! Executable and source-shaped constraint-list correspondence. -/
namespace Flapjack.Compiler.Inference.Infer.Constraint
open Flapjack.Compiler.Inference.Unify Flapjack.Compiler.Inference.Infer.HOLState
  Flapjack.Translator.Monadic.MonadBase Flapjack.HOL.Transfer.Fmsp
  Flapjack.Basis.Pure.MlString

/-- Relate executable and source-shaped constraint lists on well-formed
    sparse substitutions. Executable failures discard state, so the source
    failure state is existentially retained. An executable `.mismatch` is
    related to the source internal-error message; this theorem does not claim
    that the executable renders that message. This is Flapjack correspondence
    infrastructure, not a separate HOL theorem. -/
theorem constrainManyCorresponds (fuel : Nat) (l : Operations.LocErrInfo)
    (xs ys : List InferT) (s : Infer.State) (hw : cwfs s.subst) :
    match Core.constrainMany fuel xs ys s with
    | .ok ((), out) =>
      addConstraintsModel l xs ys (ofExecutable s) = (.success (), ofExecutable out) ∧ cwfs out.subst
    | .error (.typeMismatch a b) =>
      ∃ out, addConstraintsModel l xs ys (ofExecutable s) =
        (.failure (l.loc, mismatchMessage l a b), out)
    | .error .mismatch =>
      ∃ out, addConstraintsModel l xs ys (ofExecutable s) =
        (.failure (l.loc, ofString "Internal error: Bad call to add_constraints"), out)
    | .error _ => False := by
  induction xs generalizing ys s with
  | nil =>
    cases ys with
    | nil => simpa [Core.constrainManyNil, addConstraintsModel, ret] using hw
    | cons y ys =>
      simp [Core.constrainManyNilCons, addConstraintsModel, Operations.failwith]
  | cons x xs ih =>
    cases ys with
    | nil =>
      simp [Core.constrainManyConsNil, addConstraintsModel, Operations.failwith]
    | cons y ys =>
      have head := constrainCorresponds fuel x y s l hw
      cases found : cunifyModel s.subst x y with
      | none =>
        simp only [found] at head
        obtain ⟨executable, source⟩ := head
        simp [Core.constrainManyCons, executable, addConstraintsModel,
          Flapjack.Translator.Monadic.MonadBase.bind, source]
      | some mid =>
        simp only [found] at head
        obtain ⟨executable, source⟩ := head
        have midWf : cwfs mid := (cunifyUnifierModel s.subst x y mid ⟨hw, found⟩).1
        have tail := ih ys { s with subst := mid } midWf
        simp only [Core.constrainManyCons, executable, addConstraintsModel,
          Flapjack.Translator.Monadic.MonadBase.bind, source]
        cases hs : addConstraintsModel l xs ys (ofExecutable { s with subst := mid }) with
        | mk result next =>
          cases result with
          | success value => cases value; simpa [hs, ret] using tail
          | failure error => simpa [hs] using tail

end Flapjack.Compiler.Inference.Infer.Constraint

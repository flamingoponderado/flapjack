module

public import Flapjack.Compiler.Inference.Infer.Generalise

@[expose] public section

namespace Flapjack.Compiler.Inference.InferProps.Generalise
open Flapjack.Compiler.Inference.Infer.Generalise

/-- The source-shaped finite-map generalizer preserves list length. This is
    not tagged as the HOL theorem until its generalization operation's
    finite-map input and tuple result have a supported representation tag. -/
theorem generaliseListLength (minimum next : Nat) (subst : HolFiniteMapExact Nat Nat)
    (input : List InferT) (count : Nat) (out : HolFiniteMapExact Nat Nat)
    (result : List InferT)
    (h : generaliseListMap minimum next subst input = (count, out, result)) :
    result.length = input.length := by
  induction input generalizing next subst count out result with
  | nil =>
    simp [generaliseListMap] at h
    simp [h.2.2]
  | cons t ts ih =>
    simp only [generaliseListMap] at h
    cases first : generaliseMap minimum next subst t with
    | mk headCount headRest =>
      cases headRest with
      | mk mid headType =>
        simp only [first] at h
        cases second : generaliseListMap minimum (headCount + next) mid ts with
        | mk tailCount tailRest =>
          cases tailRest with
          | mk final tailTypes =>
            simp only [second, Prod.mk.injEq] at h
            obtain ⟨_, _, rfl⟩ := h
            simpa using ih (headCount + next) mid tailCount final tailTypes second

end Flapjack.Compiler.Inference.InferProps.Generalise

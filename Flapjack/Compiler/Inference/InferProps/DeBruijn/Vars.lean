module

public import Flapjack.Compiler.Inference.Infer
public import Flapjack.Compiler.Inference.Unify.Substitution

@[expose] public section

/-! Inference-variable preservation under de Bruijn shifting. -/
namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

mutual
private theorem shiftPreservesVars (n : Nat) (t : InferT) :
    tVars (inferDeBruijnInc n t) = tVars t := by
  cases t with
  | uvar v => simp [inferDeBruijnInc]
  | varDb v => simp [inferDeBruijnInc, tVars, encodeInferT, vars]
  | app ts tc =>
    simp [tVars, inferDeBruijnInc, encodeInferT, vars, shiftListPreservesVars n ts]
termination_by sizeOf t

private theorem shiftListPreservesVars (n : Nat) (ts : List InferT) :
    vars (encodeInferTs (inferDeBruijnIncList n ts)) = vars (encodeInferTs ts) := by
  cases ts with
  | nil => simp [inferDeBruijnIncList]
  | cons t ts =>
    funext v
    simp only [inferDeBruijnIncList, encodeInferTs, vars]
    have ht := congrFun (shiftPreservesVars n t) v
    have hl := congrFun (shiftListPreservesVars n ts) v
    simp only [tVars] at ht
    rw [ht, hl]
termination_by sizeOf ts
end

/-- De Bruijn shifts leave the free unification variables unchanged. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "t_vars_inc"]
theorem tVarsInc (n : Nat) (t : InferT) :
    tVars (inferDeBruijnInc n t) = tVars t :=
  shiftPreservesVars n t

end Flapjack.Compiler.Inference.InferProps

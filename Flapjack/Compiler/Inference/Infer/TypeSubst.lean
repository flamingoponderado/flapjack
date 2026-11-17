module

public import Flapjack.Compiler.Inference.Infer

@[expose] public section

namespace Flapjack.Compiler.Inference.Infer
open Flapjack.Basis.Pure.MlString Flapjack.TypeSystemHOL

private theorem substListEqMap (s : List (MlString × InferT)) : ∀ ts,
    inferTypeSubstList s ts = ts.map (inferTypeSubst s) := by
  intro ts
  induction ts with
  | nil => simp [inferTypeSubstList]
  | cons t ts ih => simp [inferTypeSubstList, ih]

@[hol "cakeml/compiler/inference/inferScript.sml" "infer_type_subst_alt"]
theorem inferTypeSubstAlt (s : List (MlString × InferT)) (tv : MlString)
    (n : Nat) (ts : List SemanticT) (tn : Nat) :
    (inferTypeSubst s (.var tv) = (s.lookup tv).getD (.varDb 0)) ∧
    (inferTypeSubst s (.varDb n) = .varDb n) ∧
    (inferTypeSubst s (.app ts tn) = .app (ts.map (inferTypeSubst s)) tn) := by
  simp [inferTypeSubst, substListEqMap]

end Flapjack.Compiler.Inference.Infer

module

public import Flapjack.Compiler.Inference.Infer.Substitution
public import Flapjack.FiniteMap.EmptyExact

@[expose] public section

namespace Flapjack.Compiler.Inference.InferProps.Substitution.Empty
open Flapjack.Compiler.Inference.Infer.Substitution

mutual
/-- Type case of the structural induction for `inferSubstFempty`; HOL uses
    one mutual induction rather than a separately named helper. -/
private theorem emptyType (t : InferT) :
    inferSubst (HolFiniteMapExact.holEmpty : HolFiniteMapExact Nat Nat) t = t := by
  cases t with
  | varDb n => simp [inferSubst]
  | uvar n => simp [inferSubst, HolFiniteMapExact.holEmpty, HolFiniteMapExact.empty]
  | app ts name =>
    simp only [inferSubst]
    rw [emptyList ts]
termination_by sizeOf t

/-- List case of the same structural induction, without a separate HOL
    declaration. -/
private theorem emptyList (ts : List InferT) :
    ts.map (inferSubst (HolFiniteMapExact.holEmpty : HolFiniteMapExact Nat Nat)) = ts := by
  cases ts with
  | nil => rfl
  | cons t ts => simp only [List.map_cons, emptyType t, emptyList ts]
termination_by sizeOf ts
end

@[hol "cakeml/compiler/inference/inferPropsScript.sml" "infer_subst_FEMPTY"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem inferSubstFempty :
    (∀ t : InferT, inferSubst (HolFiniteMapExact.holEmpty : HolFiniteMapExact Nat Nat) t = t) ∧
    (∀ ts : List InferT,
      ts.map (inferSubst (HolFiniteMapExact.holEmpty : HolFiniteMapExact Nat Nat)) = ts) :=
  ⟨emptyType, emptyList⟩

end Flapjack.Compiler.Inference.InferProps.Substitution.Empty

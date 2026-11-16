module

public import Flapjack.Compiler.Inference.EnvRel.Relation

@[expose] public section

/-! Prerequisites for the soundness of CakeML type inference. -/
namespace Flapjack.Compiler.Inference.InferSound
open Flapjack.NamespaceHOL Flapjack.TypeSystemHOL
  Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.InferProps
  Flapjack.Compiler.Inference.EnvRel Flapjack.Basis.Pure.MlString

@[hol "cakeml/compiler/inference/proofs/inferSoundScript.sml" "lookup_var_empty"]
theorem lookupVarBindTvarEmpty (x : Ident MlString MlString) (tvs : Nat) (tenv : TypeEnv) :
    lookupVar x (bindTvar tvs .empty) tenv = lookupVar x .empty tenv := by
  by_cases h : tvs = 0 <;> cases x <;> simp [lookupVar, lookupVarE, bindTvar, tveLookup, h]

/-- Increasing the free-variable bound preserves the same approximation
    witness. This supports the source completeness proof. -/
private theorem approxBound (s : HolFiniteMapExact Nat InferT) (tvs n m : Nat)
    (t u : InferT) (h : tschemeApproxModel 0 s (n, t) (m, u)) :
    tschemeApproxModel tvs s (n, t) (m, u) := by
  obtain ⟨subst, len, checked, equal⟩ := h
  refine ⟨subst, len, ?_, equal⟩
  intro x hx
  have bound := checkTMore2.1 x n s.domain (by simpa using checked x hx) tvs
  simpa using bound

@[hol "cakeml/compiler/inference/proofs/inferSoundScript.sml" "env_rel_complete_bind"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem envRelCompleteBind (ienv : Env) (tenv : TypeEnv) (tvs : Nat)
    (h : envRelCompleteModel HolFiniteMapExact.holEmpty ienv tenv .empty) :
    envRelCompleteModel HolFiniteMapExact.holEmpty ienv tenv (bindTvar tvs .empty) := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro id n t found
  rw [lookupVarBindTvarEmpty] at found
  obtain ⟨closed, n', t', lookup, approx⟩ := h.2.2 id n t found
  refine ⟨closed, n', t', lookup, ?_⟩
  have widened := approxBound HolFiniteMapExact.holEmpty tvs n n' (unconvertT t) t' approx
  by_cases zero : tvs = 0 <;> simpa [bindTvar, numTvs, zero] using widened

end Flapjack.Compiler.Inference.InferSound

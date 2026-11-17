module

public import Flapjack.Compiler.Inference.EnvRel.Relation

@[expose] public section

/-! Prerequisites for the soundness of CakeML type inference. -/
namespace Flapjack.Compiler.Inference.InferSound
open Flapjack.NamespaceHOL Flapjack.TypeSystemHOL
  Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.InferProps
  Flapjack.Compiler.Inference.EnvRel Flapjack.Basis.Pure.MlString

/-- The half-open range of type identifiers allocated between two states. -/
@[hol "cakeml/compiler/inference/proofs/inferSoundScript.sml" "set_ids_def"]
def setIds (n1 n2 : Nat) : Set Nat := {m | n1 ≤ m ∧ m < n2}

@[hol "cakeml/compiler/inference/proofs/inferSoundScript.sml" "set_ids_eq"]
theorem setIdsEq (n1 n2 : Nat) :
    setIds n1 n2 = {m | m ∈ (List.range (n2 - n1)).map (fun x => x + n1)} := by
  funext m
  apply propext
  change (n1 ≤ m ∧ m < n2) ↔ m ∈ (List.range (n2 - n1)).map (fun x => x + n1)
  simp only [List.mem_map, List.mem_range]
  constructor
  · intro h
    exact ⟨m - n1, by omega, by omega⟩
  · rintro ⟨x, hx, rfl⟩
    omega

@[hol "cakeml/compiler/inference/proofs/inferSoundScript.sml" "set_ids_same"]
theorem setIdsSame (x : Nat) : setIds x x = ∅ := by
  funext m
  apply propext
  change (x ≤ m ∧ m < x) ↔ False
  constructor
  · rintro ⟨h1, h2⟩
    omega
  · intro h
    exact False.elim h

@[hol "cakeml/compiler/inference/proofs/inferSoundScript.sml" "set_ids_eq_union"]
theorem setIdsEqUnion (x y z : Nat) (h : x ≤ y ∧ y ≤ z) :
    setIds x z = setIds x y ∪ setIds y z := by
  funext m
  apply propext
  change (x ≤ m ∧ m < z) ↔ ((x ≤ m ∧ m < y) ∨ (y ≤ m ∧ m < z))
  omega

@[hol "cakeml/compiler/inference/proofs/inferSoundScript.sml" "set_ids_eq_union_eq"]
theorem setIdsEqUnionEq (x y z : Nat) (s : Set Nat)
    (h : x ≤ y ∧ y ≤ z ∧ s = setIds y z) :
    setIds x z = setIds x y ∪ s := by
  rw [h.2.2]
  exact setIdsEqUnion x y z ⟨h.1, h.2.1⟩

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

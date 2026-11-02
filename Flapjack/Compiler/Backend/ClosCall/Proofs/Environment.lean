import Flapjack.Compiler.Backend.Semantics.ClosProps.FreeVars
import Mathlib.Data.List.Forall2

/-! Environment relation for direct-call closure conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang ClosProps

/-- Environments of equal length are related pointwise. If their lengths
differ, only variables used by the given function bodies need corresponding
entries. The two environment element types are independent. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "env_rel_def"]
def envRel {A B : Type} (R : A → B → Prop) (env1 : List A) (env2 : List B)
    (offset : Nat) (fns : List (Nat × Exp)) : Prop :=
  if env1.length = env2.length then List.Forall₂ R env1 env2 else
    ∀ x, (∃ fn ∈ fns, freeVar (fn.1 + offset + x) fn.2) →
      ∃ (left : x < env1.length) (right : x < env2.length), R env1[x] env2[x]

private theorem forall₂_mono_members {A B : Type} {R R' : A → B → Prop}
    {xs : List A} {ys : List B} (related : List.Forall₂ R xs ys)
    (change : ∀ x ∈ xs, ∀ y ∈ ys, R x y → R' x y) : List.Forall₂ R' xs ys := by
  induction related with
  | nil => exact .nil
  | @cons x y xs ys head tail ih =>
    apply List.Forall₂.cons
    · exact change x (by simp) y (by simp) head
    · apply ih
      intro a ha b hb rel
      exact change a (by simp [ha]) b (by simp [hb]) rel

/-- Strengthening a relation on the values actually present in the two
environments preserves the direct-call environment relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "env_rel_mono"]
theorem envRel_mono {A B : Type} {R R' : A → B → Prop} {env1 : List A} {env2 : List B}
    {offset : Nat} {fns : List (Nat × Exp)}
    (change : ∀ x ∈ env1, ∀ y ∈ env2, R x y → R' x y)
    (related : envRel R env1 env2 offset fns) : envRel R' env1 env2 offset fns := by
  unfold envRel at related ⊢
  by_cases same : env1.length = env2.length
  · simp only [same, ↓reduceIte] at related ⊢
    exact forall₂_mono_members related change
  · simp only [same, ↓reduceIte] at related ⊢
    intro x used
    obtain ⟨left, right, rel⟩ := related x used
    exact ⟨left, right, change _ (List.getElem_mem left) _ (List.getElem_mem right) rel⟩

/-- Relations that agree on the values actually present induce the same
direct-call environment relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "env_rel_cong"]
theorem envRel_congr {A B : Type} {R R' : A → B → Prop} {env1 : List A} {env2 : List B}
    {offset : Nat} {fns : List (Nat × Exp)}
    (same : ∀ x ∈ env1, ∀ y ∈ env2, R x y ↔ R' x y) :
    envRel R env1 env2 offset fns ↔ envRel R' env1 env2 offset fns := by
  constructor
  · apply envRel_mono
    intro x hx y hy
    exact (same x hx y hy).mp
  · apply envRel_mono
    intro x hx y hy
    exact (same x hx y hy).mpr

/-- A used variable that is present in the source environment has a related
value at the same index in the target environment, even when the two
environments have different lengths. -/
theorem envRel_lookup {A B : Type} {R : A → B → Prop} {env1 : List A} {env2 : List B}
    {offset x : Nat} {fns : List (Nat × Exp)} {value : A}
    (related : envRel R env1 env2 offset fns)
    (used : ∃ fn ∈ fns, freeVar (fn.1 + offset + x) fn.2)
    (lookup : env1[x]? = some value) : ∃ value', env2[x]? = some value' ∧ R value value' := by
  obtain ⟨left, leftEq⟩ := List.getElem?_eq_some_iff.mp lookup
  unfold envRel at related
  by_cases same : env1.length = env2.length
  · simp only [same, ↓reduceIte] at related
    have right : x < env2.length := by omega
    refine ⟨env2[x], List.getElem?_eq_getElem right, ?_⟩
    have values := related.get left right
    change R env1[x] env2[x] at values
    simpa only [leftEq] using values
  · simp only [same, ↓reduceIte] at related
    obtain ⟨_, right, values⟩ := related x used
    refine ⟨env2[x], List.getElem?_eq_getElem right, ?_⟩
    simpa only [leftEq] using values

end Flapjack.Compiler.Backend.ClosCall

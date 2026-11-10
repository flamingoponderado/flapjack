module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.FreeVars
public import Mathlib.Data.List.Forall2

@[expose] public section

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

/-- Flapjack infrastructure for lifting a relation between members of two lists. -/
theorem forall₂_mono_members {A B : Type} {R R' : A → B → Prop}
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
theorem envRel_mono {A B : Type} {env1 : List A} {env2 : List B} {R R' : A → B → Prop}
    {offset : Nat} {fns : List (Nat × Exp)}
    (change : ∀ x y, x ∈ env1 ∧ y ∈ env2 ∧ R x y → R' x y)
    (related : envRel R env1 env2 offset fns) : envRel R' env1 env2 offset fns := by
  unfold envRel at related ⊢
  by_cases same : env1.length = env2.length
  · simp only [same, ↓reduceIte] at related ⊢
    exact forall₂_mono_members related (fun x hx y hy rel => change x y ⟨hx, hy, rel⟩)
  · simp only [same, ↓reduceIte] at related ⊢
    intro x used
    obtain ⟨left, right, rel⟩ := related x used
    exact ⟨left, right, change _ _ ⟨List.getElem_mem left, List.getElem_mem right, rel⟩⟩

/-- Relations that agree on the values actually present induce the same
direct-call environment relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "env_rel_cong"]
theorem envRel_congr {A B : Type} {R R' : A → B → Prop} {env1 : List A} {env2 : List B}
    {offset : Nat} {fns : List (Nat × Exp)}
    (same : ∀ x ∈ env1, ∀ y ∈ env2, R x y ↔ R' x y) :
    envRel R env1 env2 offset fns ↔ envRel R' env1 env2 offset fns := by
  constructor
  · apply envRel_mono
    intro x y ⟨hx, hy, rel⟩
    exact (same x hx y hy).mp rel
  · apply envRel_mono
    intro x y ⟨hx, hy, rel⟩
    exact (same x hx y hy).mpr rel

end Flapjack.Compiler.Backend.ClosCall

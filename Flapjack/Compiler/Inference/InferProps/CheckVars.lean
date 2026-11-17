module

public import Flapjack.Compiler.Inference.Unify.Vars
public import Flapjack.Compiler.Inference.Infer.EnvironmentInvariant

@[expose] public section

namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.Unify

mutual
/-- Structural induction helper for the original variable-subset theorem. -/
private theorem checkVars (t : InferT) (tvs : Nat) (uvs : Nat → Prop)
    (h : checkT tvs uvs t) : ∀ v, tVars t v → uvs v := by
  cases t with
  | varDb n =>
    intro v hv
    have hn : tVars (.varDb n) = (∅ : Set Nat) := tVarsEqn.1 n
    rw [hn] at hv
    exact hv.elim
  | uvar n =>
    intro v hv
    have hn : v = n := by
      have he := tVarsEqn.2.2 n
      rw [he] at hv
      exact hv
    subst v
    exact (checkT_uvar tvs n uvs).mp h
  | app ts tc =>
    intro v hv
    have eq := tVarsEqn.2.1 ts tc
    rw [eq] at hv
    change ∃ p : Nat → Prop, (∃ t, t ∈ ts ∧ tVars t = p) ∧ p v at hv
    obtain ⟨_, ⟨t, ht, rfl⟩, hv⟩ := hv
    exact checkList ts tvs uvs ((checkT_app tvs tc uvs ts).mp h) t ht v hv
termination_by sizeOf t

/-- List recursion used by the structural induction on inference types. -/
private theorem checkList (ts : List InferT) (tvs : Nat) (uvs : Nat → Prop)
    (h : checkTList tvs uvs ts) : ∀ t ∈ ts, ∀ v, tVars t v → uvs v := by
  cases ts with
  | nil => simp
  | cons t ts =>
    have h' := (checkTList_cons tvs uvs t ts).mp h
    intro x hx v hv
    simp only [List.mem_cons] at hx
    cases hx with
    | inl eq => subst x; exact checkVars t tvs uvs h'.1 v hv
    | inr hin => exact checkList ts tvs uvs h'.2 x hin v hv
termination_by sizeOf ts
end

@[hol "cakeml/compiler/inference/inferPropsScript.sml" "check_t_t_vars"]
theorem checkTTVars (tvs : Nat) (uvs : Nat → Prop) (t : InferT)
    (h : checkT tvs uvs t) : Set.Subset (tVars t) uvs := checkVars t tvs uvs h

end Flapjack.Compiler.Inference.InferProps


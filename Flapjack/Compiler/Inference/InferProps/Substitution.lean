module

public import Flapjack.Compiler.Inference.Infer.Substitution
public import Flapjack.Compiler.Inference.Unify.Vars
public import Flapjack.FiniteMap.DomainExact
public import Flapjack.FiniteMap.SubmapExact

@[expose] public section

namespace Flapjack.Compiler.Inference.InferProps.Substitution
open Flapjack.Compiler.Inference.Infer.Substitution
open Flapjack.Compiler.Inference.Unify

mutual
/-- Structural recursion helper for the type conjunct of `inferSubstSubmap`;
    HOL proves the combined theorem by induction rather than naming this helper. -/
private theorem typeSubmap (t : InferT) (s1 s2 : HolFiniteMapExact Nat Nat) (m : Nat)
    (sub : s1.submap s2)
    (covered : ∀ v, tVars t v → m ≤ v → s1.domain v)
    (newBound : ∀ v, s2.domain v → ¬ s1.domain v → m ≤ v) :
    inferSubst s1 t = inferSubst s2 t := by
  cases t with
  | varDb n => simp [inferSubst]
  | uvar n =>
    simp only [inferSubst]
    cases first : s1.lookup n with
    | some value => rw [sub n value first]
    | none =>
      cases second : s2.lookup n with
      | none => rfl
      | some value =>
        have hd2 : s2.domain n := by
          change s2.lookup n ≠ none
          simp [second]
        have hd1 : ¬ s1.domain n := by
          change ¬ s1.lookup n ≠ none
          simp [first]
        have hv : tVars (.uvar n) n := by rw [tVarsEqn.2.2]; rfl
        exact (hd1 (covered n hv (newBound n hd2 hd1))).elim
  | app ts name =>
    simp only [inferSubst]
    congr 1
    apply listSubmap ts s1 s2 m sub
    · intro v t ht hv hm
      apply covered v _ hm
      rw [tVarsEqn.2.1]
      exact ⟨tVars t, ⟨t, ht, rfl⟩, hv⟩
    · exact newBound
termination_by sizeOf t

/-- List recursion helper for the same mutual induction, without a separate
    HOL declaration. -/
private theorem listSubmap (ts : List InferT) (s1 s2 : HolFiniteMapExact Nat Nat) (m : Nat)
    (sub : s1.submap s2)
    (covered : ∀ v t, t ∈ ts → tVars t v → m ≤ v → s1.domain v)
    (newBound : ∀ v, s2.domain v → ¬ s1.domain v → m ≤ v) :
    ts.map (inferSubst s1) = ts.map (inferSubst s2) := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    simp only [List.map_cons, List.cons.injEq]
    constructor
    · apply typeSubmap t s1 s2 m sub
      · intro v hv hm
        exact covered v t (by simp) hv hm
      · exact newBound
    · apply listSubmap ts s1 s2 m sub
      · intro v x hx hv hm
        exact covered v x (by simp [hx]) hv hm
      · exact newBound
termination_by sizeOf ts
end

/-- The complete type and list substitution-submap result. The HOL theorem
    quantifies finite maps independently in both conjuncts; a qualifier for
    those nested binders is still needed before this can carry its HOL tag. -/
theorem inferSubstSubmap :
    (∀ (t : InferT) (s1 s2 : HolFiniteMapExact Nat Nat) (m : Nat),
      s1.submap s2 ∧
      {v | tVars t v ∧ m ≤ v} ⊆ s1.domain ∧
      (∀ v, v ∈ s2.domain \ s1.domain → m ≤ v) →
      inferSubst s1 t = inferSubst s2 t) ∧
    (∀ (ts : List InferT) (s1 s2 : HolFiniteMapExact Nat Nat) (m : Nat),
      s1.submap s2 ∧
      {v | ∃ s : Set Nat, s v ∧ s ∈ ts.map tVars ∧ m ≤ v} ⊆ s1.domain ∧
      (∀ v, v ∈ s2.domain \ s1.domain → m ≤ v) →
      ts.map (inferSubst s1) = ts.map (inferSubst s2)) := by
  constructor
  · intro t s1 s2 m ⟨sub, covered, newBound⟩
    apply typeSubmap t s1 s2 m sub
    · intro v hv hm
      exact covered ⟨hv, hm⟩
    · intro v hd2 hd1
      exact newBound v ⟨hd2, hd1⟩
  · intro ts s1 s2 m ⟨sub, covered, newBound⟩
    apply listSubmap ts s1 s2 m sub
    · intro v t ht hv hm
      exact covered ⟨tVars t, hv, List.mem_map.mpr ⟨t, ht, rfl⟩, hm⟩
    · intro v hd2 hd1
      exact newBound v ⟨hd2, hd1⟩

end Flapjack.Compiler.Inference.InferProps.Substitution

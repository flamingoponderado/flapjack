module

public import Flapjack.HOL.Unification.Walkstar.NotDomain
public import Mathlib.Logic.Relation

@[expose] public section

/-! Dependency paths expose unbound variables in normalized terms. -/
namespace Flapjack.HOL.Unification

/-- The substitution survives the canonical finite-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_tcVRVarsWalkstar_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkstarScript.sml" "TC_vR_vars_walkstar"
  (fmap_as_finite_support_parameters := [s])]
theorem tcVRVarsWalkstar {α : Type} (s : HolFiniteMapExact Nat (Term α)) (t : Term α) (u v : Nat)
    (h : wfs s ∧ vars t u ∧ Relation.TransGen (vR s) v u ∧ v ∉ s.domain) :
    vars (walkstar s t) v := by
  obtain ⟨hw, htu, path, absent⟩ := h
  have main : ∀ u, Relation.TransGen (vR s) v u →
      ∀ t : Term α, vars t u → vars (walkstar s t) v := by
    intro u p
    induction p with
    | @single u edge =>
      intro t htu
      apply walkstarVarLift s hw t u v htu
      cases found : s.lookup u with
      | none => simp [vR, found] at edge
      | some q =>
        have hvq : vars q v := by simpa [vR, found] using edge
        have hvnorm := notFdomWalkstar s v hw q absent hvq
        classical
        simp only [walkstar, dif_pos hw] at hvnorm ⊢
        rw [normalizeVar s hw u, found]
        exact hvnorm
    | @tail z u chain edge ih =>
      intro t htu
      apply walkstarVarLift s hw t u v htu
      cases found : s.lookup u with
      | none => simp [vR, found] at edge
      | some q =>
        have hzq : vars q z := by simpa [vR, found] using edge
        have hvnorm := ih q hzq
        classical
        simp only [walkstar, dif_pos hw] at hvnorm ⊢
        rw [normalizeVar s hw u, found]
        exact hvnorm
  exact main u path t htu

end Flapjack.HOL.Unification

module

public import Flapjack.HOL.Unification.Walkstar

@[expose] public section

/-! Variables outside the substitution domain survive normalization. -/
namespace Flapjack.HOL.Unification

/-- The substitution survives the canonical finite-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_notFdomWalkstar_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkstarScript.sml" "NOT_FDOM_walkstar"
  (fmap_as_finite_support_parameters := [s])]
theorem notFdomWalkstar {α : Type} (s : HolFiniteMapExact Nat (Term α)) (v : Nat)
    (hw : wfs s) : ∀ t, v ∉ s.domain → vars t v → vars (walkstar s t) v := by
  intro t hv ht
  have missing : s.lookup v = none := by
    change ¬ (s.lookup v ≠ none) at hv
    exact Classical.not_not.mp hv
  classical
  simp only [walkstar, dif_pos hw]
  induction t with
  | var u =>
    change v = u at ht
    subst u
    rw [normalizeVar s hw v, missing]
    rfl
  | pair a b iha ihb =>
    change vars a v ∨ vars b v at ht
    change vars (normalizeWF s hw a) v ∨ vars (normalizeWF s hw b) v
    rcases ht with ha | hb
    · exact Or.inl (iha ha)
    · exact Or.inr (ihb hb)
  | const c => exact ht.elim

end Flapjack.HOL.Unification

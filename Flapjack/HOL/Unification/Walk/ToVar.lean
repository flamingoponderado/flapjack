module

public import Flapjack.HOL.Unification.Walk

@[expose] public section

namespace Flapjack.HOL.Unification

/-- The canonical substitution map survives the broad-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_vwalkToVar_subst {α : Type}
    (subst : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).lookup key = subst.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).finiteSupport = subst.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst) = subst :=
  holFmapAsFiniteSupportParamWitness_vR_subst subst key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkScript.sml" "vwalk_to_var"
  (fmap_as_finite_support_parameters := [subst])]
theorem vwalkToVar {α : Type} (subst : HolFiniteMapExact Nat (Term α))
    (h : wfs subst) : ∀ v u, vwalk subst v = .var u → u ∉ subst.domain := by
  intro v
  induction v using h.induction with
  | h v ih =>
    intro u hv
    rw [vwalkEq subst h v] at hv
    cases found : subst.lookup v with
    | none =>
      simp [found] at hv
      subst u
      change ¬ (subst.lookup v ≠ none)
      exact fun hn => hn found
    | some t =>
      cases t with
      | var n =>
        simp only [found] at hv
        apply ih n ?_ u hv
        simp [vR, found, vars]
      | pair l r => simp [found] at hv
      | const c => simp [found] at hv

end Flapjack.HOL.Unification

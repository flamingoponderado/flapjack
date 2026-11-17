module

public import Flapjack.HOL.Unification.Walk

@[expose] public section

namespace Flapjack.HOL.Unification

/-- The canonical substitution map survives the broad-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_vwalkVR_subst {α : Type}
    (subst : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).lookup key = subst.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).finiteSupport = subst.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst) = subst :=
  holFmapAsFiniteSupportParamWitness_vR_subst subst key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkScript.sml" "vwalk_vR"
  (fmap_as_finite_support_parameters := [subst])]
theorem vwalkVR {α : Type} (subst : HolFiniteMapExact Nat (Term α))
    (hw : wfs subst) : ∀ v u, vars (vwalk subst v) u ∧ vwalk subst v ≠ .var v →
      Relation.TransGen (vR subst) u v := by
  intro v
  induction v using hw.induction with
  | h v ih =>
    intro u ⟨hu, hne⟩
    have eq := vwalkEq subst hw v
    cases found : subst.lookup v with
    | none =>
      simp only [found] at eq
      exact (hne eq).elim
    | some t =>
      cases t with
      | var n =>
        simp only [found] at eq
        have edge : vR subst n v := by simp [vR, found, vars]
        by_cases unchanged : vwalk subst n = .var n
        · rw [eq, unchanged] at hu
          have : u = n := hu
          subst u
          exact .single edge
        · have hu' : vars (vwalk subst n) u := eq ▸ hu
          exact .tail (ih n edge u ⟨hu', unchanged⟩) edge
      | pair left right =>
        simp only [found] at eq
        have dep : vR subst u v := by
          simp only [vR, found]
          exact eq ▸ hu
        exact .single dep
      | const c =>
        simp only [found] at eq
        rw [eq] at hu
        exact hu.elim

end Flapjack.HOL.Unification

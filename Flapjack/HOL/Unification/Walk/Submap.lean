module

public import Flapjack.HOL.Unification.Walk

@[expose] public section

namespace Flapjack.HOL.Unification

/-- The larger substitution survives the canonical map codec. -/
theorem holFmapAsFiniteSupportParamWitness_vwalkSubmap_sx {α : Type}
    (sx : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).lookup key = sx.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).finiteSupport = sx.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx) = sx :=
  holFmapAsFiniteSupportParamWitness_vR_subst sx key

/-- The smaller substitution survives the canonical map codec. -/
theorem holFmapAsFiniteSupportParamWitness_vwalkSubmap_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkScript.sml" "vwalk_SUBMAP"
  (fmap_as_finite_support_parameters := [sx, s])]
theorem vwalkSubmap {α : Type} (sx : HolFiniteMapExact Nat (Term α)) (hw : wfs sx) :
    ∀ v (s : HolFiniteMapExact Nat (Term α)), s.submap sx →
      match vwalk s v with
      | .var u => vwalk sx v = vwalk sx u
      | t => vwalk sx v = t := by
  intro v
  induction v using hw.induction with
  | h v ih =>
    intro s sub
    have hs : wfs s := wfsSubmap sx s ⟨hw, sub⟩
    have e1 := vwalkEq s hs v
    have e2 := vwalkEq sx hw v
    cases found : s.lookup v with
    | none =>
      simp only [found] at e1
      rw [e1]
    | some t =>
      have found2 := sub v t found
      cases t with
      | var u =>
        simp only [found] at e1
        simp only [found2] at e2
        have edge : vR sx u v := by simp [vR, found2, vars]
        have hrec := ih u edge s sub
        rw [e1, e2]
        exact hrec
      | pair a b =>
        simp only [found] at e1
        simp only [found2] at e2
        rw [e1, e2]
      | const c =>
        simp only [found] at e1
        simp only [found2] at e2
        rw [e1, e2]

end Flapjack.HOL.Unification

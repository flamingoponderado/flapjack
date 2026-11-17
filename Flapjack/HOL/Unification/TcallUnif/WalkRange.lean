module

public import Flapjack.HOL.Unification.TcallUnif
public import Flapjack.HOL.Unification.Walk.Range
public import Flapjack.HOL.Unification.Subst.Vars

@[expose] public section

/-! Variable bounds for first-order walks in the tail-call unifier. -/
namespace Flapjack.HOL.Unification

/-- The substitution survives the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_vwalkRangeVars_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/compilation/tcallUnifScript.sml" "vwalk_rangevars"
  (fmap_as_finite_support_parameters := [s])]
theorem vwalkRangeVars {α : Type} (s : HolFiniteMapExact Nat (Term α)) (v : Nat) (t : Term α)
    (h : wfs s ∧ vwalk s v = t) :
    (t = .var v ∧ v ∉ s.domain) ∨ Set.Subset (vars t) (rangeVars s) := by
  classical
  by_cases present : v ∈ s.domain
  · right
    apply inFrangeRangeVars s t
    rw [← h.2]
    exact vwalkInFrange s v ⟨h.1, present⟩
  · left
    exact ⟨h.2.symm.trans (notFdomVwalk s v ⟨h.1, present⟩), present⟩

/-- The substitution survives the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_walkRangeVars_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/compilation/tcallUnifScript.sml" "walk_rangevars"
  (fmap_as_finite_support_parameters := [s])]
theorem walkRangeVars {α : Type} (s : HolFiniteMapExact Nat (Term α)) (t u : Term α)
    (h : wfs s ∧ walk s t = u) :
    Set.Subset (vars u) (Set.union (rangeVars s) (vars t)) := by
  classical
  intro v hv
  by_cases same : walk s t = t
  · right
    rw [← h.2, same] at hv
    exact hv
  · left
    apply inFrangeRangeVars s u
    · rw [← h.2]
      exact walkInFrange s t ⟨h.1, same⟩
    · exact hv

end Flapjack.HOL.Unification

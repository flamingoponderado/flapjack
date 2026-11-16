module

public import Flapjack.HOL.Unification.Walkstar
public import Flapjack.HOL.Unification.Walk.ToVar

@[expose] public section

namespace Flapjack.HOL.Unification

/-- Canonical map codec roundtrip for walked variables. -/
theorem holFmapAsFiniteSupportParamWitness_vwalkInFrange_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkScript.sml" "vwalk_IN_FRANGE"
  (fmap_as_finite_support_parameters := [s])]
theorem vwalkInFrange {α : Type} (s : HolFiniteMapExact Nat (Term α)) (v : Nat)
    (h : wfs s ∧ v ∈ s.domain) :
    vwalk s v ∈ {t | ∃ key, s.lookup key = some t} := by
  induction v using h.1.induction with
  | h v ih =>
    cases found : s.lookup v with
    | none => exact False.elim (h.2 found)
    | some t =>
      cases t with
      | var n =>
        have step : vwalk s v = vwalk s n := by rw [vwalkEq s h.1 v, found]
        by_cases np : n ∈ s.domain
        · rw [step]
          exact ih n (by simp [vR, found, vars]) ⟨h.1, np⟩
        · have last := notFdomVwalk s n ⟨h.1, np⟩
          exact ⟨v, by simpa [step, last] using found⟩
      | pair l r => exact ⟨v, by simp [vwalkEq s h.1 v, found]⟩
      | const c => exact ⟨v, by simp [vwalkEq s h.1 v, found]⟩

/-- Canonical map codec roundtrip for walks ending in variables. -/
theorem holFmapAsFiniteSupportParamWitness_walkToVar_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkScript.sml" "walk_to_var"
  (fmap_as_finite_support_parameters := [s])]
theorem walkToVar {α : Type} (s : HolFiniteMapExact Nat (Term α)) (t : Term α) (v : Nat)
    (h : wfs s ∧ walk s t = .var v) : v ∉ s.domain ∧ ∃ u, t = .var u := by
  cases t with
  | var u => exact ⟨vwalkToVar s h.1 u v h.2, u, rfl⟩
  | pair l r => cases h.2
  | const c => cases h.2

/-- Canonical map codec roundtrip for changed walks. -/
theorem holFmapAsFiniteSupportParamWitness_walkInFrange_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkScript.sml" "walk_IN_FRANGE"
  (fmap_as_finite_support_parameters := [s])]
theorem walkInFrange {α : Type} (s : HolFiniteMapExact Nat (Term α)) (t : Term α)
    (h : wfs s ∧ walk s t ≠ t) :
    walk s t ∈ {t | ∃ key, s.lookup key = some t} := by
  cases t with
  | var v =>
    apply vwalkInFrange s v
    refine ⟨h.1, ?_⟩
    by_cases present : v ∈ s.domain
    · exact present
    · exact (h.2 (notFdomVwalk s v ⟨h.1, present⟩)).elim
  | pair l r => exact (h.2 rfl).elim
  | const c => exact (h.2 rfl).elim

end Flapjack.HOL.Unification

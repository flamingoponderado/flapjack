module

public import Flapjack.HOL.Unification.Walkstar.Occurs

@[expose] public section

namespace Flapjack.HOL.Unification

/-- Canonical codec witness for the substitution. -/
theorem holFmapAsFiniteSupportParamWitness_varsMeasure_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifPropsScript.sml" "vars_measure"
  (fmap_as_finite_support_parameters := [s])]
theorem varsMeasure {α : Type} (v : Nat) (t : Term α)
    (s : HolFiniteMapExact Nat (Term α))
    (h : vars t v ∧ (∀ w, t ≠ .var w) ∧ wfs s) :
    pairCount (walkstar s (.var v)) < pairCount (walkstar s t) := by
  have bound : ∀ t : Term α, vars t v →
      pairCount (walkstar s (.var v)) ≤ pairCount (walkstar s t) := by
    intro t
    induction t with
    | var u => intro hv; change v = u at hv; subst u; exact Nat.le_refl _
    | const c => intro hv; exact hv.elim
    | pair a b iha ihb =>
      intro hv
      rw [walkstarEq s h.2.2 (.pair a b)]
      simp only [walk, pairCount]
      rcases hv with hv | hv
      · have := iha hv; omega
      · have := ihb hv; omega
  cases t with
  | var u => exact (h.2.1 u rfl).elim
  | const c => exact h.1.elim
  | pair a b =>
    rw [walkstarEq s h.2.2 (.pair a b)]
    simp only [walk, pairCount]
    rcases h.1 with hv | hv
    · have := bound a hv; omega
    · have := bound b hv; omega

/-- Canonical codec witness for the occurrence substitution. -/
theorem holFmapAsFiniteSupportParamWitness_ocSubtermNeq_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

/-- Canonical codec witness for the observing substitution. -/
theorem holFmapAsFiniteSupportParamWitness_ocSubtermNeq_s2 {α : Type}
    (s2 : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2)).lookup key = s2.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2)).finiteSupport = s2.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2) = s2 :=
  holFmapAsFiniteSupportParamWitness_vR_subst s2 key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifPropsScript.sml" "oc_subterm_neq"
  (fmap_as_finite_support_parameters := [s, s2])]
theorem ocSubtermNeq {α : Type} (s : HolFiniteMapExact Nat (Term α)) (t : Term α) (v : Nat)
    (s2 : HolFiniteMapExact Nat (Term α))
    (h : Oc s t v ∧ (∀ w, t ≠ .var w) ∧ wfs s ∧ wfs s2) :
    walkstar s2 (.var v) ≠ walkstar s2 (walkstar s t) := by
  have vars : vars (walkstar s t) v := (ocEqVarsWalkstar s t v h.2.2.1).1 h.1
  have notVar : ∀ w, walkstar s t ≠ .var w := by
    intro w
    cases t with
    | var u => exact (h.2.1 u rfl).elim
    | const c => rw [walkstarEq s h.2.2.1 (.const c)]; simp [walk]
    | pair a b => rw [walkstarEq s h.2.2.1 (.pair a b)]; simp [walk]
  have lt := varsMeasure v (walkstar s t) s2 ⟨vars, notVar, h.2.2.2⟩
  intro eq
  rw [eq] at lt
  exact (Nat.lt_irrefl _) lt

end Flapjack.HOL.Unification

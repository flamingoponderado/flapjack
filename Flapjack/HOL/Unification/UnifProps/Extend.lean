module

public import Flapjack.HOL.Unification.UnifProps

@[expose] public section

namespace Flapjack.HOL.Unification

/-- The source substitutions use the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarExtend_s1 {α : Type}
    (s1 : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1)).lookup key = s1.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1)).finiteSupport = s1.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1) = s1 :=
  holFmapAsFiniteSupportParamWitness_vR_subst s1 key

/-- The source substitutions use the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarExtend_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifPropsScript.sml" "walkstar_extend"
  (fmap_as_finite_support_parameters := [s1, s])]
theorem walkstarExtend {α : Type} (s1 : HolFiniteMapExact Nat (Term α))
    (s : HolFiniteMapExact Nat (Term α)) (vx : Nat) (tx : Term α)
    (h : wfs s1 ∧ wfs (s.updateEq (vx, tx)) ∧ vx ∉ s.domain ∧
      walkstar s1 (.var vx) = walkstar s1 (walkstar s tx)) :
    ∀ t, walkstar s1 (walkstar (s.updateEq (vx, tx)) t) = walkstar s1 (walkstar s t) := by
  let sx := s.updateEq (vx, tx)
  have sub : s.submap sx := by
    intro key value found
    have ne : key ≠ vx := by
      intro eq
      subst key
      exact h.2.2.1 (by change s.lookup vx ≠ none; rw [found]; simp)
    simpa [sx, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne] using found
  have hwx : wfs sx := h.2.1
  have hw : wfs s := wfsSubmap sx s ⟨hwx, sub⟩
  let P : Term α → Prop := fun t => walkstar s1 (walkstar sx t) = walkstar s1 (walkstar s t)
  have lift : ∀ t : Term α, (∀ v, vars t v → P (.var v)) → P t := by
    intro t
    induction t with
    | var v => intro hv; exact hv v rfl
    | const c =>
      intro _
      unfold P
      rw [walkstarEq sx hwx (.const c), walkstarEq s hw (.const c)]
      rfl
    | pair a b iha ihb =>
      intro hv
      have ha := iha (fun v hvv => hv v (Or.inl hvv))
      have hb := ihb (fun v hvv => hv v (Or.inr hvv))
      unfold P at ha hb ⊢
      rw [walkstarEq sx hwx (.pair a b), walkstarEq s hw (.pair a b)]
      simp only [walk]
      rw [walkstarEq s1 h.1 (.pair _ _), walkstarEq s1 h.1 (.pair _ _)]
      simp only [walk, Term.pair.injEq]
      exact ⟨ha, hb⟩
  have varEq : ∀ v, P (.var v) := by
    intro v
    induction v using hwx.induction with
    | h v ih =>
      unfold P
      have ev (m : HolFiniteMapExact Nat (Term α)) (hm : wfs m) (v : Nat) :
          walkstar m (.var v) = match m.lookup v with
            | none => .var v
            | some t => walkstar m t := by
        classical
        simp only [walkstar, dif_pos hm]
        exact normalizeVar m hm v
      by_cases eq : v = vx
      · subst v
        rw [ev sx hwx vx]
        have found : sx.lookup vx = some tx := by simp [sx, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
        rw [found]
        have old : s.lookup vx = none := by
          have absent := h.2.2.1
          change ¬ (s.lookup vx ≠ none) at absent
          exact Classical.not_not.mp absent
        rw [ev s hw vx, old]
        have step : P tx := by
          apply lift tx
          intro v hv
          apply ih v
          simp [vR, found, hv]
        exact step.trans h.2.2.2.symm
      · have found : sx.lookup v = s.lookup v := by
          simp [sx, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq]
        rw [ev sx hwx v, ev s hw v, found]
        cases res : s.lookup v with
        | none => rfl
        | some t =>
          apply lift t
          intro u hu
          apply ih u
          unfold vR
          rw [found, res]
          exact hu
  intro t
  exact lift t (fun v _ => varEq v)

end Flapjack.HOL.Unification

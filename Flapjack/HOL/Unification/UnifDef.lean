module

public import Flapjack.HOL.Unification.Walk
public import Flapjack.HOL.Unification.Walk.ToVar
public import Flapjack.HOL.Unification.Subst.NoCycles
public import Flapjack.HOL.Unification.Walkstar.Dependency
public import Mathlib.Logic.Relation

@[expose] public section

/-! Dependency paths through a substitution update. -/
namespace Flapjack.HOL.Unification

/-- The substitution survives the canonical finite-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_tcVRUpdate_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "TC_vR_update"
  (fmap_as_finite_support_parameters := [s])]
theorem tcVRUpdate {α : Type} (s : HolFiniteMapExact Nat (Term α)) (v : Nat) (t : Term α) :
    ∀ y x, Relation.TransGen (vR (s.updateEq (v, t))) y x → v ∉ s.domain →
      Relation.TransGen (vR s) y x ∨
      ∃ u, Relation.ReflTransGen (vR s) v x ∧ vars t u ∧ Relation.ReflTransGen (vR s) y u := by
  intro y x path
  induction path with
  | @single b edge =>
    intro absent
    by_cases eq : b = v
    · subst b
      right
      refine ⟨y, .refl, ?_, .refl⟩
      simpa [vR, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using edge
    · left
      apply Relation.TransGen.single
      simpa [vR, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using edge
  | @tail z x chain edge ih =>
    intro absent
    by_cases eq : x = v
    · subst x
      rcases ih absent with old | ⟨u, hvz, htu, hyu⟩
      · right
        refine ⟨z, .refl, ?_, old.to_reflTransGen⟩
        simpa [vR, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using edge
      · exact Or.inr ⟨u, .refl, htu, hyu⟩
    · have oldedge : vR s z x := by
        simpa [vR, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using edge
      rcases ih absent with old | ⟨u, hvz, htu, hyu⟩
      · exact Or.inl (.tail old oldedge)
      · exact Or.inr ⟨u, .tail hvz oldedge, htu, hyu⟩

/-- The substitution survives the canonical finite-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_wfsExtend_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "wfs_extend"
  (fmap_as_finite_support_parameters := [s])]
theorem wfsExtend {α : Type} (s : HolFiniteMapExact Nat (Term α)) (v : Nat) (t : Term α)
    (h : wfs s ∧ v ∉ s.domain ∧ ¬ vars (walkstar s t) v) :
    wfs (s.updateEq (v, t)) := by
  obtain ⟨hw, absent, notvars⟩ := h
  apply (wfsNoCycles _).mpr
  intro x cycle
  rcases tcVRUpdate s v t x x cycle absent with old | ⟨u, hvx, htu, hxu⟩
  · exact (wfsNoCycles s).mp hw x old
  · have hvu := hvx.trans hxu
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hvu with eq | path
    · subst u
      exact notvars (notFdomWalkstar s v hw t absent htu)
    · exact notvars (tcVRVarsWalkstar s t u v ⟨hw, htu, path, absent⟩)

/-- The substitution survives the canonical finite-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_vwalkFdom_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "vwalk_FDOM"
  (fmap_as_finite_support_parameters := [s])]
theorem vwalkFdom {α : Type} (s : HolFiniteMapExact Nat (Term α)) (v : Nat) (t : Term α)
    (hw : wfs s) (result : vwalk s v = t) :
    (v ∉ s.domain ∧ t = .var v) ∨
    (v ∈ s.domain ∧ t ≠ .var v ∧
      ∃ u, vwalk s v = vwalk s u ∧ s.lookup u = some t) := by
  have endpoint : ∀ v, v ∈ s.domain →
      ∃ u, vwalk s v = vwalk s u ∧ s.lookup u = some (vwalk s v) := by
    intro v
    induction v using hw.induction with
    | h v ih =>
      intro present
      cases found : s.lookup v with
      | none => exact False.elim (present found)
      | some term =>
        cases term with
        | var n =>
          have step : vwalk s v = vwalk s n := by rw [vwalkEq s hw v, found]
          by_cases np : n ∈ s.domain
          · obtain ⟨u, heq, hu⟩ := ih n (by simp [vR, found, vars]) np
            exact ⟨u, step.trans heq, by simpa [step] using hu⟩
          · have last := notFdomVwalk s n ⟨hw, np⟩
            refine ⟨v, rfl, ?_⟩
            simpa [step, last] using found
        | pair l r =>
          refine ⟨v, rfl, ?_⟩
          simp [vwalkEq s hw v, found]
        | const c =>
          refine ⟨v, rfl, ?_⟩
          simp [vwalkEq s hw v, found]
  by_cases present : v ∈ s.domain
  · right
    refine ⟨present, ?_, ?_⟩
    · intro eq
      have absent := vwalkToVar s hw v v (result.trans eq)
      exact absent present
    · obtain ⟨u, heq, hu⟩ := endpoint v present
      exact ⟨u, heq, by simpa [result] using hu⟩
  · exact Or.inl ⟨present, result.symm.trans (notFdomVwalk s v ⟨hw, present⟩)⟩

end Flapjack.HOL.Unification

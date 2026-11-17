module

public import Flapjack.HOL.Unification.Walkstar.Submap
public import Flapjack.HOL.Unification.Walkstar.Walk
public import Mathlib.Logic.Relation
public import Flapjack.HOL.Unification.Subst.NoCycles

@[expose] public section

/-! Properties of first-order unification. -/
namespace Flapjack.HOL.Unification

/-- The substitution survives the canonical finite-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_vwalkIrrelevantFupdate_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifPropsScript.sml" "vwalk_irrelevant_FUPDATE"
  (fmap_as_finite_support_parameters := [s])]
theorem vwalkIrrelevantFupdate {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (vx : Nat) (tx : Term α) (h : wfs (s.updateEq (vx, tx)) ∧ vx ∉ s.domain) :
    ∀ v, ¬ Relation.ReflTransGen (vR s) vx v →
      vwalk (s.updateEq (vx, tx)) v = vwalk s v := by
  have sub : s.submap (s.updateEq (vx, tx)) := by
    intro key value found
    have ne : key ≠ vx := by
      intro eq
      subst key
      exact h.2 (by change s.lookup vx ≠ none; rw [found]; simp)
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne] using found
  have hs : wfs s := wfsSubmap _ _ ⟨h.1, sub⟩
  intro v
  induction v using h.1.induction with
  | h v ih =>
    intro noPath
    have ne : v ≠ vx := by
      intro eq
      subst v
      exact noPath .refl
    have lookup : (s.updateEq (vx, tx)).lookup v = s.lookup v := by
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne]
    rw [vwalkEq _ h.1 v, vwalkEq _ hs v, lookup]
    cases found : s.lookup v with
    | none => rfl
    | some t =>
      cases t with
      | var n =>
        have edge : vR s n v := by simp [vR, found, vars]
        have edge' : vR (s.updateEq (vx, tx)) n v := by
          unfold vR
          rw [lookup, found]
          simp [vars]
        exact ih n edge' (fun path => noPath (path.tail edge))
      | pair l r => rfl
      | const c => rfl

/-- Both substitutions use the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tcVRSubmap_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

/-- Both substitutions use the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tcVRSubmap_sx {α : Type}
    (sx : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).lookup key = sx.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).finiteSupport = sx.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx) = sx :=
  holFmapAsFiniteSupportParamWitness_vR_subst sx key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifPropsScript.sml" "TC_vR_SUBMAP"
  (fmap_as_finite_support_parameters := [s, sx])]
theorem tcVRSubmap {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (sx : HolFiniteMapExact Nat (Term α))
    (sub : s.submap sx) : ∀ u v, Relation.TransGen (vR s) u v →
      Relation.TransGen (vR sx) u v := by
  have mono : ∀ u v, vR s u v → vR sx u v := by
    intro u v edge
    unfold vR at edge ⊢
    cases found : s.lookup v with
    | none => simp [found] at edge
    | some t => simpa [found, sub v t found] using edge
  intro u v path
  induction path with
  | single edge => exact .single (mono _ _ edge)
  | tail _ edge ih => exact ih.tail (mono _ _ edge)

/-- The substitution survives the canonical finite-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_vwalkFupdateVar_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifPropsScript.sml" "vwalk_FUPDATE_var"
  (fmap_as_finite_support_parameters := [s])]
theorem vwalkFupdateVar {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (v1 v2 : Nat) (h : wfs (s.updateEq (v1, .var v2)) ∧ v1 ∉ s.domain) :
    vwalk (s.updateEq (v1, .var v2)) v2 = vwalk s v2 := by
  apply vwalkIrrelevantFupdate s v1 (.var v2) h v2
  intro path
  have sub : s.submap (s.updateEq (v1, .var v2)) := by
    intro key value found
    have ne : key ≠ v1 := by
      intro eq
      subst key
      exact h.2 (by change s.lookup v1 ≠ none; rw [found]; simp)
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne] using found
  have edge : vR (s.updateEq (v1, .var v2)) v2 v1 := by
    simp [vR, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, vars]
  apply (wfsNoCycles _).mp h.1 v1
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp path with eq | path
  · subst v2
    exact .single edge
  · exact (tcVRSubmap s _ sub _ _ path).tail edge

/-- The smaller substitution uses the canonical map codec. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarWalkSubmap_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

/-- The larger substitution uses the canonical map codec. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarWalkSubmap_sx {α : Type}
    (sx : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).lookup key = sx.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).finiteSupport = sx.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx) = sx :=
  holFmapAsFiniteSupportParamWitness_vR_subst sx key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifPropsScript.sml" "walkstar_walk_SUBMAP"
  (fmap_as_finite_support_parameters := [s, sx])]
theorem walkstarWalkSubmap {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (sx : HolFiniteMapExact Nat (Term α)) (t : Term α)
    (h : s.submap sx ∧ wfs sx) : walkstar sx t = walkstar sx (walk s t) := by
  have hs := wfsSubmap sx s ⟨h.2, h.1⟩
  calc
    walkstar sx t = walkstar sx (walkstar s t) := walkstarSubmap s sx t h
    _ = walkstar sx (walkstar s (walk s t)) := by rw [walkstarWalk s t hs]
    _ = walkstar sx (walk s t) := (walkstarSubmap s sx (walk s t) h).symm

end Flapjack.HOL.Unification

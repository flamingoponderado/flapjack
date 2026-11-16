module

public import Flapjack.HOL.Unification.Walk
public import Flapjack.HOL.Unification.Walk.ToVar
public import Flapjack.HOL.Unification.Walk.Range
public import Flapjack.HOL.Unification.Walk.Submap
public import Flapjack.HOL.Unification.Walkstar.Walk
public import Flapjack.HOL.Unification.Subst.NoCycles
public import Flapjack.HOL.Unification.Subst.Vars
public import Flapjack.HOL.Unification.UnifDef.FiniteSubset
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

/-- Canonical map codec roundtrip for the unification variable measure. -/
theorem holFmapAsFiniteSupportParamWitness_allVars_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "allvars_def"
  (fmap_as_finite_support_parameters := [s])]
def allVars {α β : Type} (s : HolFiniteMapExact Nat (Term α)) (t1 t2 : Term β) : Set Nat :=
  Set.union (Set.union (vars t1) (vars t2)) (substVars s)

/-- Canonical map codec roundtrip for finiteness of the unification measure. -/
theorem holFmapAsFiniteSupportParamWitness_finiteAllVars_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "FINITE_allvars"
  (fmap_as_finite_support_parameters := [s])]
theorem finiteAllVars {α β : Type} (s : HolFiniteMapExact Nat (Term α)) (t1 t2 : Term β) :
    Set.Finite (allVars s t1 t2) :=
  ((finiteVars t1).union (finiteVars t2)).union (finiteSubstVars s)

/-- Canonical map codec roundtrip for symmetry of the unification measure. -/
theorem holFmapAsFiniteSupportParamWitness_allVarsSym_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "allvars_sym"
  (fmap_as_finite_support_parameters := [s])]
theorem allVarsSym {α β : Type} (s : HolFiniteMapExact Nat (Term α)) (t1 t2 : Term β) :
    allVars s t1 t2 = allVars s t2 t1 := by
  unfold allVars
  congr 1
  exact Set.union_comm (vars t1) (vars t2)

/-- Canonical map codec roundtrip for the walked-pair containment theorem. -/
theorem holFmapAsFiniteSupportParamWitness_vwalkPairSubsetRangeVars_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "vwalk_to_Pair_SUBSET_rangevars"
  (fmap_as_finite_support_parameters := [s])]
theorem vwalkPairSubsetRangeVars {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (v : Nat) (t1 t2 : Term α) (h : wfs s ∧ vwalk s v = .pair t1 t2) :
    Set.Subset (vars t1) (rangeVars s) ∧ Set.Subset (vars t2) (rangeVars s) := by
  have found := vwalkFdom s v (.pair t1 t2) h.1 h.2
  rcases found with ⟨_, impossible⟩ | ⟨_, _, u, _, lookup⟩
  · cases impossible
  · have contained := inFrangeRangeVars s (.pair t1 t2) ⟨u, lookup⟩
    exact ⟨fun _ hv => contained (Or.inl hv), fun _ hv => contained (Or.inr hv)⟩

/-- Canonical map codec roundtrip for the recursive unification variable sets. -/
theorem holFmapAsFiniteSupportParamWitness_allVarsSubset_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "allvars_SUBSET"
  (fmap_as_finite_support_parameters := [s])]
theorem allVarsSubset {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (t1 t2 t1a t1d t2a t2d : Term α)
    (h : wfs s ∧ walk s t1 = .pair t1a t1d ∧ walk s t2 = .pair t2a t2d) :
    Set.Subset (allVars s t1a t2a) (allVars s t1 t2) ∧
    Set.Subset (allVars s t1d t2d) (allVars s t1 t2) := by
  have part : ∀ (t a d : Term α), walk s t = .pair a d →
      Set.Subset (vars a) (Set.union (vars t) (substVars s)) ∧
      Set.Subset (vars d) (Set.union (vars t) (substVars s)) := by
    intro t a d eq
    cases t with
    | var v =>
      have hp := vwalkPairSubsetRangeVars s v a d ⟨h.1, eq⟩
      exact ⟨fun _ hv => Or.inr (Or.inr (hp.1 hv)),
        fun _ hv => Or.inr (Or.inr (hp.2 hv))⟩
    | pair l r =>
      simp only [walk, Term.pair.injEq] at eq
      obtain ⟨rfl, rfl⟩ := eq
      exact ⟨fun _ hv => Or.inl (Or.inl hv), fun _ hv => Or.inl (Or.inr hv)⟩
    | const c => simp [walk] at eq
  obtain ⟨ha, hd⟩ := part t1 t1a t1d h.2.1
  obtain ⟨ha', hd'⟩ := part t2 t2a t2d h.2.2
  constructor <;> intro v hv <;>
    change (vars t1 v ∨ vars t2 v) ∨ substVars s v <;>
    change (_ ∨ _) ∨ substVars s v at hv <;>
    rcases hv with (hv | hv) | hv
  · rcases ha hv with hv | hv <;> tauto
  · rcases ha' hv with hv | hv <;> tauto
  · tauto
  · rcases hd hv with hv | hv <;> tauto
  · rcases hd' hv with hv | hv <;> tauto
  · tauto

/-- Canonical map codec roundtrip for normalized subterm size. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarSubtermSmaller_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "walkstar_subterm_smaller"
  (fmap_as_finite_support_parameters := [s])]
theorem walkstarSubtermSmaller {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (t1 t1a t1d : Term α) (h : wfs s ∧ walk s t1 = .pair t1a t1d) :
    pairCount (walkstar s t1a) < pairCount (walkstar s t1) ∧
    pairCount (walkstar s t1d) < pairCount (walkstar s t1) := by
  have eq := walkstarEq s h.1 t1
  rw [h.2] at eq
  rw [eq]
  simp only [pairCount]
  omega

/-- Canonical map codec roundtrip for the substitution-update containment. -/
theorem holFmapAsFiniteSupportParamWitness_allVarsSubsetFupdate_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "allvars_SUBSET_FUPDATE"
  (fmap_as_finite_support_parameters := [s])]
theorem allVarsSubsetFupdate {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (t1 t2 t1a t1d t2a t2d : Term α) (v : Nat)
    (h : walk s t1 = .pair t1a t1d ∧ walk s t2 = .pair t2a t2d ∧
      walk s t1a = .var v ∧ wfs s) :
    Set.Subset (allVars (s.updateEq (v, walk s t2a)) t1d t2d) (allVars s t1 t2) := by
  classical
  have parts := allVarsSubset s t1 t2 t1a t1d t2a t2d ⟨h.2.2.2, h.1, h.2.1⟩
  have free := (walkToVar s t1a v ⟨h.2.2.2, h.2.2.1⟩).1
  have walked : ∀ t : Term α, Set.Subset (vars (walk s t))
      (Set.union (vars t) (rangeVars s)) := by
    intro t x hx
    by_cases same : walk s t = t
    · exact Or.inl (same ▸ hx)
    · exact Or.inr (inFrangeRangeVars s (walk s t) (walkInFrange s t ⟨h.2.2.2, same⟩) hx)
  have first : ∀ x, vars t1a x → allVars s t1 t2 x :=
    fun _ hx => parts.1 (Or.inl (Or.inl hx))
  have second : ∀ x, vars t2a x → allVars s t1 t2 x :=
    fun _ hx => parts.1 (Or.inl (Or.inr hx))
  have range : ∀ x, rangeVars s x → allVars s t1 t2 x :=
    fun _ hx => Or.inr (Or.inr hx)
  have inV : allVars s t1 t2 v := by
    have hv : vars (walk s t1a) v := by rw [h.2.2.1]; rfl
    rcases walked t1a hv with hv | hv
    · exact first v hv
    · exact range v hv
  have updatedRange : rangeVars (s.updateEq (v, walk s t2a)) =
      Set.union (rangeVars s) (vars (walk s t2a)) := by
    have eqUpdate : s.updateEq (v, walk s t2a) =
        @HolFiniteMapExact.updateEq Nat (Term α) (Classical.decEq Nat) s (v, walk s t2a) := by
      congr 1
      exact Subsingleton.elim _ _
    rw [eqUpdate]
    exact rangeVarsUpdate s v (walk s t2a) free
  intro x hx
  change (vars t1d x ∨ vars t2d x) ∨
    ((s.updateEq (v, walk s t2a)).domain x ∨
      rangeVars (s.updateEq (v, walk s t2a)) x) at hx
  rcases hx with (hfirst | hsecond) | (hdom | hran)
  · exact parts.2 (Or.inl (Or.inl hfirst))
  · exact parts.2 (Or.inl (Or.inr hsecond))
  · by_cases eq : x = v
    · subst x; exact inV
    · have old : s.domain x := by
        change (s.updateEq (v, walk s t2a)).lookup x ≠ none at hdom
        change s.lookup x ≠ none
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using hdom
      exact Or.inr (Or.inl old)
  · change x ∈ rangeVars (s.updateEq (v, walk s t2a)) at hran
    rw [updatedRange] at hran
    change rangeVars s x ∨ vars (walk s t2a) x at hran
    rcases hran with old | new
    · exact range x old
    · rcases walked t2a new with old | old
      · exact second x old
      · exact range x old

/-- Local lookup factoring for fresh updates; this is not the general HOL
    submap-update characterization. -/
private theorem submapFreshUpdate {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (v : Nat) (t : Term α) (absent : v ∉ s.domain) :
    s.submap (s.updateEq (v, t)) := by
  intro key value found
  have ne : key ≠ v := by
    intro eq
    subst key
    exact absent (by change s.lookup v ≠ none; rw [found]; simp)
  simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne] using found

/-- Canonical map codec roundtrip for normalized size after update. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarSubtermFupdate_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "walkstar_subterm_FUPDATE"
  (fmap_as_finite_support_parameters := [s])]
theorem walkstarSubtermFupdate {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (v : Nat) (t t1 t1a t1d : Term α)
    (h : wfs s ∧ v ∉ s.domain ∧ ¬ vars (walkstar s t) v ∧
      walk s t1 = .pair t1a t1d) :
    pairCount (walkstar (s.updateEq (v, t)) t1d) <
      pairCount (walkstar (s.updateEq (v, t)) t1) := by
  have hw := wfsExtend s v t ⟨h.1, h.2.1, h.2.2.1⟩
  have sub := submapFreshUpdate s v t h.2.1
  have walked : walk (s.updateEq (v, t)) t1 = .pair t1a t1d := by
    cases t1 with
    | var n =>
      have step := vwalkSubmap (s.updateEq (v, t)) hw n s sub
      have initial : vwalk s n = .pair t1a t1d := h.2.2.2
      rw [initial] at step
      exact step
    | pair a b => exact h.2.2.2
    | const c => cases h.2.2.2
  exact (walkstarSubtermSmaller (s.updateEq (v, t)) t1 t1a t1d ⟨hw, walked⟩).2

/-- Canonical map codec roundtrip for the larger substitution in `uP`. -/
theorem holFmapAsFiniteSupportParamWitness_uP_sx {α : Type}
    (sx : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).lookup key = sx.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).finiteSupport = sx.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx) = sx :=
  holFmapAsFiniteSupportParamWitness_vR_subst sx key

/-- Canonical map codec roundtrip for the smaller substitution in `uP`. -/
theorem holFmapAsFiniteSupportParamWitness_uP_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "uP_def"
  (fmap_as_finite_support_parameters := [sx, s])]
def uP {α β : Type} (sx : HolFiniteMapExact Nat (Term α))
    (s : HolFiniteMapExact Nat (Term α)) (t1 t2 : Term β) : Prop :=
  wfs sx ∧ s.submap sx ∧ Set.Subset (substVars sx) (allVars s t1 t2)

/-- Canonical map codec roundtrip for the larger substitution in `uPSym`. -/
theorem holFmapAsFiniteSupportParamWitness_uPSym_sx {α : Type}
    (sx : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).lookup key = sx.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).finiteSupport = sx.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx) = sx :=
  holFmapAsFiniteSupportParamWitness_vR_subst sx key

/-- Canonical map codec roundtrip for the smaller substitution in `uPSym`. -/
theorem holFmapAsFiniteSupportParamWitness_uPSym_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "uP_sym"
  (fmap_as_finite_support_parameters := [sx, s])]
theorem uPSym {α β : Type} (sx : HolFiniteMapExact Nat (Term α))
    (s : HolFiniteMapExact Nat (Term α)) (t1 t2 : Term β) :
    uP sx s t1 t2 ↔ uP sx s t2 t1 := by
  simp only [uP, allVarsSym s t1 t2]

/-- Canonical map codec roundtrip for `uP` after an update. -/
theorem holFmapAsFiniteSupportParamWitness_uPFupdate_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "uP_FUPDATE"
  (fmap_as_finite_support_parameters := [s])]
theorem uPFupdate {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (v : Nat) (t1 t2 : Term α)
    (h : wfs s ∧ v ∉ s.domain ∧ ¬ vars (walkstar s t2) v ∧ walk s t1 = .var v) :
    uP (s.updateEq (v, walk s t2)) s t1 t2 := by
  classical
  have notOccurs : ¬ vars (walkstar s (walk s t2)) v := by
    rw [walkstarWalk s t2 h.1]
    exact h.2.2.1
  have hw := wfsExtend s v (walk s t2) ⟨h.1, h.2.1, notOccurs⟩
  have sub := submapFreshUpdate s v (walk s t2) h.2.1
  have walked : ∀ t : Term α, Set.Subset (vars (walk s t))
      (Set.union (vars t) (rangeVars s)) := by
    intro t x hx
    by_cases same : walk s t = t
    · exact Or.inl (same ▸ hx)
    · exact Or.inr (inFrangeRangeVars s (walk s t) (walkInFrange s t ⟨h.1, same⟩) hx)
  have inV : allVars s t1 t2 v := by
    have hv : vars (walk s t1) v := by rw [h.2.2.2]; rfl
    rcases walked t1 hv with hv | hv
    · exact Or.inl (Or.inl hv)
    · exact Or.inr (Or.inr hv)
  have updatedRange : rangeVars (s.updateEq (v, walk s t2)) =
      Set.union (rangeVars s) (vars (walk s t2)) := by
    have eqUpdate : s.updateEq (v, walk s t2) =
        @HolFiniteMapExact.updateEq Nat (Term α) (Classical.decEq Nat) s (v, walk s t2) := by
      congr 1
      exact Subsingleton.elim _ _
    rw [eqUpdate]
    exact rangeVarsUpdate s v (walk s t2) h.2.1
  refine ⟨hw, sub, ?_⟩
  intro x hx
  change (s.updateEq (v, walk s t2)).domain x ∨
    rangeVars (s.updateEq (v, walk s t2)) x at hx
  rcases hx with hdom | hran
  · by_cases eq : x = v
    · subst x; exact inV
    · have old : s.domain x := by
        change (s.updateEq (v, walk s t2)).lookup x ≠ none at hdom
        change s.lookup x ≠ none
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using hdom
      exact Or.inr (Or.inl old)
  · change x ∈ rangeVars (s.updateEq (v, walk s t2)) at hran
    rw [updatedRange] at hran
    change rangeVars s x ∨ vars (walk s t2) x at hran
    rcases hran with old | new
    · exact Or.inr (Or.inr old)
    · rcases walked t2 new with old | old
      · exact Or.inl (Or.inr old)
      · exact Or.inr (Or.inr old)

/-- Tuple-shaped proof model for the unification decrease relation. Its full
    source equation is established by `uREq` below. -/
def uR {α : Type} (left right : HolFiniteMapExact Nat (Term α) × Term α × Term α) : Prop :=
  wfs left.1 ∧ right.1.submap left.1 ∧
  Set.Subset (allVars left.1 left.2.1 left.2.2) (allVars right.1 right.2.1 right.2.2) ∧
  pairCount (walkstar left.1 left.2.1) < pairCount (walkstar left.1 right.2.1)

/-- Canonical codec roundtrip for the left substitution in the relation. -/
theorem holFmapAsFiniteSupportParamWitness_uREq_sx {α : Type}
    (sx : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).lookup key = sx.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).finiteSupport = sx.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx) = sx :=
  holFmapAsFiniteSupportParamWitness_vR_subst sx key

/-- Canonical codec roundtrip for the right substitution in the relation. -/
theorem holFmapAsFiniteSupportParamWitness_uREq_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "uR_def"
  (fmap_as_finite_support_parameters := [sx, s])]
theorem uREq {α : Type} (sx : HolFiniteMapExact Nat (Term α)) (c1 c2 : Term α)
    (s : HolFiniteMapExact Nat (Term α)) (t1 t2 : Term α) :
    uR (sx, c1, c2) (s, t1, t2) ↔
    wfs sx ∧ s.submap sx ∧ Set.Subset (allVars sx c1 c2) (allVars s t1 t2) ∧
    pairCount (walkstar sx c1) < pairCount (walkstar sx t1) := Iff.rfl

/-- Canonical codec roundtrip for the recursive unification cases. -/
theorem holFmapAsFiniteSupportParamWitness_uRSubterm_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "uR_subterm"
  (fmap_as_finite_support_parameters := [s])]
theorem uRSubterm {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (t1 t2 t1a t1d t2a t2d : Term α)
    (h : wfs s ∧ walk s t1 = .pair t1a t1d ∧ walk s t2 = .pair t2a t2d) :
    uR (s, t1a, t2a) (s, t1, t2) ∧ uR (s, t1d, t2d) (s, t1, t2) := by
  have subset := allVarsSubset s t1 t2 t1a t1d t2a t2d h
  have size := walkstarSubtermSmaller s t1 t1a t1d ⟨h.1, h.2.1⟩
  exact ⟨⟨h.1, fun _ _ found => found, subset.1, size.1⟩,
    ⟨h.1, fun _ _ found => found, subset.2, size.2⟩⟩

/-- Canonical codec roundtrip for the first recursive unification case. -/
theorem holFmapAsFiniteSupportParamWitness_tcaThm_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "tca_thm"
  (fmap_as_finite_support_parameters := [s])]
theorem tcaThm {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (t1 t2 t1a t1d t2a t2d : Term α)
    (h : wfs s ∧ walk s t1 = .pair t1a t1d ∧ walk s t2 = .pair t2a t2d) :
    uR (s, t1a, t2a) (s, t1, t2) := (uRSubterm s t1 t2 t1a t1d t2a t2d h).1

/-- Canonical codec roundtrip for the left substitution in `uRImpUP`. -/
theorem holFmapAsFiniteSupportParamWitness_uRImpUP_sx {α : Type}
    (sx : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).lookup key = sx.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).finiteSupport = sx.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx) = sx :=
  holFmapAsFiniteSupportParamWitness_vR_subst sx key

/-- Canonical codec roundtrip for the right substitution in `uRImpUP`. -/
theorem holFmapAsFiniteSupportParamWitness_uRImpUP_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "uR_IMP_uP"
  (fmap_as_finite_support_parameters := [sx, s])]
theorem uRImpUP {α : Type} (sx : HolFiniteMapExact Nat (Term α)) (c1 c2 : Term α)
    (s : HolFiniteMapExact Nat (Term α)) (t1 t2 : Term α)
    (h : uR (sx, c1, c2) (s, t1, t2)) : uP sx s t1 t2 := by
  exact ⟨h.1, h.2.1, fun _ hv => h.2.2.1 (Or.inr hv)⟩

/-- Canonical codec roundtrip for the updated recursive unification case. -/
theorem holFmapAsFiniteSupportParamWitness_uRSubtermFupdate_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "uR_subterm_FUPDATE"
  (fmap_as_finite_support_parameters := [s])]
theorem uRSubtermFupdate {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (t1 t2 t1a t1d t2a t2d : Term α) (v : Nat) (t : Term α)
    (h : walk s t1 = .pair t1a t1d ∧ walk s t2 = .pair t2a t2d ∧
      ((walk s t1a = .var v ∧ walk s t2a = t) ∨
       (walk s t2a = .var v ∧ walk s t1a = t)) ∧
      wfs s ∧ v ∉ s.domain ∧ ¬ vars (walkstar s t) v) :
    uR (s.updateEq (v, t), t1d, t2d) (s, t1, t2) := by
  have hw := wfsExtend s v t ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  have sub := submapFreshUpdate s v t h.2.2.2.2.1
  have size := walkstarSubtermFupdate s v t t1 t1a t1d
    ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, h.1⟩
  have subset : Set.Subset (allVars (s.updateEq (v, t)) t1d t2d) (allVars s t1 t2) := by
    rcases h.2.2.1 with left | right
    · have result := allVarsSubsetFupdate s t1 t2 t1a t1d t2a t2d v
        ⟨h.1, h.2.1, left.1, h.2.2.2.1⟩
      rwa [left.2] at result
    · have result := allVarsSubsetFupdate s t2 t1 t2a t2d t1a t1d v
        ⟨h.2.1, h.1, right.1, h.2.2.2.1⟩
      rw [right.2, allVarsSym _ t2d t1d, allVarsSym _ t2 t1] at result
      exact result
  exact ⟨hw, sub, subset, size⟩

/-- Canonical codec roundtrip for the larger substitution in `walkSubmap`. -/
theorem holFmapAsFiniteSupportParamWitness_walkSubmap_sx {α : Type}
    (sx : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).lookup key = sx.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).finiteSupport = sx.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx) = sx :=
  holFmapAsFiniteSupportParamWitness_vR_subst sx key

/-- Canonical codec roundtrip for the smaller substitution in `walkSubmap`. -/
theorem holFmapAsFiniteSupportParamWitness_walkSubmap_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "walk_SUBMAP"
  (fmap_as_finite_support_parameters := [sx, s])]
theorem walkSubmap {α : Type} (sx : HolFiniteMapExact Nat (Term α))
    (s : HolFiniteMapExact Nat (Term α)) (t : Term α) (h : wfs sx ∧ s.submap sx) :
    match walk s t with
    | .var u => walk sx t = walk sx (.var u)
    | u => walk sx t = u := by
  cases t with
  | var n =>
    have step := vwalkSubmap sx h.1 n s h.2
    cases result : vwalk s n <;> simpa [walk, result] using step
  | pair l r => rfl
  | const c => rfl

/-- Canonical codec roundtrip for the larger substitution in `uPImpSubtermUR`. -/
theorem holFmapAsFiniteSupportParamWitness_uPImpSubtermUR_sx {α : Type}
    (sx : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).lookup key = sx.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).finiteSupport = sx.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx) = sx :=
  holFmapAsFiniteSupportParamWitness_vR_subst sx key

/-- Canonical codec roundtrip for the smaller substitution in `uPImpSubtermUR`. -/
theorem holFmapAsFiniteSupportParamWitness_uPImpSubtermUR_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml" "uP_IMP_subterm_uR"
  (fmap_as_finite_support_parameters := [sx, s])]
theorem uPImpSubtermUR {α : Type} (sx : HolFiniteMapExact Nat (Term α))
    (s : HolFiniteMapExact Nat (Term α)) (t1 t2 t1a t1d t2a t2d : Term α)
    (h : wfs s ∧ walk s t1 = .pair t1a t1d ∧ walk s t2 = .pair t2a t2d ∧
      (uP sx s t1a t2a ∨ uP sx s t1d t2d)) :
    uR (sx, t1d, t2d) (s, t1, t2) := by
  have parts := allVarsSubset s t1 t2 t1a t1d t2a t2d ⟨h.1, h.2.1, h.2.2.1⟩
  have hsx : wfs sx ∧ s.submap sx ∧ Set.Subset (substVars sx) (allVars s t1 t2) := by
    rcases h.2.2.2 with first | second
    · exact ⟨first.1, first.2.1, fun _ hx => parts.1 (first.2.2 hx)⟩
    · exact ⟨second.1, second.2.1, fun _ hx => parts.2 (second.2.2 hx)⟩
  have subset : Set.Subset (allVars sx t1d t2d) (allVars s t1 t2) := by
    intro x hx
    change (vars t1d x ∨ vars t2d x) ∨ substVars sx x at hx
    rcases hx with (ha | hd) | hs
    · exact parts.2 (Or.inl (Or.inl ha))
    · exact parts.2 (Or.inl (Or.inr hd))
    · exact hsx.2.2 hs
  have walked : walk sx t1 = .pair t1a t1d := by
    have step := walkSubmap sx s t1 ⟨hsx.1, hsx.2.1⟩
    rw [h.2.1] at step
    exact step
  have size := (walkstarSubtermSmaller sx t1 t1a t1d ⟨hsx.1, walked⟩).2
  exact ⟨hsx.1, hsx.2.1, subset, size⟩

end Flapjack.HOL.Unification

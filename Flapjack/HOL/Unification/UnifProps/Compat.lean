module

public import Flapjack.HOL.Unification.UnifProps.Extend

@[expose] public section

namespace Flapjack.HOL.Unification
/-- The canonical substitution survives the finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_compatible_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

/-- The canonical substitution survives the finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_compatible_s0 {α : Type}
    (s0 : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s0)).lookup key = s0.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s0)).finiteSupport = s0.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s0) = s0 :=
  holFmapAsFiniteSupportParamWitness_vR_subst s0 key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifPropsScript.sml" "COMPAT_def"
  (fmap_as_finite_support_parameters := [s, s0])]
def compatible {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (s0 : HolFiniteMapExact Nat (Term α)) : Prop :=
  wfs s ∧ wfs s0 ∧ ∀ t, walkstar s (walkstar s0 t) = walkstar s t

/-- The canonical substitution survives the finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_submapCompat_sx {α : Type}
    (sx : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).lookup key = sx.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).finiteSupport = sx.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx) = sx :=
  holFmapAsFiniteSupportParamWitness_vR_subst sx key

/-- The canonical substitution survives the finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_submapCompat_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifPropsScript.sml" "SUBMAP_COMPAT"
  (fmap_as_finite_support_parameters := [sx, s])]
theorem submapCompat {α : Type} (sx : HolFiniteMapExact Nat (Term α))
    (s : HolFiniteMapExact Nat (Term α)) (h : wfs sx ∧ s.submap sx) : compatible sx s :=
  ⟨h.1, wfsSubmap sx s ⟨h.1, h.2⟩, fun t => (walkstarSubmap s sx t ⟨h.2, h.1⟩).symm⟩

/-- The canonical substitution survives the finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_compatRefl_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifPropsScript.sml" "COMPAT_REFL"
  (fmap_as_finite_support_parameters := [s])]
theorem compatRefl {α : Type} (s : HolFiniteMapExact Nat (Term α)) (hw : wfs s) : compatible s s :=
  ⟨hw, hw, fun t => (walkstarSubmap s s t ⟨HolFiniteMapExact.submap_refl s, hw⟩).symm⟩

/-- The canonical substitution survives the finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_compatTrans_s2 {α : Type}
    (s2 : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2)).lookup key = s2.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2)).finiteSupport = s2.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2) = s2 :=
  holFmapAsFiniteSupportParamWitness_vR_subst s2 key

/-- The canonical substitution survives the finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_compatTrans_s1 {α : Type}
    (s1 : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1)).lookup key = s1.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1)).finiteSupport = s1.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1) = s1 :=
  holFmapAsFiniteSupportParamWitness_vR_subst s1 key

/-- The canonical substitution survives the finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_compatTrans_s0 {α : Type}
    (s0 : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s0)).lookup key = s0.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s0)).finiteSupport = s0.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s0) = s0 :=
  holFmapAsFiniteSupportParamWitness_vR_subst s0 key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifPropsScript.sml" "COMPAT_TRANS"
  (fmap_as_finite_support_parameters := [s2, s1, s0])]
theorem compatTrans {α : Type} (s2 : HolFiniteMapExact Nat (Term α))
    (s1 : HolFiniteMapExact Nat (Term α)) (s0 : HolFiniteMapExact Nat (Term α))
    (h : compatible s2 s1 ∧ compatible s1 s0) : compatible s2 s0 := by
  refine ⟨h.1.1, h.2.2.1, ?_⟩
  intro t
  calc
    walkstar s2 (walkstar s0 t) = walkstar s2 (walkstar s1 (walkstar s0 t)) := (h.1.2.2 _).symm
    _ = walkstar s2 (walkstar s1 t) := congrArg (walkstar s2) (h.2.2.2 t)
    _ = walkstar s2 t := h.1.2.2 t

/-- The canonical substitution survives the finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_compatExtend_sx {α : Type}
    (sx : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).lookup key = sx.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).finiteSupport = sx.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx) = sx :=
  holFmapAsFiniteSupportParamWitness_vR_subst sx key

/-- The canonical substitution survives the finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_compatExtend_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifPropsScript.sml" "COMPAT_extend"
  (fmap_as_finite_support_parameters := [sx, s])]
theorem compatExtend {α : Type} (sx : HolFiniteMapExact Nat (Term α))
    (s : HolFiniteMapExact Nat (Term α)) (vx : Nat) (tx : Term α)
    (h : compatible sx s ∧ wfs (s.updateEq (vx, tx)) ∧ vx ∉ s.domain ∧
      walkstar sx (.var vx) = walkstar sx tx) : compatible sx (s.updateEq (vx, tx)) := by
  refine ⟨h.1.1, h.2.1, ?_⟩
  have equality : walkstar sx (.var vx) = walkstar sx (walkstar s tx) :=
    h.2.2.2.trans (h.1.2.2 tx).symm
  intro t
  calc
    walkstar sx (walkstar (s.updateEq (vx, tx)) t) = walkstar sx (walkstar s t) :=
      walkstarExtend sx s vx tx ⟨h.1.1, h.2.1, h.2.2.1, equality⟩ t
    _ = walkstar sx t := h.1.2.2 t

/-- The canonical substitution survives the finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_compatMoreSpecific_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

/-- The canonical substitution survives the finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_compatMoreSpecific_s0 {α : Type}
    (s0 : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s0)).lookup key = s0.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s0)).finiteSupport = s0.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s0) = s0 :=
  holFmapAsFiniteSupportParamWitness_vR_subst s0 key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifPropsScript.sml" "COMPAT_more_specific"
  (fmap_as_finite_support_parameters := [s, s0])]
theorem compatMoreSpecific {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (s0 : HolFiniteMapExact Nat (Term α)) : compatible s s0 ↔
      wfs s ∧ wfs s0 ∧ ∀ t1 t2, walkstar s0 t1 = walkstar s0 t2 →
        walkstar s t1 = walkstar s t2 := by
  constructor
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    intro t1 t2 equal
    calc
      walkstar s t1 = walkstar s (walkstar s0 t1) := (h.2.2 t1).symm
      _ = walkstar s (walkstar s0 t2) := congrArg (walkstar s) equal
      _ = walkstar s t2 := h.2.2 t2
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    intro t
    apply h.2.2 (walkstar s0 t) t
    exact (walkstarSubmap s0 s0 t ⟨HolFiniteMapExact.submap_refl s0, h.2.1⟩).symm

end Flapjack.HOL.Unification

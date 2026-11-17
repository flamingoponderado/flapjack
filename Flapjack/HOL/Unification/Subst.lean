module

public import Flapjack.HOL.Unification.Term
public import Flapjack.FiniteMap.BroadCodec
public import Flapjack.FiniteMap.SubmapExact

@[expose] public section

/-! Finite substitutions and their original variable-dependency relation. -/
namespace Flapjack.HOL.Unification

/-- Canonical map codec roundtrip for the dependency relation's substitution. -/
theorem holFmapAsFiniteSupportParamWitness_vR_subst {α κ : Type}
    (subst : HolFiniteMapExact κ (Term α)) (key : κ) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).lookup key = subst.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).finiteSupport = subst.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst) = subst := by
  cases subst
  exact ⟨rfl, rfl, rfl⟩

@[hol "HOL/examples/algorithms/unification/triangular/first-order/substScript.sml" "vR_def"
  (fmap_as_finite_support_parameters := [subst])]
def vR {α κ : Type} (subst : HolFiniteMapExact κ (Term α)) (y : Nat) (x : κ) : Prop :=
  match subst.lookup x with
  | some t => vars t y
  | none => False

/-- Canonical map codec roundtrip for the well-formedness predicate. -/
theorem holFmapAsFiniteSupportParamWitness_wfs_subst {α : Type}
    (subst : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).lookup key = subst.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).finiteSupport = subst.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst) = subst :=
  holFmapAsFiniteSupportParamWitness_vR_subst subst key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/substScript.sml" "wfs_def"
  (fmap_as_finite_support_parameters := [subst])]
def wfs {α : Type} (subst : HolFiniteMapExact Nat (Term α)) : Prop :=
  WellFounded (vR subst)

/-- The larger substitution's canonical map roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_wfsSubmap_sx {α : Type}
    (sx : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).lookup key = sx.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).finiteSupport = sx.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx) = sx :=
  holFmapAsFiniteSupportParamWitness_vR_subst sx key

/-- The smaller substitution's canonical map roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_wfsSubmap_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/substScript.sml" "wfs_SUBMAP"
  (fmap_as_finite_support_parameters := [sx, s])]
theorem wfsSubmap {α : Type} (sx : HolFiniteMapExact Nat (Term α))
    (s : HolFiniteMapExact Nat (Term α))
    (h : wfs sx ∧ s.submap sx) : wfs s := by
  apply Subrelation.wf _ h.1
  intro y x edge
  unfold vR at edge ⊢
  cases found : s.lookup x with
  | none => simp [found] at edge
  | some t =>
    have found' := h.2 x t found
    simpa [found, found'] using edge

end Flapjack.HOL.Unification

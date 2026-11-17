module

public import Flapjack.Compiler.Inference.Unify.Walkstar.Submap
public import Flapjack.Compiler.Inference.Unify.Walkstar.Idempotent

@[expose] public section

/-! Compatibility of inference substitutions. -/
namespace Flapjack.Compiler.Inference.Unify

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tCompat_s1
    (s1 : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1)).lookup key = s1.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1)).finiteSupport = s1.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1) = s1 :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s1 key

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tCompat_s2
    (s2 : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2)).lookup key = s2.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2)).finiteSupport = s2.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2) = s2 :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s2 key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_compat_def"
  (fmap_as_finite_support_parameters := [s1, s2])]
def tCompat (s1 : HolFiniteMapExact Nat InferT) (s2 : HolFiniteMapExact Nat InferT) : Prop :=
  tWfs s1 ∧ tWfs s2 ∧ ∀ t, tWalkstar s2 (tWalkstar s1 t) = tWalkstar s2 t

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tCompatRefl_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_compat_refl"
  (fmap_as_finite_support_parameters := [s])]
theorem tCompatRefl (s : HolFiniteMapExact Nat InferT) (h : tWfs s) : tCompat s s :=
  ⟨h, h, tWalkstarIdempotent s h⟩

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tCompatTrans_a
    (a : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad a)).lookup key = a.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad a)).finiteSupport = a.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad a) = a :=
  holFmapAsFiniteSupportParamWitness_tVR_subst a key

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tCompatTrans_b
    (b : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad b)).lookup key = b.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad b)).finiteSupport = b.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad b) = b :=
  holFmapAsFiniteSupportParamWitness_tVR_subst b key

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tCompatTrans_c
    (c : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad c)).lookup key = c.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad c)).finiteSupport = c.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad c) = c :=
  holFmapAsFiniteSupportParamWitness_tVR_subst c key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_compat_trans"
  (fmap_as_finite_support_parameters := [a, b, c])]
theorem tCompatTrans (a : HolFiniteMapExact Nat InferT) (b : HolFiniteMapExact Nat InferT)
    (c : HolFiniteMapExact Nat InferT) (h : tCompat a b ∧ tCompat b c) : tCompat a c := by
  refine ⟨h.1.1, h.2.2.1, ?_⟩
  intro t
  calc
    tWalkstar c (tWalkstar a t) = tWalkstar c (tWalkstar b (tWalkstar a t)) := (h.2.2.2 _).symm
    _ = tWalkstar c (tWalkstar b t) := congrArg (tWalkstar c) (h.1.2.2 t)
    _ = tWalkstar c t := h.2.2.2 t

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_submapTCompat_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s key

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_submapTCompat_sx
    (sx : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).lookup key = sx.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).finiteSupport = sx.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx) = sx :=
  holFmapAsFiniteSupportParamWitness_tVR_subst sx key

@[hol "cakeml/compiler/inference/unifyScript.sml" "SUBMAP_t_compat"
  (fmap_as_finite_support_parameters := [sx, s])]
theorem submapTCompat (sx : HolFiniteMapExact Nat InferT) (s : HolFiniteMapExact Nat InferT)
    (h : tWfs sx ∧ s.submap sx) : tCompat s sx :=
  ⟨tWfsSubmap s sx ⟨h.1, h.2⟩, h.1, fun t => (tWalkstarSubmap s sx t ⟨h.2, h.1⟩).symm⟩

end Flapjack.Compiler.Inference.Unify

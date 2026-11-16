module

public import Flapjack.Compiler.Inference.Unify.Encoding
public import Flapjack.HOL.Unification.Subst

@[expose] public section

/-! Inference-type substitutions through the first-order term encoding. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_vars_def"]
def tVars (t : InferT) : Nat → Prop := vars (encodeInferT t)

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tVR_subst {κ : Type}
    (subst : HolFiniteMapExact κ InferT) (key : κ) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).lookup key = subst.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).finiteSupport = subst.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst) = subst := by
  cases subst
  exact ⟨rfl, rfl, rfl⟩

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_vR_def"
  (fmap_as_finite_support_parameters := [subst])]
def tVR {κ : Type} (subst : HolFiniteMapExact κ InferT) : Nat → κ → Prop :=
  vR (subst.map2 (fun p => encodeInferT p.2))

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tWfs_subst
    (subst : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).lookup key = subst.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).finiteSupport = subst.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst) = subst :=
  holFmapAsFiniteSupportParamWitness_tVR_subst subst key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_wfs_def"
  (fmap_as_finite_support_parameters := [subst])]
def tWfs (subst : HolFiniteMapExact Nat InferT) : Prop :=
  wfs (subst.map2 (fun p => encodeInferT p.2))

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tVREqn_subst {κ : Type}
    (subst : HolFiniteMapExact κ InferT) (key : κ) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).lookup key = subst.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).finiteSupport = subst.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst) = subst :=
  holFmapAsFiniteSupportParamWitness_tVR_subst subst key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_vR_eqn"
  (fmap_as_finite_support_parameters := [subst])]
theorem tVREqn {κ : Type} (subst : HolFiniteMapExact κ InferT) (x : κ) (y : Nat) :
    tVR subst y x ↔ match subst.lookup x with
      | none => False
      | some t => tVars t y := by
  cases found : subst.lookup x <;> simp [tVR, tVars, vR, found]

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tWfsEqn_subst
    (subst : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).lookup key = subst.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).finiteSupport = subst.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst) = subst :=
  holFmapAsFiniteSupportParamWitness_tVR_subst subst key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_wfs_eqn"
  (fmap_as_finite_support_parameters := [subst])]
theorem tWfsEqn (subst : HolFiniteMapExact Nat InferT) :
    tWfs subst ↔ WellFounded (tVR subst) := Iff.rfl

end Flapjack.Compiler.Inference.Unify

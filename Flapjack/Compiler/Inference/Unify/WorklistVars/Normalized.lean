module

public import Flapjack.Compiler.Inference.Unify.WorklistVars
public import Flapjack.HOL.Unification.Walkstar
public import Mathlib.Data.Set.Lattice

@[expose] public section

/-! Variables of encoded lists after first-order normalization. -/

namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- The canonical substitution survives the finite-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_varsWalkstarEncodeInferTs_s
    (s : HolFiniteMapExact Nat (Term Atom)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "cakeml/compiler/inference/unifyScript.sml" "vars_walkstar_encode_infer_ts"
  (fmap_as_finite_support_parameters := [s])]
theorem varsWalkstarEncodeInferTs (s : HolFiniteMapExact Nat (Term Atom)) (hw : wfs s)
    (ts : List InferT) :
    vars (walkstar s (encodeInferTs ts)) =
      Set.sUnion (Set.image (fun t => vars (walkstar s (encodeInferT t))) (fun t => t ∈ ts)) := by
  induction ts with
  | nil =>
    funext v
    apply propext
    rw [walkstarEq s hw]
    simp [encodeInferTs, walk, vars]
    change v ∉ Set.sUnion (Set.image (fun t => vars (walkstar s (encodeInferT t))) (fun _ => False))
    simp only [Set.mem_sUnion]
    rintro ⟨_, ⟨_, impossible, _⟩, _⟩
    exact impossible
  | cons t ts ih =>
    funext v
    apply propext
    rw [walkstarEq s hw]
    simp [encodeInferTs, walk, vars, ih]
    change (vars (walkstar s (encodeInferT t)) v ∨
      (∃ p : Nat → Prop, (∃ a, a ∈ ts ∧ vars (walkstar s (encodeInferT a)) = p) ∧ p v)) ↔
      (∃ p : Nat → Prop, (∃ a, (a = t ∨ a ∈ ts) ∧
        vars (walkstar s (encodeInferT a)) = p) ∧ p v)
    simp

end Flapjack.Compiler.Inference.Unify

module

public import Flapjack.Compiler.Inference.Unify.Walkstar
public import Flapjack.HOL.Unification.Walkstar.Occurs

@[expose] public section

namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- Occurrence through the inference-type encoding. The first-order occurrence
    model is only source-reviewed under well-formed substitutions, so this
    definition is not yet tagged as the unconditional HOL definition. -/
def tOc (s : HolFiniteMapExact Nat InferT) (t : InferT) (v : Nat) : Prop :=
  Oc (s.map2 (fun p => encodeInferT p.2)) (encodeInferT t) v

private theorem encodedListOc (s : HolFiniteMapExact Nat InferT) (hw : tWfs s)
    (ts : List InferT) (v : Nat) :
    Oc (s.map2 (fun p => encodeInferT p.2)) (encodeInferTs ts) v ↔
      ∃ t ∈ ts, tOc s t v := by
  induction ts with
  | nil =>
    rw [ocWalking _ _ _ hw]
    simp [encodeInferTs, walk]
  | cons t ts ih =>
    rw [ocWalking _ _ _ hw]
    simp [encodeInferTs, walk, tOc, ih]

/-- The canonical substitution survives the finite-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_tOcEqn_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_oc_eqn"
  (fmap_as_finite_support_parameters := [s])]
theorem tOcEqn (s : HolFiniteMapExact Nat InferT) (hw : tWfs s)
    (t : InferT) (v : Nat) : tOc s t v ↔ match tWalk s t with
      | .uvar u => v = u
      | .app ts _ => ∃ t ∈ ts, tOc s t v
      | .varDb _ => False := by
  unfold tOc
  rw [ocWalking _ _ _ hw, encodeWalk s hw t]
  cases tw : tWalk s t with
  | uvar u => simp [encodeInferT]
  | varDb n => simp [encodeInferT]
  | app ts tc =>
    simp only [encodeInferT]
    rw [ocWalking _ _ _ hw]
    simp only [walk]
    rw [ocWalking _ (.pair (.const (.tcTag tc)) (encodeInferTs ts)) v hw]
    simp only [walk]
    rw [ocWalking _ (.const (.tcTag tc)) v hw]
    simp only [walk, false_or]
    exact encodedListOc s hw ts v

end Flapjack.Compiler.Inference.Unify

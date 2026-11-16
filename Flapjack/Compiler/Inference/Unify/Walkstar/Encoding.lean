module

public import Flapjack.Compiler.Inference.Unify.Walkstar.Induction

@[expose] public section

namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_encodeWalkstar_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s key

@[hol "cakeml/compiler/inference/unifyScript.sml" "encode_walkstar"
  (fmap_as_finite_support_parameters := [s])]
theorem encodeWalkstar (s : HolFiniteMapExact Nat InferT) (t : InferT) (hw : tWfs s) :
    walkstar (s.map2 (fun p => encodeInferT p.2)) (encodeInferT t) = encodeInferT (tWalkstar s t) := by
  revert t
  apply tWalkstarInd s hw
  intro t ih
  rw [walkstarEq _ hw, encodeWalk s hw t, walkstarEqn s hw t]
  cases heq : tWalk s t with
  | varDb n => simp [encodeInferT]
  | uvar n => simp [encodeInferT]
  | app ts tc =>
    simp only [encodeInferT]
    rw [walkstarEq _ hw]
    simp only [walk]
    rw [walkstarEq _ hw]
    simp only [walk]
    rw [walkstarEq _ hw]
    simp only [walk]
    congr 2
    have each : ∀ a ∈ ts,
        walkstar (s.map2 (fun p => encodeInferT p.2)) (encodeInferT a) =
          encodeInferT (tWalkstar s a) := by
      intro a ha
      exact ih ts tc a ⟨heq, ha⟩
    clear ih heq t tc
    induction ts with
    | nil =>
      rw [walkstarEq _ hw]
      simp [encodeInferTs, walk]
    | cons a ts ihList =>
      rw [walkstarEq _ hw]
      simp only [encodeInferTs, walk, List.map_cons]
      rw [each a (by simp)]
      apply congrArg (Term.pair (encodeInferT (tWalkstar s a)))
      apply ihList
      intro b hb
      exact each b (by simp [hb])

end Flapjack.Compiler.Inference.Unify

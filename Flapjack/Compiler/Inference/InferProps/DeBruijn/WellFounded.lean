module

public import Flapjack.Compiler.Inference.InferProps.DeBruijn.Vars

@[expose] public section

/-! Well-founded inference substitutions are preserved by de Bruijn shifts. -/
namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.Unify

/-- The substitution parameter survives the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_incWfs_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s key

/-- Shifting each range value preserves the original well-foundedness condition. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "inc_wfs"
  (fmap_as_finite_support_parameters := [s])]
theorem incWfs (n : Nat) (s : HolFiniteMapExact Nat InferT) (h : tWfs s) :
    tWfs (s.map2 (fun p => inferDeBruijnInc n p.2)) := by
  apply (tWfsEqn _).2
  have relationEq : tVR (s.map2 (fun p => inferDeBruijnInc n p.2)) = tVR s := by
    funext a b
    apply propext
    rw [tVREqn, tVREqn]
    cases found : s.lookup b with
    | none => simp [found]
    | some t => simp [found, tVarsInc]
  rw [relationEq]
  exact (tWfsEqn s).1 h

end Flapjack.Compiler.Inference.InferProps

module

public import Flapjack.Compiler.Inference.Infer
public import Flapjack.FiniteMap.BroadCodec

@[expose] public section

/-!
# Substitution lookup for a type variable

Lean counterpart of `infer_subst_var_def`: a type variable is replaced by the
mapped value when the canonical finite-map substitution has one.  The map
parameter is the reviewed `HolFiniteMapExact` translation, and its codec
witness is declared beside the tagged definition.
-/

namespace Flapjack.Compiler.Inference.InferProps

open Flapjack.Compiler.Inference

/-- Canonical codec roundtrip for the substitution-map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_inferSubstVar_s
    (s : HolFiniteMapExact Nat Nat) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
      (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
      FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s := by
  cases s
  exact ⟨rfl, rfl, rfl⟩

/-- Original `infer_subst_var_def`: substitute a type variable through a map. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "infer_subst_var_def"
  (fmap_as_finite_support_parameters := [s])]
def inferSubstVar (s : HolFiniteMapExact Nat Nat) : InferT → InferT
  | .uvar n =>
    match s.lookup n with
    | none => .uvar n
    | some tv => .varDb tv
  | t => t

end Flapjack.Compiler.Inference.InferProps

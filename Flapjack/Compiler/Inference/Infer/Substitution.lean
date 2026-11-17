module

public import Flapjack.Compiler.Inference.InferT
public import Flapjack.FiniteMap.BroadCodec

@[expose] public section

namespace Flapjack.Compiler.Inference.Infer.Substitution

/-- The canonical input substitution survives the finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_inferSubst_subst
    (subst : HolFiniteMapExact Nat Nat) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).lookup key = subst.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).finiteSupport = subst.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst) = subst := by
  cases subst
  exact ⟨rfl, rfl, rfl⟩

/-- Substitute inference variables using the canonical finite-map carrier. -/
@[hol "cakeml/compiler/inference/inferScript.sml" "infer_subst_def"
  (fmap_as_finite_support_parameters := [subst])]
def inferSubst (subst : HolFiniteMapExact Nat Nat) : InferT → InferT
  | .varDb n => .varDb n
  | .app ts name => .app (ts.map (inferSubst subst)) name
  | .uvar n => match subst.lookup n with
    | none => .uvar n
    | some value => .varDb value
termination_by t => sizeOf t

end Flapjack.Compiler.Inference.Infer.Substitution

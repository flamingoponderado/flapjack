module

public import Flapjack.Compiler.Inference.Unify.Walkstar
public import Flapjack.HOL.Unification.Walkstar.Empty
public import Flapjack.FiniteMap.MapKeys

@[expose] public section

namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_walkstar_FEMPTY"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem tWalkstarEmpty : ∀ t : InferT,
    tWalkstar Flapjack.HolFiniteMapExact.holEmpty t = t := by
  intro t
  have encEmpty : (HolFiniteMapExact.holEmpty : HolFiniteMapExact Nat InferT).map2
      (fun p => encodeInferT p.2) = HolFiniteMapExact.holEmpty := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    rfl
  unfold tWalkstar
  rw [encEmpty, walkstarEmpty, decodeLeftInverse.1]

end Flapjack.Compiler.Inference.Unify

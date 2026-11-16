module

public import Flapjack.Compiler.Inference.Unify.Unification
public import Flapjack.Compiler.Inference.Unify.Walk
public import Flapjack.HOL.Unification.UnifDef.Choice

@[expose] public section

/-! Connection between the selected source specification and inference model. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- Under the original substitution guard, decoding the selected
    first-order unifier agrees with the existing inference model. This is a
    Lean correspondence lemma: HOL's `t_unify_def` itself has no guard, and
    the option-wrapped finite-map result still needs a reviewed qualifier. -/
theorem tUnifyModelEqSpecified (s : HolFiniteMapExact Nat InferT) (t1 t2 : InferT)
    (hw : tWfs s) :
    (specifiedUnify (encodeSubst s) (encodeInferT t1) (encodeInferT t2)).map decodeSubst =
      tUnifyModel s t1 t2 := by
  change wfs (encodeSubst s) at hw
  rw [specifiedUnifyEqAux _ _ _ hw]
  rfl

end Flapjack.Compiler.Inference.Unify

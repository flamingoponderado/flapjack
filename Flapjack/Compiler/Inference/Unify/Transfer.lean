module

public import Flapjack.HOL.Transfer.Relation
public import Flapjack.Compiler.Inference.Unify.Machine

@[expose] public section

/-!
# The unify transfer relation `RKC` is surjective

Counterpart of `surj_RKC` from `cakeml/compiler/inference/unifyScript.sml`. The
relation itself (`RKC_def`) is ported in `Unify/Machine.lean`; this module adds
the surjectivity law over the reviewed transfer relation.
-/

namespace Flapjack.Compiler.Inference.Unify

open Flapjack.HOL.Transfer.Relation

/-- Original `surj_RKC`: every inference type is related to its encoding. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "surj_RKC"]
theorem surjRkc : surj rkc := by
  intro ct
  exact ⟨encodeInferT ct, rfl⟩

end Flapjack.Compiler.Inference.Unify

module

public import Flapjack.Compiler.Inference.Infer.HOLState
public import Flapjack.Compiler.Inference.Unify.Walkstar.Empty

@[expose] public section

/-!
# Initial inference state facts

Lean counterparts of the `inferProps` statements about the initial inference
state and the empty substitution.  The state carrier is
`Infer.HOLState.InferState` whose substitution field is the canonical
`HolFiniteMapExact` translation of the HOL `|->` map, and the roundtrip witness is
re-exported here so the tagged declarations in this module have their canonical
witness beside them.
-/

namespace Flapjack.Compiler.Inference.InferProps

open Flapjack.Compiler.Inference.Infer.HOLState
open Flapjack.Compiler.Inference.Unify

/-- The canonical state codec roundtrip, re-exported from the carrier module. -/
theorem holFmapAsFiniteSupportWitness :
    (∀ s : InferState, ofBroad (toBroad s) = s) ∧
    (∀ s : InferStateBroad, toBroad (ofBroad s) = s) :=
  Flapjack.Compiler.Inference.Infer.HOLState.holFmapAsFiniteSupportWitness

/-- Original `hide_def`: the identity helper. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "hide_def"]
def hide {α : Type} (x : α) : α := x

/-- Original `init_infer_state_next_uvar`: the fresh-variable counter restarts. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "init_infer_state_next_uvar"]
theorem initInferState_nextUvar (s : InferState) : (initInferState s).nextUvar = 0 := rfl

/-- Original `init_infer_state_subst`: the substitution starts empty. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "init_infer_state_subst"
  (fmap_as_finite_support := [subst])]
theorem initInferState_subst (s : InferState) :
    (initInferState s).subst =
      (Flapjack.HolFiniteMapExact.holEmpty : HolFiniteMapExact Nat InferT) := rfl

/-- Original `t_wfs_FEMPTY`: the empty substitution is well formed. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "t_wfs_FEMPTY"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem tWfsEmpty :
    tWfs (Flapjack.HolFiniteMapExact.holEmpty : HolFiniteMapExact Nat InferT) := by
  unfold tWfs
  have encEmpty :
      (Flapjack.HolFiniteMapExact.holEmpty : HolFiniteMapExact Nat InferT).map2
        (fun p => encodeInferT p.2) = Flapjack.HolFiniteMapExact.holEmpty := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    rfl
  rw [encEmpty]
  exact Flapjack.HOL.Unification.wfsEmpty

/-- Original `t_wfs_init_infer_state`: the initial substitution is well formed. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "t_wfs_init_infer_state"
  (fmap_as_finite_support := [subst])]
theorem tWfs_initInferState (s : InferState) :
    tWfs (initInferState s).subst := by
  rw [initInferState_subst]
  exact tWfsEmpty

end Flapjack.Compiler.Inference.InferProps

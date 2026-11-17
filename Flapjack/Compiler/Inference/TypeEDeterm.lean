module

public import Flapjack.TypeSystemHOL.Patterns

@[expose] public section

/-! Pattern-typing prerequisites for inference determinacy. -/
namespace Flapjack.Compiler.Inference.TypeEDeterm
open Flapjack Flapjack.TypeSystemHOL Flapjack.AstHOL

/-- Pattern typing preserves the source ordering of bound names. -/
@[hol "cakeml/compiler/inference/proofs/type_eDetermScript.sml" "type_p_pat_bindings"]
theorem typePPatBindings :
    (∀ tvs env p t bindings, TypeP tvs env p t bindings → bindings.map Prod.fst = patBindings p) ∧
    (∀ tvs env ps ts bindings, TypePs tvs env ps ts bindings → bindings.map Prod.fst = patsBindings ps) := by
  constructor <;> intro tvs env p t bindings typed
  all_goals
    first
    | refine TypeP.rec (motive_1 := fun p t bindings _ => bindings.map Prod.fst = patBindings p)
        (motive_2 := fun ps ts bindings _ => bindings.map Prod.fst = patsBindings ps)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
    | refine TypePs.rec (motive_1 := fun p t bindings _ => bindings.map Prod.fst = patBindings p)
        (motive_2 := fun ps ts bindings _ => bindings.map Prod.fst = patsBindings ps)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
    all_goals simp_all [patBindings, patsBindings, List.map_append]
end Flapjack.Compiler.Inference.TypeEDeterm

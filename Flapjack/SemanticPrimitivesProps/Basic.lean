module

public import Flapjack.SemanticPrimitivesHOL

@[expose] public section

/-! Opening record and Boolean-value laws of `semanticPrimitivesPropsScript`. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.SemanticPrimitivesHOL

/-- Rewriting an environment's value part with its own value part is the identity. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "with_same_v"]
theorem with_same_v {α : Type} (env : SemEnv α) : { env with v := env.v } = env := rfl

/-- Rebuilding an environment from its own parts is the identity. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "unchanged_env"]
theorem unchanged_env {α : Type} (env : SemEnv α) : { v := env.v, c := env.c } = env := rfl

/-- Rewriting the clock with the state's own clock is the identity. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "with_same_clock"]
theorem with_same_clock {σ : Type} (state : State σ) :
    { state with clock := state.clock } = state := rfl

/-- The Boolean value encoding is injective. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "Boolv_11"]
theorem boolValue_eq_iff (left right : Bool) :
    boolValue left = boolValue right ↔ left = right := by
  cases left
  all_goals cases right
  all_goals simp [boolValue]
  all_goals decide

end Flapjack.SemanticPrimitivesProps

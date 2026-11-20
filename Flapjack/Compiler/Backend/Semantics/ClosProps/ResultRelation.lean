module

public import Flapjack.SemanticPrimitivesProps.ResultRelation
public import Flapjack.HolRef

@[expose] public section

/-! Successful-result inversions for the standard result relation. -/
namespace Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL
open Flapjack.SemanticPrimitivesProps

/-- A source result relates to a successful value exactly when it is that
value under the value relation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "result_rel_Rval2"]
theorem resultRel_Rval2 {α β γ δ : Type} (R1 : α → β → Prop) (R2 : γ → δ → Prop)
    (r : Result α γ) (v : β) :
    resultRel R1 R2 r (.val v) ↔ ∃ v' : α, r = .val v' ∧ R1 v' v := by
  cases r with
  | val a => simp [resultRel]
  | err e => simp [resultRel]

end Flapjack.Compiler.Backend.ClosProps

module

public import Flapjack.SemanticPrimitivesProps.ResultRelation

@[expose] public section

/-! Result-shape prerequisite for source evaluator oracle semantics. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- A related result is a value, a raised value, or an abort. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "result_rel_IMP_cases"]
theorem resultRel_imp_cases {α β γ δ : Type} (values : α → β → Prop) (errors : γ → δ → Prop)
    (r : Result α γ) (r' : Result β δ) (_related : resultRel values errors r r') :
    (∃ x, r = .val x) ∨ (∃ y, r = .err (.raise y)) ∨ ∃ a, r = .err (.abort a) := by
  cases r with
  | val x => exact .inl ⟨x, rfl⟩
  | err e =>
    cases e with
    | raise y => exact .inr (.inl ⟨y, rfl⟩)
    | abort a => exact .inr (.inr ⟨a, rfl⟩)

end Flapjack.Compiler.Backend.SourceEval.Proofs

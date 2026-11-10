module

public import Flapjack.SemanticPrimitivesHOL

@[expose] public section

/-! Relations on CakeML evaluation results. -/
namespace Flapjack.SemanticPrimitivesProps
open SemanticPrimitivesHOL

/-- Relate raised payloads using the given relation and preserve aborts. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "exc_rel_def"]
def excRel {α β : Type} (rel : α → β → Prop) : ErrorResult α → ErrorResult β → Prop
  | .raise a, .raise b => rel a b
  | .abort a, .abort b => a = b
  | _, _ => False

/-- Relate successful results and errors using their respective relations. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "result_rel_def"]
def resultRel {α β γ δ : Type} (values : α → β → Prop) (errors : γ → δ → Prop) :
    Result α γ → Result β δ → Prop
  | .val a, .val b => values a b
  | .err a, .err b => excRel errors a b
  | _, _ => False

/-- Check raised payloads; aborts satisfy the predicate unconditionally. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "every_error_result_def"]
def everyErrorResult {α : Type} (predicate : α → Prop) : ErrorResult α → Prop
  | .raise value => predicate value
  | .abort _ => True

/-- Apply separate predicates to successful values and raised payloads. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "every_result_def"]
def everyResult {α β : Type} (values : α → Prop) (errors : β → Prop) : Result α β → Prop
  | .val value => values value
  | .err error => everyErrorResult errors error

/-- Flapjack infrastructure: weakening the payload relation weakens the error relation. -/
theorem excRel_mono {α β : Type} (rel rel' : α → β → Prop)
    (weaken : ∀ a b, rel a b → rel' a b) (a : ErrorResult α) (b : ErrorResult β)
    (related : excRel rel a b) : excRel rel' a b := by
  cases a <;> cases b <;> simp_all [excRel]

end Flapjack.SemanticPrimitivesProps

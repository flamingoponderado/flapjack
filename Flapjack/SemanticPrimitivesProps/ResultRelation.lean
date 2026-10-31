import Flapjack.SemanticPrimitivesHOL

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

/-- Flapjack infrastructure: weakening the payload relation weakens the error relation. -/
theorem excRel_mono {α β : Type} (rel rel' : α → β → Prop)
    (weaken : ∀ a b, rel a b → rel' a b) (a : ErrorResult α) (b : ErrorResult β)
    (related : excRel rel a b) : excRel rel' a b := by
  cases a <;> cases b <;> simp_all [excRel]

end Flapjack.SemanticPrimitivesProps

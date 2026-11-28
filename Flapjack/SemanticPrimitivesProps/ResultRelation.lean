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

/-- A raised payload on the left is related exactly to the results that raise it. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "exc_rel_raise1"]
theorem excRel_raise1 {α β : Type} (rel : α → β → Prop) (value : α) (error : ErrorResult β) :
    excRel rel (.raise value) error ↔ ∃ value', error = .raise value' ∧ rel value value' := by
  cases error
  all_goals simp [excRel]

/-- A raised payload on the right is related exactly to the results that raise it. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "exc_rel_raise2"]
theorem excRel_raise2 {α β : Type} (rel : α → β → Prop) (error : ErrorResult α) (value : β) :
    excRel rel error (.raise value) ↔ ∃ value', error = .raise value' ∧ rel value' value := by
  cases error
  all_goals simp [excRel]

/-- An abort on the left is related exactly to the identical abort (HOL's
`exc_rel_type_error1`). -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "exc_rel_type_error1"]
theorem excRel_typeError1 {α β : Type} (rel : α → β → Prop)
    (abort : Abort) (error : ErrorResult β) :
    excRel rel (.abort abort) error ↔ error = .abort abort := by
  cases error
  all_goals simp [excRel, eq_comm]

/-- An abort on the right is related exactly to the identical abort (HOL's
`exc_rel_type_error2`). -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "exc_rel_type_error2"]
theorem excRel_typeError2 {α β : Type} (rel : α → β → Prop)
    (error : ErrorResult α) (abort : Abort) :
    excRel rel error (.abort abort) ↔ error = .abort abort := by
  cases error
  all_goals simp [excRel, eq_comm]

/-- A reflexive payload relation makes the error relation reflexive. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "exc_rel_refl"]
theorem excRel_refl {α : Type} (rel : α → α → Prop) (refl : ∀ x, rel x x) (error : ErrorResult α) :
    excRel rel error error := by
  cases error
  all_goals simp [excRel, refl]

/-- A transitive payload relation makes the error relation transitive. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "exc_rel_trans"]
theorem excRel_trans {α : Type} (rel : α → α → Prop)
    (trans : ∀ x y z, rel x y ∧ rel y z → rel x z) :
    ∀ x y z, excRel rel x y ∧ excRel rel y z → excRel rel x z := by
  intro x y z ⟨xy, yz⟩
  cases x
  all_goals cases y
  all_goals cases z
  all_goals first
    | exact trans _ _ _ ⟨xy, yz⟩
    | simp_all [excRel]

/-- A successful value on the left is related exactly to the results holding it. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "result_rel_Rval"]
theorem resultRel_val {α β γ δ : Type} (values : α → β → Prop) (errors : γ → δ → Prop)
    (value : α) (other : Result β δ) :
    resultRel values errors (.val value) other ↔
      ∃ value', other = .val value' ∧ values value value' := by
  cases other
  all_goals simp [resultRel]

/-- An error on the left is related exactly to the results carrying a related error. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "result_rel_Rerr1"]
theorem resultRel_err1 {α β γ δ : Type} (values : α → β → Prop) (errors : γ → δ → Prop)
    (error : ErrorResult γ) (other : Result β δ) :
    resultRel values errors (.err error) other ↔
      ∃ error', other = .err error' ∧ excRel errors error error' := by
  cases other
  all_goals simp [resultRel]

/-- An error on the right is related exactly to the results carrying a related error. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "result_rel_Rerr2"]
theorem resultRel_err2 {α β γ δ : Type} (values : α → β → Prop) (errors : γ → δ → Prop)
    (other : Result α γ) (error : ErrorResult δ) :
    resultRel values errors other (.err error) ↔
      ∃ error', other = .err error' ∧ excRel errors error' error := by
  cases other
  all_goals simp [resultRel]

/-- Reflexive payload relations make the result relation reflexive. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "result_rel_refl"]
theorem resultRel_refl {α β : Type} (values : α → α → Prop) (errors : β → β → Prop)
    (h : (∀ x, values x x) ∧ (∀ x, errors x x)) :
    ∀ (result : Result α β), resultRel values errors result result := by
  obtain ⟨valuesRefl, errorsRefl⟩ := h
  intro result
  cases result with
  | val value => exact valuesRefl value
  | err error => exact excRel_refl errors errorsRefl error

/-- Transitive payload relations make the result relation transitive. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "result_rel_trans"]
theorem resultRel_trans {α β : Type} (values : α → α → Prop) (errors : β → β → Prop)
    (h : (∀ x y z, values x y ∧ values y z → values x z) ∧
      (∀ x y z, errors x y ∧ errors y z → errors x z)) :
    ∀ x y z, resultRel values errors x y ∧ resultRel values errors y z →
      resultRel values errors x z := by
  obtain ⟨valuesTrans, errorsTrans⟩ := h
  intro x y z ⟨xy, yz⟩
  cases x
  all_goals cases y
  all_goals cases z
  all_goals first
    | exact valuesTrans _ _ _ ⟨xy, yz⟩
    | exact excRel_trans errors errorsTrans _ _ _ ⟨xy, yz⟩
    | simp_all [resultRel, excRel]

end Flapjack.SemanticPrimitivesProps

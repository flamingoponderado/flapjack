module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact
public import Flapjack.HolRef

@[expose] public section

/-! Composition of the flat declaration evaluator. -/
namespace Flapjack.Compiler.Backend.FlatSem

/-- Evaluation of an appended declaration list stops at the first error, or
continues with the second list after the first succeeds. HOL's three unused
universally quantified variables are vacuous and omitted here. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_decs_append"]
theorem evaluateDecs_append {C F : Type} (state : State C F)
    (first second : List FlatLang.Exp) :
    evaluateDecs state (first ++ second) =
      match evaluateDecs state first with
      | (next, none) => evaluateDecs next second
      | (next, some error) => (next, some error) := by
  induction first generalizing state with
  | nil => simp [evaluateDecs]
  | cons declaration rest ih =>
    simp only [List.cons_append, evaluateDecs]
    generalize h : fixClock state (evaluate ⟨[]⟩ state [declaration]) = step
    rcases step with ⟨next, result⟩
    cases result with
    | err error => rfl
    | val values =>
      cases values with
      | nil => rfl
      | cons first tail =>
        cases tail with
        | nil =>
          cases first with
          | conv ctor fields =>
            cases ctor <;> cases fields <;> simp_all
          | litv literal => rfl
          | closure env name body => rfl
          | recclosure env funs name => rfl
          | loc flag loc => rfl
          | vectorv values => rfl
        | cons second tail => cases first <;> simp

end Flapjack.Compiler.Backend.FlatSem

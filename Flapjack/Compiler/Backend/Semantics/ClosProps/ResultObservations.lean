module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.Semantics
public import Flapjack.Misc.List

@[expose] public section

/-! Shared observable consequences of the standard result relation used by the
Clos pass simulations. Flapjack proof infrastructure; no separately named HOL
declaration. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- The terminating outcome carried by an evaluator result, with timeout
represented by absence of a terminating observation. -/
def resultHasOutcome (result : Result (List Value) Value) (outcome : HolOutcome) : Prop :=
  match result with
  | .err (.abort .timeoutError) => False
  | .err (.abort (.ffiError event)) => outcome = .ffiOutcome event
  | _ => outcome = .success

/-- Pointwise case analysis of `resultHasOutcome`. -/
theorem resultHasOutcome_iff (result : Result (List Value) Value) (outcome : HolOutcome) :
    resultHasOutcome result outcome ↔
      (match result, outcome with
       | .err (.abort .timeoutError), _ => False
       | .err (.abort (.ffiError event)), outcome => outcome = .ffiOutcome event
       | _, outcome => outcome = .success) := by
  cases result with
  | val values => rfl
  | err error => cases error with
    | raise value => rfl
    | abort reason => cases reason <;> rfl

/-- The standard result relation, built from a value relation: related value
lists, related raised values and identical aborts. -/
def ResultRelOf (ValueRel : Value → Value → Prop) :
    Result (List Value) Value → Result (List Value) Value → Prop
  | .val left, .val right => List.Forall₂ ValueRel left right
  | .err (.raise left), .err (.raise right) => ValueRel left right
  | .err (.abort left), .err (.abort right) => left = right
  | _, _ => False

/-- Related results agree on type errors and all terminating observations. -/
theorem resultRel_observations {ValueRel : Value → Value → Prop}
    (left right : Result (List Value) Value) (related : ResultRelOf ValueRel left right) :
    (left = .err (.abort .typeError) ↔ right = .err (.abort .typeError)) ∧
    ∀ outcome : HolOutcome, resultHasOutcome left outcome ↔ resultHasOutcome right outcome := by
  cases left with
  | val values =>
    cases right with
    | val nextValues => simp [resultHasOutcome]
    | err error => cases error <;> simp [ResultRelOf] at related
  | err error =>
    cases error with
    | raise value =>
      cases right with
      | val values => simp [ResultRelOf] at related
      | err nextError =>
        cases nextError with
        | raise nextValue => simp [resultHasOutcome]
        | abort reason => cases related
    | abort reason =>
      cases right with
      | val values => simp [ResultRelOf] at related
      | err nextError =>
        cases nextError with
        | raise value => simp [ResultRelOf] at related
        | abort nextReason =>
          have same : reason = nextReason := related
          subst nextReason
          cases reason <;> simp [resultHasOutcome]

end Flapjack.Compiler.Backend.ClosProps

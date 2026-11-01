import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateCall
import Flapjack.Compiler.Backend.Semantics.DataProps.Jump

/-! Result-sensitive control invariant for data-language evaluation. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- The stack and handler invariant needed for recursive calls: continuing
and value-returning executions retain the entry control state, and a raised
exception uses the entry exception jump. Abort cases impose no condition.
This predicate is auxiliary and has no direct HOL declaration. -/
def stackResult {C F : Type} (source : State C F) (result : Option (Result (List Value) Value))
    (next : State C F) : Prop :=
  match result with
  | none | some (.val _) => next.stack = source.stack ∧ next.handler = source.handler
  | some (.err (.raise _)) =>
      ∃ jumped, jumpExc source = some jumped ∧ next.stack = jumped.stack ∧ next.handler = jumped.handler
  | some (.err (.abort _)) => True

/-- The result-sensitive invariant composes through sequential execution.
The induction hypotheses are precisely the invariants for the two components. -/
theorem evaluate_seq_stackResult {C F : Type} (first second : DataLang.Prog) (state next : State C F)
    (result : Option (Result (List Value) Value))
    (firstIH : ∀ before after : State C F, ∀ outcome,
      evaluate first before = (outcome, after) → stackResult before outcome after)
    (secondIH : ∀ before after : State C F, ∀ outcome,
      evaluate second before = (outcome, after) → stackResult before outcome after)
    (run : evaluate (.seq first second) state = (result, next)) : stackResult state result next := by
  rw [evaluate, fixClock_evaluate] at run
  cases firstRun : evaluate first state with
  | mk outcome mid =>
    rw [firstRun] at run
    have firstControl := firstIH state mid outcome firstRun
    cases outcome with
    | some stopped =>
      simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact firstControl
    | none =>
      have midControl : mid.stack = state.stack ∧ mid.handler = state.handler := firstControl
      have secondControl := secondIH mid next result run
      cases result with
      | none =>
        exact ⟨secondControl.1.trans midControl.1, secondControl.2.trans midControl.2⟩
      | some stopped =>
        cases stopped with
        | val values =>
          exact ⟨secondControl.1.trans midControl.1, secondControl.2.trans midControl.2⟩
        | err error =>
          cases error with
          | abort reason => trivial
          | raise value =>
            obtain ⟨jumped, jumpedRun, stack, handler⟩ := secondControl
            let originalJump := { state with stack := jumped.stack, handler := jumped.handler, locals := jumped.locals, localsSize := jumped.localsSize }
            refine ⟨originalJump, jumpExc_transport mid state jumped midControl.1.symm midControl.2.symm jumpedRun, ?_, ?_⟩
            · simpa [originalJump] using stack
            · simpa [originalJump] using handler

/-- The result-sensitive invariant composes through either conditional branch. -/
theorem evaluate_if_stackResult {C F : Type} (name : Nat) (yes no : DataLang.Prog) (state next : State C F)
    (result : Option (Result (List Value) Value))
    (yesIH : ∀ before after : State C F, ∀ outcome,
      evaluate yes before = (outcome, after) → stackResult before outcome after)
    (noIH : ∀ before after : State C F, ∀ outcome,
      evaluate no before = (outcome, after) → stackResult before outcome after)
    (run : evaluate (.ifThenElse name yes no) state = (result, next)) : stackResult state result next := by
  cases read : getVar name state.locals with
  | none =>
    simp [evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some value =>
    by_cases yes : isBool true value
    · apply yesIH state next result
      simpa [evaluate, read, yes] using run
    · by_cases no : isBool false value
      · apply noIH state next result
        simpa [evaluate, read, yes, no] using run
      · simp [evaluate, read, yes, no] at run
        obtain ⟨rfl, rfl⟩ := run
        trivial

/-- A raise either fails with a type error or ends at the exception jump. -/
theorem evaluate_raise_stackResult {C F : Type} (name : Nat) (state next : State C F)
    (result : Option (Result (List Value) Value))
    (run : evaluate (.raise name) state = (result, next)) : stackResult state result next := by
  cases read : getVar name state.locals with
  | none =>
    simp [evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some value =>
    cases jump : jumpExc state with
    | none =>
      simp [evaluate, read, jump] at run
      obtain ⟨rfl, rfl⟩ := run
      trivial
    | some jumped =>
      simp [evaluate, read, jump] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨jumped, jump, rfl, rfl⟩

/-- Returning values clears locals but keeps the control stack and handler. -/
theorem evaluate_return_stackResult {C F : Type} (names : List Nat) (state next : State C F)
    (result : Option (Result (List Value) Value))
    (run : evaluate (.return names) state = (result, next)) : stackResult state result next := by
  cases read : getVars names state.locals with
  | none =>
    simp [evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some values =>
    simp [evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨rfl, rfl⟩

end Flapjack.Compiler.Backend.DataSem

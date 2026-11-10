module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock
public import Flapjack.SemanticPrimitivesProps.ResultRelation
public import Mathlib.Data.List.Forall2

@[expose] public section

/-! Shared installation step of the proof-side Clos evaluator: the install
arguments are evaluated first, then the dynamically installed program runs on
the resulting state. This helper has no independent HOL declaration. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- All related installation payload lists yield related outcomes, for any
value and state relations and an install relation preserved by related
two-argument installations and type errors. Flapjack infrastructure shared by
the closure-simulation passes; no separate HOL declaration is claimed. -/
theorem install_related {C F : Type} {ValueRel : Value → Value → Prop}
    {StateRel : State C F → State C F → Prop}
    {InstallRel : (Result (List ClosLang.Exp) Value × State C F) →
      (Result (List ClosLang.Exp) Value × State C F) → Prop}
    (pair : ∀ (s t : State C F) (a b x y : Value),
      StateRel s t → ValueRel a x → ValueRel b y →
      InstallRel (doInstall [a, b] s) (doInstall [x, y] t))
    (typeError : ∀ (s t : State C F), StateRel s t →
      InstallRel (.err (.abort .typeError), s) (.err (.abort .typeError), t))
    (s t : State C F) (xs ys : List Value) (states : StateRel s t)
    (values : List.Forall₂ ValueRel xs ys) :
    InstallRel (doInstall xs s) (doInstall ys t) := by
  by_cases arity : xs.length = 2
  · cases values with
    | nil => simp at arity
    | @cons a x rest nextRest first tail =>
      cases tail with
      | nil => simp at arity
      | @cons b y rest nextRest second tail =>
        cases tail with
        | nil => exact pair s t a b x y states first second
        | cons third tail => simp at arity
  · have targetArity : ys.length ≠ 2 := by simpa [← values.length_eq] using arity
    have hx := doInstall_wrongArity xs s arity
    have hy := doInstall_wrongArity ys t targetArity
    rw [hx, hy]
    exact typeError s t states

/-- Installation preserves a state relation and produces related programs or
related exceptions, from the outcome relation's own clauses. Flapjack
infrastructure shared by the closure-simulation passes; no separate HOL
declaration is claimed. -/
theorem doInstallLemmaOf {C F : Type} {ValueRel : Value → Value → Prop}
    {StateRel : State C F → State C F → Prop}
    {CodeRel : List ClosLang.Exp → List ClosLang.Exp → Prop}
    {InstallRel : (Result (List ClosLang.Exp) Value × State C F) →
      (Result (List ClosLang.Exp) Value × State C F) → Prop}
    (rel : ∀ (r1 r2 : Result (List ClosLang.Exp) Value) (s t : State C F),
      InstallRel (r1, s) (r2, t) ↔
        match r1, r2 with
        | .err e, .err f => Flapjack.SemanticPrimitivesProps.excRel ValueRel e f ∧ StateRel s t
        | .val xs, .val ys => xs ≠ [] ∧ CodeRel xs ys ∧ StateRel s t
        | _, _ => False)
    (s t : State C F) (xs ys : List Value)
    (both : InstallRel (doInstall xs s) (doInstall ys t)) :
    match doInstall xs s with
    | (.err err1, s1) => ∃ err2 t1, doInstall ys t = (.err err2, t1) ∧
        Flapjack.SemanticPrimitivesProps.excRel ValueRel err1 err2 ∧ StateRel s1 t1
    | (.val exps1, s1) => ∃ exps2 t1, StateRel s1 t1 ∧ exps1 ≠ [] ∧ CodeRel exps1 exps2 ∧
        doInstall ys t = (.val exps2, t1) := by
  cases sourceRun : doInstall xs s with
  | mk sourceResult sourceNext =>
    cases targetRun : doInstall ys t with
    | mk targetResult targetNext =>
      rw [sourceRun, targetRun] at both
      rw [rel] at both
      cases sourceResult with
      | err error =>
        cases targetResult with
        | val values => exact both.elim
        | err targetError =>
          exact ⟨targetError, targetNext, rfl, both.1, both.2⟩
      | val program =>
        cases targetResult with
        | err error => exact both.elim
        | val targetProgram =>
          exact ⟨targetProgram, targetNext, both.2.2, both.1, both.2.1, rfl⟩

/-- Installation continuation factored out of the install equation: install
the evaluated values, run the installed program, and return its last value. -/
noncomputable def runInstalled {C F : Type} (values : List Value) (state : State C F) :
    EvalResult C F :=
  match doInstall values state with
  | (.err error, next) => (.err error, next)
  | (.val program, next) =>
    let (result, last) := evaluate program [] next
    match result with
    | .err error => (.err error, last)
    | .val values => (.val [@Flapjack.holLast Value ⟨unitValue⟩ values], last)

/-- Unfold the install operation at its argument evaluation boundary. -/
theorem evaluate_install_eq {C F : Type} (trace : BackendCommon.Tra) (args : List ClosLang.Exp)
    (env : List Value) (state : State C F) :
    evaluate [.op trace .install args] env state =
      match evaluate args env state with
      | (.err error, next) => (.err error, next)
      | (.val values, next) => runInstalled values.reverse next := by
  rw [evaluate, fixClock_evaluate]
  cases evaluated : evaluate args env state with
  | mk result next =>
    cases result with
    | err error => rfl
    | val values =>
      dsimp only
      unfold runInstalled
      split <;> simp_all
      split <;> simp_all
      rfl

end Flapjack.Compiler.Backend.ClosProps

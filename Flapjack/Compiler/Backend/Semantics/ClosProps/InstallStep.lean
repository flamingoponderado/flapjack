module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock
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

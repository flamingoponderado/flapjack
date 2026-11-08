import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock

/-! Shared installation step of the proof-side Clos evaluator: the install
arguments are evaluated first, then the dynamically installed program runs on
the resulting state. This helper has no independent HOL declaration. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosSem

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

import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock

/-! Sequencing properties of the proof-side closure evaluator. -/
namespace Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL

/-- An error in the first expression prevents evaluation of the tail. -/
theorem evaluate_cons_error {C F : Type} (first : ClosLang.Exp) (rest : List ClosLang.Exp)
    (env : List ClosSem.Value) (state next : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.evaluate [first] env state = (.err error, next)) :
    ClosSem.evaluate (first :: rest) env state = (.err error, next) := by
  cases rest with
  | nil => exact run
  | cons second rest =>
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, run]

/-- A singleton successful first result is prepended to the tail's values;
an error from the tail is propagated. -/
theorem evaluate_cons_value {C F : Type} (first : ClosLang.Exp) (rest : List ClosLang.Exp)
    (env : List ClosSem.Value) (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.evaluate [first] env state = (.val [value], next)) :
    ClosSem.evaluate (first :: rest) env state =
      match ClosSem.evaluate rest env next with
      | (.err error, last) => (.err error, last)
      | (.val values, last) => (.val (value :: values), last) := by
  cases rest with
  | nil => simpa [ClosSem.evaluate] using run
  | cons second rest =>
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, run]
    cases tailRun : ClosSem.evaluate (second :: rest) env next with
    | mk result last => cases result <;> rfl

end Flapjack.Compiler.Backend.ClosProps

module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock

@[expose] public section

/-! Original closure evaluator clock statements over the reviewed state. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

namespace EvaluateClockPort
/-- The closure state uses the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end EvaluateClockPort

/-- Both closure evaluation and application preserve the original clock bound. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "evaluate_clock"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_clock_source :
    (∀ {C F : Type} (xs : List ClosLang.Exp) (env : List Value) (s : State C F)
      (result : Result (List Value) Value) (next : State C F),
      evaluate xs env s = (result, next) → next.clock ≤ s.clock) ∧
    (∀ {C F : Type} (location : Option Nat) (function : Value) (args : List Value) (s : State C F)
      (result : Result (List Value) Value) (next : State C F),
      evaluateApp location function args s = (result, next) → next.clock ≤ s.clock) := by
  constructor
  · intro C F xs env s result next run
    have bound := evaluate_clock_le xs env s
    simpa [run] using bound
  · intro C F location function args s result next run
    have bound := evaluateApp_clock_le location function args s
    simpa [run] using bound

/-- Clamping a closure evaluation to its input clock has no effect. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "fix_clock_evaluate"
  (fmap_as_finite_support := [refs, code])]
theorem fixClock_evaluate_source {C F : Type} (xs : List ClosLang.Exp)
    (env : List Value) (state : State C F) :
    fixClock state (evaluate xs env state) = evaluate xs env state :=
  fixClock_evaluate xs env state

end Flapjack.Compiler.Backend.ClosSem

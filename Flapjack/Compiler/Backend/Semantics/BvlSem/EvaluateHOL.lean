import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateLength
import Flapjack.HolRef

/-! Source-typed BVL evaluation and its clock invariants. -/
namespace Flapjack.Compiler.Backend.BvlSem
open Flapjack.SemanticPrimitivesHOL

namespace EvaluateCarrier
/-- Canonical reference-map state representation roundtrip for evaluation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end EvaluateCarrier

/-- Clocked BVL evaluation on the source's expression/environment/state
triple. The curried implementation uses the source's termination-only clock
clamps, and `fixClock_evaluate` proves those clamps inert. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "evaluate_def" 596
  (fmap_as_finite_support := [refs])]
noncomputable def evaluateTuple {C F : Type}
    (input : List Bvl.Exp × List Value × Flapjack.Compiler.Backend.BvlSem.State C F) :
    Result (List Value) Value × Flapjack.Compiler.Backend.BvlSem.State C F :=
  evaluate input.1 input.2.1 input.2.2

/-- Evaluation never increases the clock. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "evaluate_clock"
  (fmap_as_finite_support := [refs])]
theorem evaluateClock {C F : Type} (expressions : List Bvl.Exp) (env : List Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F) (result : Result (List Value) Value)
    (next : Flapjack.Compiler.Backend.BvlSem.State C F)
    (run : evaluateTuple (expressions, env, state) = (result, next)) :
    next.clock ≤ state.clock := by
  have bound := evaluate_clock_le expressions env state
  change evaluate expressions env state = (result, next) at run
  simpa [run] using bound

/-- The original termination-only clock clamp leaves evaluation unchanged. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "fix_clock_evaluate"
  (fmap_as_finite_support := [refs])]
theorem fixClockEvaluate {C F : Type} (expressions : List Bvl.Exp) (env : List Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F) :
    fixClock state (evaluateTuple (expressions, env, state)) =
      evaluateTuple (expressions, env, state) := by
  exact fixClock_evaluate expressions env state

end Flapjack.Compiler.Backend.BvlSem

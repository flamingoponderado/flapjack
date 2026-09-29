import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-!
# Production/exact Loop Continue case

This case compares the exact HOL-shaped `LoopSemStateFiniteExact.evaluate`
Continue equation (`cakeml/pancake/semantics/loopSemScript.sml:349`) with the
production `evaluateLoop` Continue branch (`Flapjack/Pancake/Semantics/LoopSem.lean`,
`evaluateLoop`). Both return the same Continue label and preserve their input
state verbatim, so an existing pre-state `prodRel` is preserved. This is
Flapjack-specific cross-carrier bridge infrastructure, not a standalone HOL
theorem, so this declaration intentionally has no `@[hol]` tag.
-/

namespace Flapjack
namespace LoopSemStateFiniteExact.EvaluateCases

/-- Relate the single Continue case of the exact Loop evaluator to production.
The arbitrary hook record is unused by Continue; positive production fuel
reaches the Continue clause, and both carriers preserve their input state
verbatim. The Continue payload includes the unchanged label. No other evaluator
constructor or hook is covered by this lemma. -/
theorem evaluateContinue_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hooks : LoopEvaluateHooks (BitVec width) F) (label : Nat)
    (hrel : state.prodRel machine) :
    let exactStep := LoopSemStateFiniteExact.evaluate (.continue label) state
    let productionStep :=
      Flapjack.evaluateLoop (machine.clock + 1) hooks (.continue label) machine
    exactStep = (some (.continue label), state) ∧
      productionStep = (some (.continue label), machine) ∧
      exactStep.2.prodRel productionStep.2 := by
  constructor
  · simp [LoopSemStateFiniteExact.evaluate]
  constructor
  · simp [Flapjack.evaluateLoop]
  · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop] using hrel

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack

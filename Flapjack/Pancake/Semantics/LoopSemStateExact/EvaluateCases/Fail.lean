import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-!
# Production/exact Loop Fail case

This case compares the exact HOL-shaped `LoopSemStateFiniteExact.evaluate`
Fail equation (`cakeml/pancake/semantics/loopSemScript.sml:280`) with the
production `evaluateLoop` Fail branch (`Flapjack/Pancake/Semantics/LoopSem.lean`,
`evaluateLoop`). Both return Error and preserve their input state, so an
existing pre-state `prodRel` is preserved. This is Flapjack-specific
cross-carrier bridge infrastructure, not a standalone HOL theorem, so this
declaration intentionally has no `@[hol]` tag.
-/

namespace Flapjack
namespace LoopSemStateFiniteExact.EvaluateCases

/-- Relate the single Fail case of the exact Loop evaluator to production.
The arbitrary hook record is unused by Fail; positive fuel reaches the
production Fail clause, and both carriers preserve their input state verbatim.
No other evaluator constructor or hook is covered by this lemma. -/
theorem evaluateFail_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hooks : LoopEvaluateHooks (BitVec width) F)
    (hrel : state.prodRel machine) :
    let exactStep := LoopSemStateFiniteExact.evaluate (.fail) state
    let productionStep :=
      Flapjack.evaluateLoop (machine.clock + 1) hooks (.fail) machine
    exactStep = (some .error, state) ∧ productionStep = (some .error, machine) ∧
      exactStep.2.prodRel productionStep.2 := by
  constructor
  · simp [LoopSemStateFiniteExact.evaluate]
  constructor
  · simp [Flapjack.evaluateLoop]
  · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop] using hrel

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack

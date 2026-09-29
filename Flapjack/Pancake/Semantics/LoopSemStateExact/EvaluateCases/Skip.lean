import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-!
# Production/exact Loop Skip case

This case compares the exact HOL-shaped `LoopSemStateFiniteExact.evaluate`
Skip equation (`cakeml/pancake/semantics/loopSemScript.sml:279`) with the
production `evaluateLoop` Skip branch (`Flapjack/Pancake/Semantics/LoopSem.lean`,
`evaluateLoop`). Both return no result and preserve their input state, so an
existing pre-state `prodRel` is preserved. This is Flapjack-specific
cross-carrier bridge infrastructure, not a standalone HOL theorem, so this
declaration intentionally has no `@[hol]` tag.
-/

namespace Flapjack
namespace LoopSemStateFiniteExact.EvaluateCases

/-- Relate the single Skip case of the exact Loop evaluator to production.
The arbitrary hook record is unused by Skip; positive fuel is supplied to the
production evaluator, and both carriers preserve the pre-state verbatim. No
other evaluator constructor or hook is covered by this lemma. -/
theorem evaluateSkip_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hooks : LoopEvaluateHooks (BitVec width) F)
    (hrel : state.prodRel machine) :
    let exactStep := LoopSemStateFiniteExact.evaluate (.skip) state
    let productionStep :=
      Flapjack.evaluateLoop (machine.clock + 1) hooks (.skip) machine
    exactStep = (none, state) ∧ productionStep = (none, machine) ∧
      exactStep.2.prodRel productionStep.2 := by
  constructor
  · simp [LoopSemStateFiniteExact.evaluate]
  constructor
  · simp [Flapjack.evaluateLoop]
  · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop] using hrel

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack

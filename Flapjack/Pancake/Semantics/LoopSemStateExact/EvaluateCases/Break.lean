import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-!
# Production/exact Loop Break case

This case compares the exact HOL-shaped `LoopSemStateFiniteExact.evaluate`
Break equation (`cakeml/pancake/semantics/loopSemScript.sml:348`) with the
production `evaluateLoop` Break branch (`Flapjack/Pancake/Semantics/LoopSem.lean`,
`evaluateLoop`). Both return the given Break label and preserve their input
state, so an existing pre-state `prodRel` is preserved. This is Flapjack-
specific cross-carrier bridge infrastructure, not a standalone HOL theorem,
so this declaration intentionally has no `@[hol]` tag.
-/

namespace Flapjack
namespace LoopSemStateFiniteExact.EvaluateCases

/-- Relate the single Break case of the exact Loop evaluator to production.
The arbitrary hook record is unused by Break; positive fuel reaches the
production Break clause, and both carriers preserve their input state verbatim.
No other evaluator constructor or hook is covered by this lemma. -/
theorem evaluateBreak_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hooks : LoopEvaluateHooks (BitVec width) F) (label : Nat)
    (hrel : state.prodRel machine) :
    let exactStep := LoopSemStateFiniteExact.evaluate (.break label) state
    let productionStep :=
      Flapjack.evaluateLoop (machine.clock + 1) hooks (.break label) machine
    exactStep = (some (.break label), state) ∧
      productionStep = (some (.break label), machine) ∧
      exactStep.2.prodRel productionStep.2 := by
  constructor
  · simp [LoopSemStateFiniteExact.evaluate]
  constructor
  · simp [Flapjack.evaluateLoop]
  · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop] using hrel

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack

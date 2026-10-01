import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.Seq

/-!
# Exact and production Loop Mark composition

HOL `loopSemScript.sml:347` erases Mark before evaluating its body. The
production evaluator also evaluates the body, consuming one unit of its
explicit fuel. This Flapjack-specific relation composes a recursive body
hypothesis at that child fuel; it is not an unconditional HOL evaluator port
and therefore has no HOL tag.
-/

namespace Flapjack.LoopSemStateFiniteExact.EvaluateCases

/-- Mark preserves the complete related body result and post-state. The only
recursive premise concerns the body at child fuel, not the Mark evaluation. -/
theorem evaluateMark_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hooks : LoopEvaluateHooks (BitVec width) F) (fuel : Nat)
    (body : HolLoopProg width) (runtimeBody : LoopProg (BitVec width))
    (hrel : state.prodRel machine)
    (hBody : ∀ {state' : LoopSemStateFiniteExact width F}
      {machine' : LoopMachineState (BitVec width) F},
      state'.prodRel machine' → loopEvaluationStepRel
        (LoopSemStateFiniteExact.evaluate body state')
        (Flapjack.evaluateLoop fuel hooks runtimeBody machine')) :
    loopEvaluationStepRel
      (LoopSemStateFiniteExact.evaluate (.mark body) state)
      (Flapjack.evaluateLoop (fuel + 1) hooks (.mark runtimeBody) machine) := by
  simpa only [LoopSemStateFiniteExact.evaluate.eq_14, Flapjack.evaluateLoop]
    using hBody hrel

end Flapjack.LoopSemStateFiniteExact.EvaluateCases

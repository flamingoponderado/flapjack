import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-!
# Production/exact Loop Assign case

This case compares the exact HOL-shaped `LoopSemStateFiniteExact.evaluate`
Assign equation (`cakeml/pancake/semantics/loopSemScript.sml:281-284`) with the
production `evaluateLoop` Assign branch (`Flapjack/Pancake/Semantics/LoopSem.lean`,
`evaluateLoop`). HOL evaluates with its exact `eval`, whereas production calls
an arbitrary `hooks.eval`; therefore the cross-carrier bridge requires their
results to agree for this expression. Without that condition an unconditional
claim is false. This is Flapjack-specific bridge infrastructure, not a
standalone HOL theorem, so these declarations intentionally have no `@[hol]`
tag. The general production hook-refinement proof remains open work.
-/

namespace Flapjack
namespace LoopSemStateFiniteExact.EvaluateCases

/-- Assign has only its successful/None and Error result shapes. -/
def assignResultRel {width : Nat} [NeZero width]
    (exact : Option (LoopResultExact width))
    (production : Option (LoopMachineResult (BitVec width))) : Prop :=
  match exact, production with
  | none, none => True
  | some .error, some .error => True
  | _, _ => False

/-- Relate one Assign step when the production expression hook agrees with
exact `eval` for the corresponding expression pair. The exact and production
expression carriers are explicitly distinct. Eval failure preserves both
states; success uses the existing `setVar_prodRel` bridge. This does not
establish expression translation or hook agreement for the executed compiler. -/
theorem evaluateAssign_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hooks : LoopEvaluateHooks (BitVec width) F)
    (hrel : state.prodRel machine) (destination : Nat)
    (sourceExpression : HolLoopExp width)
    (runtimeExpression : LoopExp (BitVec width))
    (hEval : hooks.eval machine runtimeExpression =
      (LoopSemStateFiniteExact.eval state sourceExpression).map loopValueOfWordLocW) :
    let exactStep :=
      LoopSemStateFiniteExact.evaluate (.assign destination sourceExpression) state
    let productionStep := Flapjack.evaluateLoop (machine.clock + 1) hooks
      (.assign destination runtimeExpression) machine
    assignResultRel exactStep.1 productionStep.1 ∧
      exactStep.2.prodRel productionStep.2 := by
  cases heval : LoopSemStateFiniteExact.eval state sourceExpression with
  | none =>
      have hprod : hooks.eval machine runtimeExpression = none := by
        rw [hEval, heval]
        rfl
      constructor
      · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          assignResultRel, heval, hprod]
      · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          heval, hprod] using hrel
  | some value =>
      have hprod : hooks.eval machine runtimeExpression =
          some (loopValueOfWordLocW value) := by
        rw [hEval, heval]
        rfl
      have hpost :=
        LoopSemStateFiniteExact.setVar_prodRel hrel destination value
      constructor
      · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          assignResultRel, heval, hprod]
      · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          heval, hprod] using hpost

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack

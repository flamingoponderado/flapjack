import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.Seq

/-!
# Exact signed Loop Div production adapter

HOL `loop_arith_def` at `loopSemScript.sml:118-124` divides fixed-width signed
words, fails on zero, and updates only the destination. This adapter uses that
same `BitVec.sdiv` operation. The broad Nat arithmetic helper has unsigned
semantics and cannot supply this relation. These are Flapjack-specific
cross-carrier proofs, not HOL ports; no HOL tag or executed caller is claimed.
-/
namespace Flapjack
namespace LoopSemStateFiniteExact.EvaluateCases

/-- Signed fixed-width Div hook, preserving all other production state fields. -/
def loopMachineDivExact {width : Nat} [NeZero width] {F : Type}
    (machine : LoopMachineState (BitVec width) F)
    (destination dividend divisor : Nat) : Option (LoopMachineState (BitVec width) F) :=
  match machine.locals divisor, machine.locals dividend with
  | some (.word q), some (.word value) =>
      if q ≠ 0 then
        some { machine with locals := loopSetVar machine.locals destination (.word (value.sdiv q)) }
      else none
  | _, _ => none

/-- The concrete Div hook derives its successful post-state relation internally
from related input locals; all invalid operands and zero divisors fail together. -/
theorem loopMachineDivExact_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine) (destination dividend divisor : Nat) :
    match LoopSemStateFiniteExact.loopArith state (.div destination dividend divisor),
        loopMachineDivExact machine destination dividend divisor with
    | none, none => True
    | some nextState, some nextMachine => nextState.prodRel nextMachine
    | _, _ => False := by
  have hd := hrel.1 divisor
  have hv := hrel.1 dividend
  cases hq : sptLookup divisor state.locals with
  | none => simp [LoopSemStateFiniteExact.loopArith, loopMachineDivExact, hd, hq]
  | some q =>
      cases q with
      | loc label offset =>
          simp [LoopSemStateFiniteExact.loopArith, loopMachineDivExact, hd, hq,
            loopValueOfWordLocW]
      | word q =>
          cases hw : sptLookup dividend state.locals with
          | none =>
              simp [LoopSemStateFiniteExact.loopArith, loopMachineDivExact, hd, hv, hq, hw,
                loopValueOfWordLocW]
          | some value =>
              cases value with
              | loc label offset =>
                  simp [LoopSemStateFiniteExact.loopArith, loopMachineDivExact, hd, hv, hq, hw,
                    loopValueOfWordLocW]
              | word value =>
                  by_cases hz : q = BitVec.ofNat width 0
                  · simp [LoopSemStateFiniteExact.loopArith, loopMachineDivExact, hd, hv,
                      hq, hw, loopValueOfWordLocW, hz]
                  · simpa [LoopSemStateFiniteExact.loopArith, loopMachineDivExact, hd, hv,
                      hq, hw, loopValueOfWordLocW, hz] using
                      LoopSemStateFiniteExact.setVar_prodRel hrel destination (.word (value.sdiv q))

/-- Full Div evaluator case from concrete hook selection, including every
failure. No target evaluation or successful post-state is supplied as a premise. -/
theorem evaluateDiv_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hooks : LoopEvaluateHooks (BitVec width) F)
    (hrel : state.prodRel machine) (destination dividend divisor : Nat)
    (hHook : hooks.arith machine (.div destination dividend divisor) =
      loopMachineDivExact machine destination dividend divisor) :
    loopEvaluationStepRel
      (LoopSemStateFiniteExact.evaluate (.arith (.div destination dividend divisor)) state)
      (Flapjack.evaluateLoop (machine.clock + 1) hooks
        (.arith (.div destination dividend divisor)) machine) := by
  have hstep := loopMachineDivExact_prodRel hrel destination dividend divisor
  cases he : LoopSemStateFiniteExact.loopArith state (.div destination dividend divisor) <;>
    cases hp : loopMachineDivExact machine destination dividend divisor <;>
    simp [he, hp] at hstep
  · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop, hHook, he, hp,
      loopEvaluationStepRel, loopResultOptionRel] using (And.intro trivial hrel)
  · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop, hHook, he, hp,
      loopEvaluationStepRel, loopResultOptionRel] using (And.intro trivial hstep)

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack

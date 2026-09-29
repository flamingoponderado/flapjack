import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-!
# Production/exact Loop Tick case

This case compares the exact HOL-shaped `LoopSemStateFiniteExact.evaluate`
Tick equation (`cakeml/pancake/semantics/loopSemScript.sml:379-381`) and
`dec_clock_def` (`loopSemScript.sml:42-43`) with the production
`evaluateLoop` Tick branch (`Flapjack/Pancake/Semantics/LoopSem.lean`) and
`decrementLoopClock` (`Flapjack/LoopStateResult.lean`). Both sides time out
and clear locals at clock zero; at a nonzero clock both decrement once and
preserve the remaining state. These are Flapjack-specific cross-carrier
bridge lemmas, not standalone HOL theorems, so they intentionally have no
`@[hol]` tags.
-/

namespace Flapjack
namespace LoopSemStateFiniteExact.EvaluateCases

/-- Clearing exact and production locals preserves every other component of
`prodRel`; the cleared local lookups are both absent. -/
theorem tickTimeout_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine) :
    ({ state with locals := .ln }).prodRel
      ({ machine with locals := fun _ => none }) := by
  rcases hrel with
    ⟨hlocals, hglobals, hmemory, hmdomain, hshMdomain, hclock, hbe, hffi,
      hbaseAddr, htopAddr, hcode, hcoverage⟩
  refine ⟨?_, hglobals, hmemory, hmdomain, hshMdomain, hclock, hbe, hffi,
    hbaseAddr, htopAddr, hcode, hcoverage⟩
  intro name
  simp

/-- Decrementing related exact and production clocks preserves `prodRel`;
all other state components are unchanged. -/
theorem tickDecrement_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine) :
    (LoopSemStateFiniteExact.decClock state).prodRel
      (Flapjack.decrementLoopClock machine) := by
  rcases hrel with
    ⟨hlocals, hglobals, hmemory, hmdomain, hshMdomain, hclock, hbe, hffi,
      hbaseAddr, htopAddr, hcode, hcoverage⟩
  refine ⟨hlocals, hglobals, hmemory, hmdomain, hshMdomain, ?_, hbe, hffi,
    hbaseAddr, htopAddr, hcode, hcoverage⟩
  simp [LoopSemStateFiniteExact.decClock, Flapjack.decrementLoopClock, hclock]

/-- Relate the single Tick case of exact HOL evaluation to production from the
pre-state relation alone. At zero clock both evaluators return `TimeOut` and
clear locals; otherwise both return normally and decrement their related
clocks. No other evaluator constructor or hook is covered. -/
theorem evaluateTick_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hooks : LoopEvaluateHooks (BitVec width) F)
    (hrel : state.prodRel machine) :
    let exactStep := LoopSemStateFiniteExact.evaluate (.tick) state
    let productionStep :=
      Flapjack.evaluateLoop (machine.clock + 1) hooks (.tick) machine
    (exactStep.1 = some .timeOut ∧ productionStep.1 = some .timeOut ∧
        exactStep.2.prodRel productionStep.2) ∨
      (exactStep.1 = none ∧ productionStep.1 = none ∧
        exactStep.2.prodRel productionStep.2) := by
  dsimp only
  have hclock : machine.clock = state.clock := hrel.2.2.2.2.2.1
  by_cases hz : state.clock = 0
  · left
    have hpost := tickTimeout_prodRel hrel
    refine ⟨?_, ?_, ?_⟩
    · simp [LoopSemStateFiniteExact.evaluate, hz]
    · simp [Flapjack.evaluateLoop, hclock, hz]
    · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop, hclock, hz]
        using hpost
  · right
    have hpost := tickDecrement_prodRel hrel
    refine ⟨?_, ?_, ?_⟩
    · simp [LoopSemStateFiniteExact.evaluate, hz]
    · simp [Flapjack.evaluateLoop, hclock, hz]
    · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop, hclock, hz,
        LoopSemStateFiniteExact.decClock, Flapjack.decrementLoopClock]
        using hpost

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack

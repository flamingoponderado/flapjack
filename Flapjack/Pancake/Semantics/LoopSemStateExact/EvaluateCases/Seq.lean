import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-!
# Production/exact Loop Seq case

HOL `loopSem$evaluate_def` (`loopSemScript.sml:338`) evaluates its first
command, applies `fix_clock` to that result and state, and evaluates the second
command only when the fixed first result is `NONE`. The production
`evaluateLoop` Seq branch (`LoopSem.lean:187-189`) has the same composition
with `fixLoopMachineClock`, but its recursive calls are fuel-bounded and use
the executable program carrier. This module proves that composition from
explicit recursive case relations; it does not assume the Seq result itself
and does not claim the arbitrary hooks or finite fuel implement the HOL
evaluator unconditionally. This is Flapjack-specific bridge infrastructure,
not a standalone HOL theorem, so it has no `@[hol]` tag.
-/

namespace Flapjack
namespace LoopSemStateFiniteExact.EvaluateCases

/-- Result correspondence used when a recursive exact and production Loop
evaluation step is composed by Seq. Word/location payloads use the reviewed
carrier conversion; FFI final events use `FfiFinalEventRel`. -/
def loopResultOptionRel {width : Nat} [NeZero width] :
    Option (LoopResultExact width) → Option (LoopMachineResult (BitVec width)) → Prop
  | none, none => True
  | some (.result exact), some (.result production) =>
      production = exact.map loopValueOfWordLocW
  | some (.exception exact), some (.except production) =>
      production = loopValueOfWordLocW exact
  | some (.break exact), some (.break production) => production = exact
  | some (.continue exact), some (.continue production) => production = exact
  | some .timeOut, some .timeOut => True
  | some (.finalFfi exact), some (.finalFfi production) =>
      FfiFinalEventRel production exact
  | some .error, some .error => True
  | _, _ => False

/-- A one-step exact/production relation. Keeping this pair local to the Loop
evaluator makes clear that Seq composes result correspondence and `prodRel`
state correspondence together. -/
def loopEvaluationStepRel {width : Nat} [NeZero width] {F : Type}
    (exact : Option (LoopResultExact width) × LoopSemStateFiniteExact width F)
    (production : Option (LoopMachineResult (BitVec width)) × LoopMachineState (BitVec width) F) :
    Prop := loopResultOptionRel exact.1 production.1 ∧ exact.2.prodRel production.2

/-- Updating the exact and production clock to the same value preserves every
other conjunct of `prodRel`. -/
theorem clockUpdate_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine) (clock : Nat) :
    ({ state with clock := clock }).prodRel ({ machine with clock := clock }) := by
  rcases hrel with
    ⟨hlocals, hglobals, hmemory, hmdomain, hshMdomain, _hclock, hbe, hffi,
      hbaseAddr, htopAddr, hcode, hcoverage⟩
  exact ⟨hlocals, hglobals, hmemory, hmdomain, hshMdomain, rfl, hbe, hffi,
    hbaseAddr, htopAddr, hcode, hcoverage⟩

/-- The exact HOL `fix_clock` and production `fixLoopMachineClock` preserve a
related result and state. Their minimum-clock clauses agree because the old
and returned clocks are related. This lemma is the explicit Seq clock-restoration
bridge; it does not erase the clock update or assume the post-state relation. -/
theorem fixClock_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    {exactStep : Option (LoopResultExact width) × LoopSemStateFiniteExact width F}
    {productionStep : Option (LoopMachineResult (BitVec width)) × LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine)
    (hstep : loopEvaluationStepRel exactStep productionStep) :
    loopEvaluationStepRel
      (LoopSemStateFiniteExact.fixClock state exactStep)
      (fixLoopMachineClock machine productionStep) := by
  rcases hstep with ⟨hresult, hpost⟩
  have hOldClock : machine.clock = state.clock := hrel.2.2.2.2.2.1
  have hStepClock : productionStep.2.clock = exactStep.2.clock := hpost.2.2.2.2.2.1
  let nextClock := if state.clock < exactStep.2.clock then state.clock else exactStep.2.clock
  have hclockPost := clockUpdate_prodRel hpost nextClock
  constructor
  · simpa [loopEvaluationStepRel, LoopSemStateFiniteExact.fixClock,
      fixLoopMachineClock] using hresult
  · simpa [LoopSemStateFiniteExact.fixClock, fixLoopMachineClock,
      hOldClock, hStepClock, nextClock] using hclockPost

/-- Source-shaped compositional Seq bridge. The premises are precisely the
recursive case relations for the two child programs at the child fuel. The
first relation is evaluated from the original related states; after HOL
`fix_clock`/production `fixLoopMachineClock`, the second relation is needed
only if the first result is `NONE`. Every non-`NONE` result is propagated
without running the second program. No whole-Seq evaluation equivalence is
assumed. -/
theorem evaluateSeq_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hooks : LoopEvaluateHooks (BitVec width) F)
    (fuel : Nat) (first second : HolLoopProg width)
    (runtimeFirst runtimeSecond : LoopProg (BitVec width))
    (hrel : state.prodRel machine)
    (hFirst : ∀ {state' : LoopSemStateFiniteExact width F}
      {machine' : LoopMachineState (BitVec width) F},
      state'.prodRel machine' →
        loopEvaluationStepRel
          (LoopSemStateFiniteExact.evaluate first state')
          (Flapjack.evaluateLoop fuel hooks runtimeFirst machine'))
    (hSecond : ∀ {state' : LoopSemStateFiniteExact width F}
      {machine' : LoopMachineState (BitVec width) F},
      state'.prodRel machine' →
        loopEvaluationStepRel
          (LoopSemStateFiniteExact.evaluate second state')
          (Flapjack.evaluateLoop fuel hooks runtimeSecond machine')) :
    loopEvaluationStepRel
      (LoopSemStateFiniteExact.evaluate (.seq first second) state)
      (Flapjack.evaluateLoop (fuel + 1) hooks (.seq runtimeFirst runtimeSecond) machine) := by
  rw [LoopSemStateFiniteExact.evaluate.eq_12]
  have hfixed := fixClock_prodRel hrel (hFirst hrel)
  cases hexact : LoopSemStateFiniteExact.evaluate first state with
  | mk exactResult exactState =>
      cases hproduction : Flapjack.evaluateLoop fuel hooks runtimeFirst machine with
      | mk productionResult productionState =>
          have hfixed' : loopEvaluationStepRel
              (LoopSemStateFiniteExact.fixClock state (exactResult, exactState))
              (fixLoopMachineClock machine (productionResult, productionState)) := by
            simpa [hexact, hproduction] using hfixed
          have hfixed'' := hfixed'
          simp only [LoopSemStateFiniteExact.fixClock, fixLoopMachineClock,
            loopEvaluationStepRel] at hfixed''
          have hfixedResult := hfixed''.1
          have hfixedState := hfixed''.2
          cases exactResult with
          | none =>
              have hproductionNone : productionResult = none := by
                cases productionResult with
                | none => rfl
                | some result => simp [loopResultOptionRel] at hfixedResult
              subst productionResult
              have hsecond := hSecond hfixedState
              simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
                hexact, hproduction, LoopSemStateFiniteExact.fixClock,
                fixLoopMachineClock] using hsecond
          | some result =>
              cases productionResult with
              | none => simp [loopResultOptionRel] at hfixedResult
              | some productionResult =>
                  simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
                    hexact, hproduction, LoopSemStateFiniteExact.fixClock,
                    fixLoopMachineClock, loopEvaluationStepRel] using
                      (And.intro hfixedResult hfixedState)

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack

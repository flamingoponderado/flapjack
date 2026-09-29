import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-!
# Production/exact Loop Raise case

This case relates the HOL-shaped `LoopSemStateFiniteExact.evaluate` Raise
equation to the production `evaluateLoop` Raise branch under `prodRel`. It
uses the same empty-local `call_env []` state effect on both carriers. The
theorem is Flapjack-specific bridge infrastructure, not a separate HOL theorem
or a whole-evaluator simulation.
-/

namespace Flapjack
namespace LoopSemStateFiniteExact.EvaluateCases

/-- The exact exception/error outcomes of `evaluate Raise` and the production
`evaluateLoop Raise` outcome have the same observable result payload. This is a
small Flapjack bridge relation: the exact HOL `exception` carries `WordLocW`,
while the executable result carries its `LoopValue` mirror. -/
def raiseResultRel {width : Nat} [NeZero width]
    (exact : Option (LoopResultExact width))
    (production : Option (LoopMachineResult (BitVec width))) : Prop :=
  match exact, production with
  | some .error, some .error => True
  | some (.exception value), some (.except output) =>
      output = loopValueOfWordLocW value
  | _, _ => False

/-- Exact HOL `call_env []` and the production `callEnv []` both clear locals;
all other fields in `prodRel` are preserved. The source HOL operation is
`loopSemScript.sml:177-180`, and this is the state effect used by the Raise
case below. -/
theorem callEnvEmpty_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine) :
    (LoopSemStateFiniteExact.callEnv [] state).prodRel (Flapjack.callEnv [] machine) := by
  rcases hrel with
    ⟨hlocals, hglobals, hmemory, hmdomain, hshMdomain, hclock, hbe, hffi,
      hbaseAddr, htopAddr, hcode, hcoverage⟩
  refine ⟨?_, hglobals, hmemory, hmdomain, hshMdomain, hclock, hbe, hffi,
    hbaseAddr, htopAddr, hcode, hcoverage⟩
  intro name
  simp [LoopSemStateFiniteExact.callEnv, Flapjack.callEnv,
    Flapjack.machineLocalsFromList, LoopSemStateFiniteExact.sptFromList]

/-- Relate the single `Raise` control/effect case of exact HOL evaluation to
the production Loop evaluator. Positive fuel (`machine.clock + 1`) reaches
the production Raise clause. If the local is absent both sides return Error
and preserve the input state; if present both return the related exception
payload and clear locals with `call_env []`/`callEnv []`. No other evaluator
constructor or hook is assumed correct by this lemma. -/
theorem evaluateRaise_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hooks : LoopEvaluateHooks (BitVec width) F)
    (hrel : state.prodRel machine) (name : Nat) :
    let exactStep := LoopSemStateFiniteExact.evaluate (.raise name) state
    let productionStep :=
      Flapjack.evaluateLoop (machine.clock + 1) hooks (.raise name) machine
    raiseResultRel exactStep.1 productionStep.1 ∧ exactStep.2.prodRel productionStep.2 := by
  cases hlookup : sptLookup name state.locals with
  | none =>
      have hproductionLookup : machine.locals name = none := by
        rw [hrel.1 name, hlookup]
        rfl
      constructor
      · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          raiseResultRel, hlookup, hproductionLookup]
      · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          hlookup, hproductionLookup] using hrel
  | some value =>
      have hproductionLookup :
          machine.locals name = some (loopValueOfWordLocW value) := by
        rw [hrel.1 name, hlookup]
        rfl
      have hpost := callEnvEmpty_prodRel hrel
      constructor
      · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          raiseResultRel, hlookup, hproductionLookup]
      · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          hlookup, hproductionLookup] using hpost

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack

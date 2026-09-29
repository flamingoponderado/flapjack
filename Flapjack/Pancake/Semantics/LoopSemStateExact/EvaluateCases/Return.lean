import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.Raise

/-!
# Production/exact Loop Return case

This compares the HOL-shaped `LoopSemStateFiniteExact.evaluate` Return clause
(`cakeml/pancake/semantics/loopSemScript.sml:363`) with the production
`evaluateLoop` Return branch. The result relation records the exact list of
returned word/location values, while the post-state uses the `call_env []` /
`callEnv []` empty-local update. This is Flapjack-specific bridge
infrastructure, not a standalone HOL theorem or whole-evaluator simulation.
-/

namespace Flapjack
namespace LoopSemStateFiniteExact.EvaluateCases

/-- A Return result has the same ordered value list after converting exact
HOL `word_loc` values to the production `LoopValue` carrier; Error matches
Error when a requested local is missing. -/
def returnResultRel {width : Nat} [NeZero width]
    (exact : Option (LoopResultExact width))
    (production : Option (LoopMachineResult (BitVec width))) : Prop :=
  match exact, production with
  | some (.result values), some (.result output) =>
      output = values.map loopValueOfWordLocW
  | some .error, some .error => True
  | _, _ => False

/-- Relate the exact and production Loop Return case under only the pre-state
`prodRel`. For a successful lookup, the same ordered locals are returned and
both evaluators replace locals with the empty `call_env []`; when any name is
missing, both return Error and preserve the pre-state. `hooks` is arbitrary and
unused by Return. The theorem covers this constructor only. -/
theorem evaluateReturn_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hooks : LoopEvaluateHooks (BitVec width) F)
    (hrel : state.prodRel machine) (names : List Nat) :
    let exactStep := LoopSemStateFiniteExact.evaluate (.return names) state
    let productionStep :=
      Flapjack.evaluateLoop (machine.clock + 1) hooks (.return names) machine
    returnResultRel exactStep.1 productionStep.1 ∧
      exactStep.2.prodRel productionStep.2 := by
  have hget : Flapjack.getVars names machine =
      Flapjack.loopMachineGetVars machine.locals names := by
    induction names with
    | nil => rfl
    | cons name names ih =>
        cases hlocal : machine.locals name with
        | none => simp [Flapjack.getVars, Flapjack.loopMachineGetVars, hlocal]
        | some value =>
            cases htail : Flapjack.loopMachineGetVars machine.locals names <;>
              simp [Flapjack.getVars, Flapjack.loopMachineGetVars, hlocal, htail, ih]
  cases hvalues : LoopSemStateFiniteExact.getVars names state with
  | none =>
      have hproductionValues : Flapjack.loopMachineGetVars machine.locals names = none := by
        have hmap := LoopSemStateFiniteExact.getVars_map_eq_of_prodRel hrel names
        rw [hvalues] at hmap
        rw [← hget]
        exact hmap.symm
      constructor
      · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          returnResultRel, hvalues, hproductionValues]
      · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          hvalues, hproductionValues] using hrel
  | some values =>
      have hproductionValues :
          Flapjack.loopMachineGetVars machine.locals names =
            some (values.map loopValueOfWordLocW) := by
        have hmap := LoopSemStateFiniteExact.getVars_map_eq_of_prodRel hrel names
        rw [hvalues] at hmap
        rw [← hget]
        exact hmap.symm
      have hpost := callEnvEmpty_prodRel hrel
      constructor
      · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          returnResultRel, hvalues, hproductionValues]
      · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          hvalues, hproductionValues] using hpost

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack

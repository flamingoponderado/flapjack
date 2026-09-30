import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace Flapjack

open Pancake.PanLang PanSemStateFiniteExact

/-- Flapjack-specific observation lemma for the top-level call used by
`semantics_empty_locals`. There is no separate HOL declaration for this
evaluator observation: HOL proves the enclosing semantics equation directly.
Caller locals are discarded on callee entry; failures retain the same FFI.
No successful lookup or recursive evaluation hypothesis is assumed. -/
theorem panGlobals_call_emptyLocals_observation {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ) (start : MlS) :
    let first := evaluateHOLFiniteState state (.call none start [])
    let second := evaluateHOLFiniteState (emptyLocalsHOLFinite state) (.call none start [])
    (first.1, first.2.ffi.ioEvents) = (second.1, second.2.ffi.ioEvents) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun a => Classical.propDecidable (state.memaddrs a),
      fun a => Classical.propDecidable (state.shMemaddrs a)⟩
  let cleared := FiniteEvalContext.emptyLocalsContextHOLFinite context
  have hclear : evaluateHOLFiniteState (emptyLocalsHOLFinite state) (.call none start []) =
      (match evalPanSemRecursiveCallFiniteContext (.call none start []) cleared with
       | some pair => (pair.1, pair.2.state)
       | none => (none, emptyLocalsHOLFinite state)) := by
    unfold evaluateHOLFiniteState evaluateHOLFiniteStateWithDeciders
    rw [evalPanSemRecursiveCallFiniteContext_state_eq
      (.call none start []) _ cleared rfl]
    rfl
  rw [hclear]
  unfold evaluateHOLFiniteState evaluateHOLFiniteStateWithDeciders
  change _ = _
  rw [evalPanSemRecursiveCallFiniteContext.eq_5,
    evalPanSemRecursiveCallFiniteContext.eq_5]
  simp only [evalListHOLFinite, evalListHOLExact]
  cases hlookup : lookupCodeHOLFinite state.code.lookup start [] with
  | none => simp [context, cleared, emptyLocalsHOLFinite, hlookup]
  | some data =>
      obtain ⟨body, callee, shape⟩ := data
      have hentry : callEntryContextHOLFinite context callee =
          callEntryContextHOLFinite cleared callee := FiniteEvalContext.ext rfl
      by_cases hclock : state.clock = 0
      · simp [context, cleared, emptyLocalsHOLFinite, hlookup, hclock]
      · simp only [show cleared.state.code = state.code from rfl,
          show cleared.state.clock = state.clock from rfl, hlookup, if_neg hclock]
        rw [← hentry]
        cases hbody : evalPanSemRecursiveCallFiniteContext body
            (callEntryContextHOLFinite context callee) with
        | none => simp [emptyLocalsHOLFinite]
        | some output =>
            obtain ⟨result, post⟩ := output
            have hstate : callEntryStateHOLFinite context.state callee =
                callEntryStateHOLFinite cleared.state callee := rfl
            rw [← hstate]
            cases result with
            | none => rfl
            | some result =>
                cases result <;> try rfl
                rename_i value
                by_cases hshape : shapeEqHOL (shapeOfHOLExact value) shape = true
                · simp [hshape]
                  rfl
                · simp [hshape]
                  rfl

end Flapjack

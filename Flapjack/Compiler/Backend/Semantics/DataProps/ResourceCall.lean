import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceMonotonicity
import Flapjack.Misc.ClockWeightInduction

/-! Resource observations of data-language call setup and restoration. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- The three source observations used to propagate allocation failure.
This relation is Flapjack infrastructure for the evaluator induction. -/
def ResourceLe {C F : Type} (before after : State C F) : Prop :=
  before.ffi.ioEvents <+: after.ffi.ioEvents ∧
  BackendProps.optionLe before.stackMax after.stackMax ∧
  (after.safeForSpace = true → before.safeForSpace = true)

/-- Resource observations are reflexive. -/
theorem ResourceLe.refl {C F : Type} (state : State C F) : ResourceLe state state := by
  simp [ResourceLe, BackendProps.optionLe_refl]

/-- Resource observations compose through multiple state transitions. -/
theorem ResourceLe.trans {C F : Type} {first middle last : State C F}
    (a : ResourceLe first middle) (b : ResourceLe middle last) : ResourceLe first last :=
  ⟨List.IsPrefix.trans a.1 b.1, BackendProps.optionLe_trans _ _ _ ⟨a.2.1, b.2.1⟩,
    fun safe => a.2.2 (b.2.2 safe)⟩

/-- Pushing a call frame only grows the recorded stack maximum and can only
clear the safety flag; it leaves FFI events untouched. -/
theorem pushEnv_resourceLe {C F : Type} (env : Spt Value) (handler : Bool) (state : State C F) :
    ResourceLe state (pushEnv env handler state) := by
  unfold ResourceLe pushEnv
  simp only
  refine ⟨List.prefix_refl _, ?_, ?_⟩
  · exact (BackendProps.optionLe_max_right _ _ _).2 (Or.inl (BackendProps.optionLe_refl _))
  · simp
    tauto

/-- Entering a function maintains the same resource ordering. -/
theorem callEnv_resourceLe {C F : Type} (args : List Value) (size : Option Nat) (state : State C F) :
    ResourceLe state (callEnv args size state) := by
  unfold ResourceLe callEnv
  simp only
  refine ⟨List.prefix_refl _, ?_, ?_⟩
  · exact (BackendProps.optionLe_max_right _ _ _).2 (Or.inl (BackendProps.optionLe_refl _))
  · simp
    tauto

/-- Popping a saved frame preserves all three resource observations. -/
theorem popEnv_resourceLe {C F : Type} (state next : State C F) (run : popEnv state = some next) :
    ResourceLe state next := by
  cases stack : state.stack with
  | nil => simp [popEnv, stack] at run
  | cons frame rest =>
    cases frame <;> simp [popEnv, stack] at run <;> subst next <;> exact ResourceLe.refl _

/-- A tail call inherits resource monotonicity from its strictly lower-clock
callee, including bad lookups and timeout. This is one case of the pending
unrestricted evaluator induction. -/
theorem resourceMono_tailCall {C F : Type} (dest : Option Nat) (names : List Nat) (state : State C F)
    (calleeIH : ∀ (body : DataLang.Prog) (called : State C F), called.clock < state.clock → ResourceMono body called) :
    ResourceMono (.call none dest names none) state := by
  cases read : getVars names state.locals with
  | none => simp [ResourceMono, evaluate, read, BackendProps.optionLe_refl]
  | some values =>
    cases found : findCode dest values state.code state.stackFrameSizes with
    | none => simp [ResourceMono, evaluate, read, found, BackendProps.optionLe_refl]
    | some entry =>
      obtain ⟨args, body, size⟩ := entry
      by_cases zero : state.clock = 0
      · simp [ResourceMono, evaluate, read, found, zero, flushState, BackendProps.optionLe_refl]
      · let called := callEnv args size (decClock state)
        have clockLt : called.clock < state.clock := by
          simp [called, callEnv, decClock]
          omega
        have entryRel : ResourceLe state called := by
          simpa [called, ResourceLe, decClock] using callEnv_resourceLe args size (decClock state)
        have bodyRel : ResourceLe called (evaluate body called).2 := calleeIH body called clockLt
        have whole := entryRel.trans bodyRel
        cases bodyRun : evaluate body called with
        | mk result after =>
          have facts : ResourceLe state after := by simpa [bodyRun] using whole
          dsimp [called] at bodyRun
          cases result <;>
            simpa [ResourceMono, ResourceLe, evaluate, read, found, zero, bodyRun] using facts

/-- Tail-position force inherits the property from its lower-clock thunk
body; already evaluated thunks and all failing checks are covered directly. -/
theorem resourceMono_tailForce {C F : Type} (label src : Nat) (state : State C F)
    (calleeIH : ∀ (body : DataLang.Prog) (called : State C F), called.clock < state.clock → ResourceMono body called) :
    ResourceMono (.force none label src) state := by
  cases read : getVar src state.locals with
  | none => simp [ResourceMono, evaluate, read, BackendProps.optionLe_refl]
  | some thunk =>
    cases th : destThunk thunk state.refs with
    | badRef => simp [ResourceMono, evaluate, read, th, BackendProps.optionLe_refl]
    | notThunk => simp [ResourceMono, evaluate, read, th, BackendProps.optionLe_refl]
    | isThunk mode value =>
      cases mode with
      | evaluated => simp [ResourceMono, evaluate, read, th, flushState, BackendProps.optionLe_refl]
      | notEvaluated =>
        cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
        | none => simp [ResourceMono, evaluate, read, th, found, BackendProps.optionLe_refl]
        | some entry =>
          obtain ⟨args, body, size⟩ := entry
          by_cases zero : state.clock = 0
          · simp [ResourceMono, evaluate, read, th, found, zero, BackendProps.optionLe_refl]
          · let called := callEnv args size (decClock state)
            have clockLt : called.clock < state.clock := by
              simp [called, callEnv, decClock]
              omega
            have entryRel : ResourceLe state called := by
              simpa [called, ResourceLe, decClock] using callEnv_resourceLe args size (decClock state)
            have bodyRel : ResourceLe called (evaluate body called).2 := calleeIH body called clockLt
            have whole := entryRel.trans bodyRel
            cases bodyRun : evaluate body called with
            | mk result after =>
              have facts : ResourceLe state after := by simpa [bodyRun] using whole
              dsimp [called] at bodyRun
              cases result <;>
                simpa [ResourceMono, ResourceLe, evaluate, read, th, found, zero, bodyRun] using facts

/-- Returning force inherits source resource monotonicity from its lower-clock
thunk body, including caller-frame restoration after a single returned value. -/
theorem resourceMono_returningForce {C F : Type} (dest : Nat) (names : NumSet) (label src : Nat)
    (state : State C F)
    (calleeIH : ∀ (body : DataLang.Prog) (called : State C F), called.clock < state.clock → ResourceMono body called) :
    ResourceMono (.force (some (dest, names)) label src) state := by
  cases read : getVar src state.locals with
  | none => simp [ResourceMono, evaluate, read, BackendProps.optionLe_refl]
  | some thunk =>
    cases th : destThunk thunk state.refs with
    | badRef => simp [ResourceMono, evaluate, read, th, BackendProps.optionLe_refl]
    | notThunk => simp [ResourceMono, evaluate, read, th, BackendProps.optionLe_refl]
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        cases cut : cutEnv names state.locals <;>
          simp [ResourceMono, evaluate, read, th, cut, setVar, BackendProps.optionLe_refl]
      | notEvaluated =>
        cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
        | none => simp [ResourceMono, evaluate, read, th, found, BackendProps.optionLe_refl]
        | some entry =>
          obtain ⟨args, body, size⟩ := entry
          cases cut : cutEnv names state.locals with
          | none => simp [ResourceMono, evaluate, read, th, found, cut, BackendProps.optionLe_refl]
          | some env =>
            let called := callEnv args size (pushEnv env false (decClock state))
            have entryRel : ResourceLe state called := by
              have pushed := pushEnv_resourceLe env false (decClock state)
              have entered := callEnv_resourceLe args size (pushEnv env false (decClock state))
              have combined := pushed.trans entered
              simpa [ResourceLe, called, decClock] using combined
            by_cases zero : state.clock = 0
            · simpa [ResourceMono, ResourceLe, evaluate, read, th, found, cut, zero, called] using entryRel
            · have clockLt : called.clock < state.clock := by
                simp [called, callEnv, pushEnv, decClock]
                omega
              have bodyRel : ResourceLe called (evaluate body called).2 := calleeIH body called clockLt
              have clampedRel : ResourceLe state (fixClock called (evaluate body called)).2 := by
                have combined := entryRel.trans bodyRel
                simpa [ResourceLe, fixClock] using combined
              cases bodyRun : fixClock called (evaluate body called) with
              | mk result after =>
                have facts : ResourceLe state after := by simpa [bodyRun] using clampedRel
                dsimp [called] at bodyRun
                cases result with
                | none => simpa [ResourceMono, ResourceLe, evaluate, read, th, found, cut, zero, bodyRun] using facts
                | some result =>
                  cases result with
                  | err error => simpa [ResourceMono, ResourceLe, evaluate, read, th, found, cut, zero, bodyRun] using facts
                  | val values =>
                    cases values with
                    | nil => simpa [ResourceMono, ResourceLe, evaluate, read, th, found, cut, zero, bodyRun] using facts
                    | cons result rest =>
                      cases rest with
                      | cons other tail => simpa [ResourceMono, ResourceLe, evaluate, read, th, found, cut, zero, bodyRun] using facts
                      | nil =>
                        cases popped : popEnv after with
                        | none => simpa [ResourceMono, ResourceLe, evaluate, read, th, found, cut, zero, bodyRun, popped] using facts
                        | some final =>
                          have finalFacts := facts.trans (popEnv_resourceLe after final popped)
                          simpa [ResourceMono, ResourceLe, evaluate, read, th, found, cut, zero, bodyRun, popped, setVar] using finalFacts

/-- All force forms inherit resource monotonicity from lower-clock callees. -/
theorem resourceMono_force {C F : Type} (ret : Option (Nat × NumSet)) (label src : Nat)
    (state : State C F)
    (calleeIH : ∀ (body : DataLang.Prog) (called : State C F), called.clock < state.clock → ResourceMono body called) :
    ResourceMono (.force ret label src) state := by
  cases ret with
  | none => exact resourceMono_tailForce label src state calleeIH
  | some pair =>
    obtain ⟨dest, names⟩ := pair
    exact resourceMono_returningForce dest names label src state calleeIH

/-- A returning call without a handler inherits resource monotonicity from
its lower-clock callee, including argument checks and frame restoration. -/
theorem resourceMono_returningCall_noHandler {C F : Type} (returns : List Nat) (live : NumSet)
    (dest : Option Nat) (names : List Nat) (state : State C F)
    (calleeIH : ∀ (body : DataLang.Prog) (called : State C F), called.clock < state.clock → ResourceMono body called) :
    ResourceMono (.call (some (returns, live)) dest names none) state := by
  cases read : getVars names state.locals with
  | none => simp [ResourceMono, evaluate, read, BackendProps.optionLe_refl]
  | some values =>
    cases found : findCode dest values state.code state.stackFrameSizes with
    | none => simp [ResourceMono, evaluate, read, found, BackendProps.optionLe_refl]
    | some entry =>
      obtain ⟨args, body, size⟩ := entry
      by_cases distinct : returns.Nodup
      · cases cut : cutEnv live state.locals with
        | none => simp [ResourceMono, evaluate, read, found, distinct, cut, BackendProps.optionLe_refl]
        | some env =>
          let called := callEnv args size (pushEnv env false (decClock state))
          have entryRel : ResourceLe state called := by
            have pushed := pushEnv_resourceLe env false (decClock state)
            have entered := callEnv_resourceLe args size (pushEnv env false (decClock state))
            have combined := pushed.trans entered
            simpa [ResourceLe, called, decClock] using combined
          by_cases zero : state.clock = 0
          · simpa [ResourceMono, ResourceLe, evaluate, read, found, distinct, cut, zero, called] using entryRel
          · have clockLt : called.clock < state.clock := by
              simp [called, callEnv, pushEnv, decClock]
              omega
            have bodyRel : ResourceLe called (evaluate body called).2 := calleeIH body called clockLt
            have clampedRel : ResourceLe state (fixClock called (evaluate body called)).2 := by
              have combined := entryRel.trans bodyRel
              simpa [ResourceLe, fixClock] using combined
            cases bodyRun : fixClock called (evaluate body called) with
            | mk result after =>
              have facts : ResourceLe state after := by simpa [bodyRun] using clampedRel
              dsimp [called] at bodyRun
              cases result with
              | none => simpa [ResourceMono, ResourceLe, evaluate, read, found, distinct, cut, zero, bodyRun] using facts
              | some result =>
                cases result with
                | err error =>
                  cases error <;>
                    simpa [ResourceMono, ResourceLe, evaluate, read, found, distinct, cut, zero, bodyRun] using facts
                | val results =>
                  by_cases length : results.length = returns.length
                  · cases popped : popEnv after with
                    | none => simpa [ResourceMono, ResourceLe, evaluate, read, found, distinct, cut, zero, bodyRun, length, popped] using facts
                    | some final =>
                      have finalFacts := facts.trans (popEnv_resourceLe after final popped)
                      simpa [ResourceMono, ResourceLe, evaluate, read, found, distinct, cut, zero, bodyRun, length, popped, setVars] using finalFacts
                  · simpa [ResourceMono, ResourceLe, evaluate, read, found, distinct, cut, zero, bodyRun, length] using facts
      · simp [ResourceMono, evaluate, read, found, distinct, BackendProps.optionLe_refl]


/-- A returning call with a handler preserves the resource property through the handler. -/
theorem resourceMono_returningCall_handler {C F : Type} (returns : List Nat) (live : NumSet)
    (dest : Option Nat) (names : List Nat) (handlerName : Nat) (handlerBody : DataLang.Prog) (state : State C F)
    (calleeIH : ∀ (body : DataLang.Prog) (called : State C F), called.clock < state.clock → ResourceMono body called) :
    ResourceMono (.call (some (returns, live)) dest names (some (handlerName, handlerBody))) state := by
  cases read : getVars names state.locals with
  | none => simp [ResourceMono, evaluate, read, BackendProps.optionLe_refl]
  | some values =>
    cases found : findCode dest values state.code state.stackFrameSizes with
    | none => simp [ResourceMono, evaluate, read, found, BackendProps.optionLe_refl]
    | some entry =>
      obtain ⟨args, body, size⟩ := entry
      by_cases distinct : returns.Nodup
      · cases cut : cutEnv live state.locals with
        | none => simp [ResourceMono, evaluate, read, found, distinct, cut, BackendProps.optionLe_refl]
        | some env =>
          let called := callEnv args size (pushEnv env true (decClock state))
          have entryRel : ResourceLe state called := by
            have pushed := pushEnv_resourceLe env true (decClock state)
            have entered := callEnv_resourceLe args size (pushEnv env true (decClock state))
            have combined := pushed.trans entered
            simpa [ResourceLe, called, decClock] using combined
          by_cases zero : state.clock = 0
          · simpa [ResourceMono, ResourceLe, evaluate, read, found, distinct, cut, zero, called] using entryRel
          · have clockLt : called.clock < state.clock := by
              simp [called, callEnv, pushEnv, decClock]
              omega
            have bodyRel : ResourceLe called (evaluate body called).2 := calleeIH body called clockLt
            have clampedRel : ResourceLe state (fixClock called (evaluate body called)).2 := by
              have combined := entryRel.trans bodyRel
              simpa [ResourceLe, fixClock] using combined
            cases bodyRun : fixClock called (evaluate body called) with
            | mk result after =>
              have facts : ResourceLe state after := by simpa [bodyRun] using clampedRel
              have afterBound : after.clock ≤ called.clock := by
                have h := congrArg (fun p : EvalResult C F => p.2.clock) bodyRun
                simp [fixClock] at h
                omega
              dsimp [called] at bodyRun
              cases result with
              | none => simpa [ResourceMono, ResourceLe, evaluate, read, found, distinct, cut, zero, bodyRun] using facts
              | some result =>
                cases result with
                | err error =>
                  cases error with
                  | abort abort =>
                    simpa [ResourceMono, ResourceLe, evaluate, read, found, distinct, cut, zero, bodyRun] using facts
                  | raise raised =>
                    have handlerLt : (setVar handlerName raised after).clock < state.clock := by
                      simp [setVar]
                      omega
                    have handlerRel : ResourceLe after (evaluate handlerBody (setVar handlerName raised after)).2 := by
                      have h := calleeIH handlerBody (setVar handlerName raised after) handlerLt
                      simpa [ResourceMono, ResourceLe, setVar] using h
                    have finalFacts := facts.trans handlerRel
                    simpa [ResourceMono, ResourceLe, evaluate, read, found, distinct, cut, zero, bodyRun] using finalFacts
                | val results =>
                  by_cases length : results.length = returns.length
                  · cases popped : popEnv after with
                    | none => simpa [ResourceMono, ResourceLe, evaluate, read, found, distinct, cut, zero, bodyRun, length, popped] using facts
                    | some final =>
                      have finalFacts := facts.trans (popEnv_resourceLe after final popped)
                      simpa [ResourceMono, ResourceLe, evaluate, read, found, distinct, cut, zero, bodyRun, length, popped, setVars] using finalFacts
                  · simpa [ResourceMono, ResourceLe, evaluate, read, found, distinct, cut, zero, bodyRun, length] using facts
      · simp [ResourceMono, evaluate, read, found, distinct, BackendProps.optionLe_refl]

/-- Every source call form inherits resource monotonicity from lower-clock
callee and handler executions. -/
theorem resourceMono_call {C F : Type} (ret : Option (List Nat × NumSet)) (dest : Option Nat)
    (names : List Nat) (handler : Option (Nat × DataLang.Prog)) (state : State C F)
    (calleeIH : ∀ (body : DataLang.Prog) (called : State C F), called.clock < state.clock → ResourceMono body called) :
    ResourceMono (.call ret dest names handler) state := by
  cases ret with
  | none =>
    cases handler with
    | none => exact resourceMono_tailCall dest names state calleeIH
    | some handler =>
      cases read : getVars names state.locals with
      | none => simp [ResourceMono, evaluate, read, BackendProps.optionLe_refl]
      | some values =>
        cases found : findCode dest values state.code state.stackFrameSizes with
        | none => simp [ResourceMono, evaluate, read, found, BackendProps.optionLe_refl]
        | some entry =>
          obtain ⟨args, body, size⟩ := entry
          simp [ResourceMono, evaluate, read, found, BackendProps.optionLe_refl]
  | some pair =>
    obtain ⟨returns, live⟩ := pair
    cases handler with
    | none => exact resourceMono_returningCall_noHandler returns live dest names state calleeIH
    | some pair =>
      obtain ⟨name, body⟩ := pair
      exact resourceMono_returningCall_handler returns live dest names name body state calleeIH

/-- Every execution of the source data evaluator has monotone FFI events,
stack maximum, and space safety. This combined Lean theorem is infrastructure
for the separate HOL monotonicity declarations; it is not tagged as a port. -/
theorem evaluate_resourceMono {C F : Type} (program : DataLang.Prog) (state : State C F) :
    ResourceMono program state := by
  refine clockWeightInduction (α := DataLang.Prog) (σ := State C F) (·.clock) sizeOf
    (motive := fun program state => ResourceMono program state) ?_ program state
  intro program state exprIH smaller
  cases program with
  | skip => exact resourceMono_skip state
  | move dest src => exact resourceMono_move dest src state
  | assign dest op names live => exact resourceMono_assign_all dest op names live state
  | tick => exact resourceMono_tick state
  | makeSpace amount names => exact resourceMono_makeSpace amount names state
  | raise name => exact resourceMono_raise name state
  | «return» names => exact resourceMono_return names state
  | seq first second =>
    have firstMono : ResourceMono first state := by
      apply exprIH first state (by omega)
      simp only [DataLang.Prog.seq.sizeOf_spec] at ⊢
      omega
    apply resourceMono_seq_bounded first second state firstMono
    intro mid bound
    apply exprIH second mid (by omega)
    simp only [DataLang.Prog.seq.sizeOf_spec] at ⊢
    omega
  | ifThenElse name yes no =>
    apply resourceMono_if name yes no state
    · apply exprIH yes state (by omega)
      simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at ⊢
      omega
    · apply exprIH no state (by omega)
      simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at ⊢
      omega
  | force ret label src =>
    apply resourceMono_force ret label src state
    intro body next bound
    exact smaller body next (by omega)
  | call ret dest names handler =>
    apply resourceMono_call ret dest names handler state
    intro body next bound
    exact smaller body next (by omega)

/-- Successful primitive applications preserve the event prefix. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_io_events_mono"]
theorem doApp_events_of_result {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : State C F) (value : Value) (next : State C F)
    (run : doApp op args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents :=
  (doApp_resource_frame op args state next value run).1

/-- Successful primitive applications cannot increase space safety. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_safe_for_space_mono"]
theorem doApp_safety_of_result {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : State C F) (value : Value) (next : State C F)
    (premises : doApp op args state = .val (value, next) ∧ next.safeForSpace = true) :
    state.safeForSpace = true :=
  (doApp_resource_frame op args state next value premises.1).2.2 premises.2

/-- Successful primitive applications do not decrease the stack maximum. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_stack_max"]
theorem doApp_stack_of_result {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : State C F) (value : Value) (next : State C F)
    (run : doApp op args state = .val (value, next)) :
    BackendProps.optionLe state.stackMax next.stackMax :=
  (doApp_resource_frame op args state next value run).2.1

/-- Evaluation preserves the event prefix for an explicit evaluation result. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "evaluate_io_events_mono"]
theorem evaluate_events_of_result {C F : Type} (program : DataLang.Prog)
    (state : State C F) (result : Option (Result (List Value) Value)) (next : State C F)
    (run : evaluate program state = (result, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents := by
  simpa only [run] using (evaluate_resourceMono program state).1

/-- Evaluation cannot increase space safety. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "evaluate_safe_for_space_mono"]
theorem evaluate_safety_of_result {C F : Type} (program : DataLang.Prog)
    (state : State C F) (result : Option (Result (List Value) Value)) (next : State C F)
    (premises : evaluate program state = (result, next) ∧ next.safeForSpace = true) :
    state.safeForSpace = true := by
  apply (evaluate_resourceMono program state).2.2
  simpa only [premises.1] using premises.2

/-- Evaluation does not decrease the recorded stack maximum. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "evaluate_option_le_stack_max"]
theorem evaluate_stack_of_result {C F : Type} (program : DataLang.Prog)
    (state : State C F) (result : Option (Result (List Value) Value)) (next : State C F)
    (run : evaluate program state = (result, next)) :
    BackendProps.optionLe state.stackMax next.stackMax := by
  simpa only [run] using (evaluate_resourceMono program state).2.1

end Flapjack.Compiler.Backend.DataSem

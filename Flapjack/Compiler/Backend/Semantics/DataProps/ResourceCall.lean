import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceMonotonicity

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

end Flapjack.Compiler.Backend.DataSem

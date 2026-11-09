module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateSource

@[expose] public section

/-! I/O-event monotonicity for the faithful flat evaluator. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult)
/-- Flat evaluation extends the input FFI event trace in all three modes. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_io_events_mono"]
theorem evaluate_ioEventsMono {C F : Type} :
    (∀ (env : Environment Value) (state : State C F) (es : List FlatLang.Exp),
      state.ffi.ioEvents <+: (evaluate env state es).1.ffi.ioEvents) ∧
    (∀ (state : State C F) (d : FlatLang.Exp),
      state.ffi.ioEvents <+: (evaluateDec state d).1.ffi.ioEvents) ∧
    (∀ (state : State C F) (ds : List FlatLang.Exp),
      state.ffi.ioEvents <+: (evaluateDecs state ds).1.ffi.ioEvents) := by
  refine ⟨?_, ?_, ?_⟩
  · intro env state es
    exact (evaluate_clockAndEvents_mutual.1 env state es).2
  · intro state d
    have events := (evaluate_clockAndEvents_mutual.1 ⟨[]⟩ state [d]).2
    cases run : evaluate ⟨[]⟩ state [d] with
    | mk next result =>
      simp only [run] at events
      cases result with
      | err error => simpa [evaluateDec_source, run] using events
      | val values =>
        simp only [evaluateDec_source, run]
        split <;> exact events
  · intro state ds
    exact (evaluate_clockAndEvents_mutual.2 state ds).2
/-- The event-prefix result specialized to explicit evaluation outcomes. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_io_events_mono_IMP"]
theorem evaluate_ioEventsMono_imp {C F : Type} (env : Environment Value) (state : State C F)
    (es : List FlatLang.Exp) (next : State C F) (result : Result (List Value) Value)
    (d : FlatLang.Exp) (decResult : Option (ErrorResult Value)) (ds : List FlatLang.Exp)
    (decsResult : Option (ErrorResult Value)) :
    (evaluate env state es = (next, result) → state.ffi.ioEvents <+: next.ffi.ioEvents) ∧
    (evaluateDec state d = (next, decResult) → state.ffi.ioEvents <+: next.ffi.ioEvents) ∧
    (evaluateDecs state ds = (next, decsResult) → state.ffi.ioEvents <+: next.ffi.ioEvents) := by
  refine ⟨?_, ?_, ?_⟩
  · intro run
    simpa [run] using (evaluate_ioEventsMono (C := C) (F := F)).1 env state es
  · intro run
    simpa [run] using (evaluate_ioEventsMono (C := C) (F := F)).2.1 state d
  · intro run
    simpa [run] using (evaluate_ioEventsMono (C := C) (F := F)).2.2 state ds

/-- A single declaration extends the input event trace. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_dec_io_events_mono"]
theorem evaluateDec_ioEventsMono {C F : Type} :
    ∀ (d : FlatLang.Exp) (state : State C F),
      state.ffi.ioEvents <+: (evaluateDec state d).1.ffi.ioEvents := by
  intro d state
  exact (evaluate_ioEventsMono (C := C) (F := F)).2.1 state d

/-- A declaration-list result extends the input event trace. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_decs_io_events_mono"]
theorem evaluateDecs_ioEventsMono {C F : Type} :
    ∀ (ds : List FlatLang.Exp) (state next : State C F) (result : Option (ErrorResult Value)),
      evaluateDecs state ds = (next, result) → state.ffi.ioEvents <+: next.ffi.ioEvents := by
  intro ds state next result run
  simpa [run] using (evaluate_ioEventsMono (C := C) (F := F)).2.2 state ds

end Flapjack.Compiler.Backend.FlatProps

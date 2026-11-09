module

public import Flapjack.Compiler.Backend.FlatProps.EvaluateClockEvents
public import Flapjack.Compiler.Backend.Semantics.FlatSem.Semantics

@[expose] public section
/-! Initial-state clock corollaries for flat declaration evaluation. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL (ErrorResult Abort)
/-- Extending the initial clock preserves a declaration evaluation that did not time out. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_decs_add_to_clock_initial_state"]
theorem evaluateDecs_addToClock_initialState {C F : Type}
    (r : Option (ErrorResult Value)) (ffi : HolFfiState F) (k : Nat) (ec : InstallConfig C)
    (decs : List FlatLang.Exp) (s : State C F) (ck : Nat)
    (h : r ≠ some (.abort .timeoutError) ∧ evaluateDecs (initialState ffi k ec) decs = (s, r)) :
    evaluateDecs (initialState ffi (ck + k) ec) decs = ({ s with clock := s.clock + ck }, r) := by
  simpa [initialState, Nat.add_comm] using evaluateDecs_addToClock ck decs (initialState ffi k ec) s r h

/-- Extending the initial clock preserves the event prefix of a declaration run. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_decs_add_to_clock_initial_state_io_events_mono"]
theorem evaluateDecs_addToClock_initialState_ioEventsMono {C F : Type}
    (ffi : HolFfiState F) (k : Nat) (ec : InstallConfig C) (prog : List FlatLang.Exp)
    (s : State C F) (r : Option (ErrorResult Value)) (ck : Nat)
    (h : evaluateDecs (initialState ffi k ec) prog = (s, r)) :
    s.ffi.ioEvents <+: (evaluateDecs (initialState ffi (k + ck) ec) prog).1.ffi.ioEvents := by
  have ev := evaluateDecs_addToClock_ioEventsMono prog (initialState ffi k ec) ck
  simp only [h] at ev
  simpa [initialState] using ev

/-- Updating the clock of an initial state agrees with adding to its clock parameter. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "initial_state_with_clock"]
theorem initialState_withClock {C F : Type} (ffi : HolFfiState F) (k : Nat) (ec : InstallConfig C) (ck : Nat) :
    { initialState ffi k ec with clock := (initialState ffi k ec).clock + ck } = initialState ffi (k + ck) ec := by
  rfl
/-- An initial state has its supplied clock, and an update replaces it. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "initial_state_clock"]
theorem initialState_clock {C F : Type} (ffi : HolFfiState F) (k : Nat) (ec : InstallConfig C) (k1 : Nat) :
    (initialState ffi k ec).clock = k ∧
      { initialState ffi k ec with clock := k1 } = initialState ffi k1 ec := by
  exact ⟨rfl, rfl⟩

end Flapjack.Compiler.Backend.FlatProps

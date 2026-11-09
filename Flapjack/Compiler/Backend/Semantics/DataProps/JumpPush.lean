import Flapjack.Compiler.Backend.Semantics.DataProps.Jump

/-! Exception jumps across a saved non-handler call frame. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack

/-- Saving an ordinary environment does not change which exception frame is
selected. Only the non-control fields of the jumped state come from the new
call state. This auxiliary lemma has no direct HOL counterpart. -/
theorem jumpExc_pushEnv_noHandler {C F : Type} (state : State C F) (env : Spt Value) :
    jumpExc (pushEnv env false state) = (jumpExc state).map (fun jumped =>
      { (pushEnv env false state) with stack := jumped.stack, handler := jumped.handler, locals := jumped.locals, localsSize := jumped.localsSize }) := by
  by_cases inside : state.handler < state.stack.length
  · have shifted : state.handler < (Stack.env state.localsSize env :: state.stack).length := by simp; omega
    have offset : (Stack.env state.localsSize env :: state.stack).length - (state.handler + 1) =
        (state.stack.length - (state.handler + 1)) + 1 := by simp; omega
    simp only [jumpExc, pushEnv, List.length_cons, Bool.false_eq_true, ↓reduceIte, inside]
    simp only [List.length_cons] at shifted offset
    rw [if_pos shifted, offset]
    simp only [List.drop_succ_cons]
    split <;> rfl
  · by_cases shifted : state.handler < state.stack.length + 1
    · have equal : state.handler = state.stack.length := by omega
      simp [jumpExc, pushEnv, equal]
    · simp [jumpExc, pushEnv, inside, shifted]

/-- Entering a call without installing a handler leaves exception-frame
selection unchanged. This auxiliary lemma has no direct HOL counterpart. -/
theorem jumpExc_callEnv_push_noHandler {C F : Type} (state : State C F) (env : Spt Value)
    (args : List Value) (size : Option Nat) :
    jumpExc (callEnv args size (pushEnv env false (decClock state))) =
      (jumpExc state).map (fun jumped =>
        { (callEnv args size (pushEnv env false (decClock state))) with stack := jumped.stack, handler := jumped.handler, locals := jumped.locals, localsSize := jumped.localsSize }) := by
  let pushed := pushEnv env false (decClock state)
  let entered := callEnv args size pushed
  have stack : entered.stack = pushed.stack := rfl
  have handler : entered.handler = pushed.handler := rfl
  cases initial : jumpExc state with
  | none =>
    have decNone : jumpExc (decClock state) = none := by
      cases decRun : jumpExc (decClock state) with
      | none => rfl
      | some jumped =>
        have contradiction := jumpExc_transport (decClock state) state jumped rfl rfl decRun
        rw [initial] at contradiction
        contradiction
    have pushedNone : jumpExc pushed = none := by
      change jumpExc (pushEnv env false (decClock state)) = none
      rw [jumpExc_pushEnv_noHandler, decNone]
      rfl
    cases run : jumpExc entered with
    | none => rfl
    | some jumped =>
      have contradiction := jumpExc_transport entered pushed jumped stack.symm handler.symm run
      rw [pushedNone] at contradiction
      contradiction
  | some jumped =>
    have decJump : jumpExc (decClock state) = some { (decClock state) with stack := jumped.stack, handler := jumped.handler, locals := jumped.locals, localsSize := jumped.localsSize } :=
      jumpExc_transport state (decClock state) jumped rfl rfl initial
    have pushedJump := jumpExc_pushEnv_noHandler (decClock state) env
    rw [decJump] at pushedJump
    have enteredJump := jumpExc_transport pushed entered _ stack handler (by simpa [pushed] using pushedJump)
    simpa [pushed, entered, initial] using enteredJump

/-- A successful jump from an ordinary call frame identifies the original
caller jump and restores its saved control fields. -/
theorem jumpExc_callEnv_push_noHandler_inv {C F : Type} (state jumped : State C F) (env : Spt Value)
    (args : List Value) (size : Option Nat)
    (run : jumpExc (callEnv args size (pushEnv env false (decClock state))) = some jumped) :
    ∃ original, jumpExc state = some original ∧ jumped.stack = original.stack ∧ jumped.handler = original.handler := by
  rw [jumpExc_callEnv_push_noHandler] at run
  cases initial : jumpExc state with
  | none => simp [initial] at run
  | some original =>
    simp [initial] at run
    subst jumped
    exact ⟨original, rfl, rfl, rfl⟩

/-- The caller jump also supplies the restored local environment. -/
theorem jumpExc_callEnv_push_noHandler_inv_locals {C F : Type} (state jumped : State C F) (env : Spt Value)
    (args : List Value) (size : Option Nat)
    (run : jumpExc (callEnv args size (pushEnv env false (decClock state))) = some jumped) :
    ∃ original, jumpExc state = some original ∧ jumped.stack = original.stack ∧
      jumped.handler = original.handler ∧ jumped.locals = original.locals := by
  rw [jumpExc_callEnv_push_noHandler] at run
  cases initial : jumpExc state with
  | none => simp [initial] at run
  | some original =>
    simp [initial] at run
    subst jumped
    exact ⟨original, rfl, rfl, rfl, rfl⟩

end Flapjack.Compiler.Backend.DataSem

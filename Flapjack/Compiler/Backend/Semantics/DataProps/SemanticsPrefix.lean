module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Semantics
public import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceCall
public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateAddClockEvents

@[expose] public section

/-! Prefix facts about the data-language whole-program semantics. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Exact HOL `semantics_Term_IMP_PREFIX` (`dataPropsScript.sml:2193`): a
    terminating observation starts with the initial FFI trace. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "semantics_Term_IMP_PREFIX"]
theorem semanticsTermImpPrefix {C F : Type} (ffi : HolFfiState F)
    (prog : Spt (Nat × DataLang.Prog)) (co : CompileOracle C) (cc : Compiler C)
    (lim : Limits) (ss : Spt Nat) (start : Nat) (tt : HolOutcome) (l : List HolIoEvent)
    (run : semantics ffi prog co cc lim ss start = .terminate tt l) :
    List.IsPrefix ffi.ioEvents l := by
  unfold semantics at run
  dsimp only at run
  split_ifs at run with hfail
  cases obs : holOptionSome (terminatingObservation ffi prog co cc lim ss start) with
  | none =>
    simp only [obs] at run
    cases run
  | some behavior =>
    simp only [obs] at run
    rw [run] at obs
    have chosen := holOptionSome_some obs
    unfold terminatingObservation at chosen
    obtain ⟨clock, state, result, outcome, runEval, outcomeEq, behEq⟩ := chosen
    cases behEq
    have mono := evaluate_events_of_result (.call none (some start) [] none)
      (initialState ffi prog co cc true lim ss clock) (some result) state runEval
    simpa only [initialState] using mono

/-- Extending the initial clock by `extra` yields the initial state at the
    extended clock. Flapjack infrastructure for `semantics_Div_IMP_LPREFIX`; no
    separate HOL original. -/
private theorem initialState_clock_add {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × DataLang.Prog)) (oracle : CompileOracle C)
    (compiler : Compiler C) (limits : Limits) (frameSizes : Spt Nat)
    (clock extra : Nat) :
    { initialState ffi code oracle compiler true limits frameSizes clock with
      clock := (initialState ffi code oracle compiler true limits frameSizes clock).clock +
        extra } =
    initialState ffi code oracle compiler true limits frameSizes (clock + extra) := by
  simp only [initialState]

/-- The initial call at clock zero keeps the starting FFI state: every branch of
    the call either fails or times out before any FFI operation. Flapjack
    infrastructure for `semantics_Div_IMP_LPREFIX`; no separate HOL original. -/
private theorem initialCall_zero_ffi {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × DataLang.Prog)) (oracle : CompileOracle C)
    (compiler : Compiler C) (limits : Limits) (frameSizes : Spt Nat) (start : Nat) :
    (evaluate (.call none (some start) [] none)
      (initialState ffi code oracle compiler true limits frameSizes 0)).2.ffi = ffi := by
  simp only [evaluate, getVars]
  cases found : findCode (some start) []
      (initialState ffi code oracle compiler true limits frameSizes 0).code
      (initialState ffi code oracle compiler true limits frameSizes 0).stackFrameSizes with
  | none =>
    simp [typeError, initialState]
  | some entry =>
    obtain ⟨args, body, size⟩ := entry
    simp [initialState, timeoutError, flushState]

/-- Exact HOL `semantics_Div_IMP_LPREFIX` (`dataPropsScript.sml:2165`): a
    divergent observation starts with the initial FFI trace. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "semantics_Div_IMP_LPREFIX"]
theorem semanticsDivImpLprefix {C F : Type} (ffi : HolFfiState F)
    (prog : Spt (Nat × DataLang.Prog)) (co : CompileOracle C) (cc : Compiler C)
    (lim : Limits) (ss : Spt Nat) (start : Nat) (l : HolLList HolIoEvent)
    (run : semantics ffi prog co cc lim ss start = .diverge l) :
    HolLList.lprefix (HolLList.fromList ffi.ioEvents) l := by
  classical
  unfold semantics at run
  dsimp only at run
  cases obs : holOptionSome (terminatingObservation ffi prog co cc lim ss start) with
  | none =>
    simp only [obs] at run
    split_ifs at run with hfail
    all_goals cases run
    refine HolLList.buildLprefixLub_upper ?_ (HolLList.fromList ffi.ioEvents) ⟨0, ?_⟩
    · refine HolLList.lprefixChain_intro ?_
      intro ll1 ll2 h1 h2
      obtain ⟨k1, rfl⟩ := h1
      obtain ⟨k2, rfl⟩ := h2
      rcases Nat.le_total k1 k2 with hle | hle
      · left
        refine (HolLList.lprefix_fromList _ _).mpr ?_
        have mono := evaluate_add_clock_io_events_mono (.call none (some start) [] none)
          (initialState ffi prog co cc true lim ss k1) (k2 - k1)
        rw [initialState_clock_add] at mono
        have hk : k1 + (k2 - k1) = k2 := by omega
        rwa [hk] at mono
      · right
        refine (HolLList.lprefix_fromList _ _).mpr ?_
        have mono := evaluate_add_clock_io_events_mono (.call none (some start) [] none)
          (initialState ffi prog co cc true lim ss k2) (k1 - k2)
        rw [initialState_clock_add] at mono
        have hk : k2 + (k1 - k2) = k1 := by omega
        rwa [hk] at mono
    · rw [initialCall_zero_ffi]
  | some behavior =>
    simp only [obs] at run
    split_ifs at run with hfail
    · have observed := holOptionSome_some obs
      unfold terminatingObservation at observed
      obtain ⟨clock, state, result, outcome, runEval, ending, behEq⟩ := observed
      rw [behEq] at run
      cases run

end Flapjack.Compiler.Backend.DataProps

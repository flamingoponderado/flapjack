module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Semantics
public import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceCall

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

end Flapjack.Compiler.Backend.DataProps

import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact
import Flapjack.Misc.LprefixLub

/-! Initial state and observational semantics for the flat evaluator. -/
namespace Flapjack.Compiler.Backend.FlatSem

/-- The flat evaluator begins with no globals or references. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "initial_state_def"]
def initialState {C F : Type} (ffi : HolFfiState F) (clock : Nat) (evalConfig : InstallConfig C) : State C F :=
  ⟨clock, [], ffi, [], evalConfig⟩

/-- Observational behavior built from the current flat evaluator. Its
correspondence depends on the remaining source review of that evaluator, so
this definition is not yet tagged as the original HOL semantics. -/
noncomputable def semantics {C F : Type} (evalConfig : InstallConfig C)
    (ffi : HolFfiState F) (program : List FlatLang.Exp) : HolBehaviour :=
  open Classical in
  if ∃ clock, (evaluateDecs (initialState ffi clock evalConfig) program).2 = some (.abort .typeError)
  then .fail
  else
    match holOptionSome (fun behavior => ∃ clock state result outcome,
      evaluateDecs (initialState ffi clock evalConfig) program = (state, result) ∧
      (match result with
       | some (.abort (.ffiError event)) => outcome = HolOutcome.ffiOutcome event
       | some (.abort _) => False
       | _ => outcome = HolOutcome.success) ∧
      behavior = HolBehaviour.terminate outcome state.ffi.ioEvents) with
    | some behavior => behavior
    | none => .diverge (HolLList.buildLprefixLub (fun trace => ∃ clock,
        trace = HolLList.fromList (evaluateDecs (initialState ffi clock evalConfig) program).1.ffi.ioEvents))

/-- If no clock produces a type error, flat observational semantics does not
return failure. This is a consequence of the factored semantics definition. -/
theorem semantics_ne_fail {C F : Type} (evalConfig : InstallConfig C)
    (ffi : HolFfiState F) (program : List FlatLang.Exp)
    (safe : ∀ clock, (evaluateDecs (initialState ffi clock evalConfig) program).2 ≠
      some (.abort .typeError)) : semantics evalConfig ffi program ≠ .fail := by
  classical
  unfold semantics
  simp only [show ¬ ∃ clock, (evaluateDecs (initialState ffi clock evalConfig) program).2 =
    some (.abort .typeError) from fun ⟨clock, error⟩ => safe clock error, if_false]
  split
  · rename_i behavior chosen
    obtain ⟨_, _, _, _, _, _, shape⟩ := holOptionSome_some chosen
    rw [shape]
    intro impossible
    cases impossible
  · intro impossible
    cases impossible

/-- A terminating flat behavior comes from a finite evaluation and its
actual outcome and event trace. -/
theorem semantics_terminate {C F : Type} (evalConfig : InstallConfig C)
    (ffi : HolFfiState F) (program : List FlatLang.Exp) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : semantics evalConfig ffi program = .terminate outcome events) :
    ∃ clock state result,
      evaluateDecs (initialState ffi clock evalConfig) program = (state, result) ∧
      (match result with
       | some (.abort (.ffiError event)) => outcome = .ffiOutcome event
       | some (.abort _) => False
       | _ => outcome = .success) ∧ events = state.ffi.ioEvents := by
  classical
  unfold semantics at terminates
  split at terminates
  · cases terminates
  · split at terminates
    · rename_i behavior chosen
      obtain ⟨clock, state, result, resultOutcome, run, resultShape, shape⟩ := holOptionSome_some chosen
      rw [shape] at terminates
      cases terminates
      refine ⟨clock, state, result, run, ?_, rfl⟩
      cases result with
      | none => exact resultShape
      | some error => cases error with
        | raise value => exact resultShape
        | abort error => cases error <;> exact resultShape
    · cases terminates

/-- A diverging flat behavior has no terminating clock and uses the limit of
the clock-indexed event traces. -/
theorem semantics_diverge {C F : Type} (evalConfig : InstallConfig C)
    (ffi : HolFfiState F) (program : List FlatLang.Exp) (events : HolLList HolIoEvent)
    (diverges : semantics evalConfig ffi program = .diverge events) :
    (∀ clock state result (outcome : HolOutcome),
      evaluateDecs (initialState ffi clock evalConfig) program = (state, result) →
      (match result with
       | some (.abort (.ffiError event)) => outcome = .ffiOutcome event
       | some (.abort _) => False
       | _ => outcome = .success) → False) ∧
    events = HolLList.buildLprefixLub (fun trace => ∃ clock,
      trace = HolLList.fromList (evaluateDecs (initialState ffi clock evalConfig) program).1.ffi.ioEvents) := by
  classical
  unfold semantics at diverges
  split at diverges
  · cases diverges
  · split at diverges
    · rename_i behavior chosen
      obtain ⟨_, _, _, _, _, _, shape⟩ := holOptionSome_some chosen
      rw [shape] at diverges
      cases diverges
    · rename_i absent
      cases diverges
      refine ⟨?_, rfl⟩
      intro clock state result outcome run outcomeEq
      have impossible := holOptionSome_none absent (.terminate outcome state.ffi.ioEvents)
      apply impossible
      refine ⟨clock, state, result, outcome, run, ?_, rfl⟩
      cases result with
      | none => exact outcomeEq
      | some error => cases error with
        | raise value => exact outcomeEq
        | abort error => cases error <;> exact outcomeEq

end Flapjack.Compiler.Backend.FlatSem

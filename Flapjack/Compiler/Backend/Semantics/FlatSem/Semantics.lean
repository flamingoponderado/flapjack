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

end Flapjack.Compiler.Backend.FlatSem

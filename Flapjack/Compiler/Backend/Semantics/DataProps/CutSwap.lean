module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Control

@[expose] public section

/-! Cut-state behavior under resource-field updates. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Cutting locals commutes with resource-field updates. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "cut_state_opt_with_swap"]
theorem cutStateOpt_withSwap {C F : Type} (names : Option NumSet) (state : State C F)
    (mx : Option Nat) (safe : Bool) (peak : Nat) :
    cutStateOpt names {state with stackMax := mx, safeForSpace := safe, peakHeapLength := peak} =
      (cutStateOpt names state).map (fun t => {t with stackMax := mx, safeForSpace := safe, peakHeapLength := peak}) := by
  cases names with
  | none => rfl
  | some names =>
    simp only [cutStateOpt, cutState]
    cases found : cutEnv names state.locals <;> simp

/-- Cutting locals preserves the stack maximum. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "cut_state_opt_stack_max"]
theorem cutStateOpt_stackMax {C F : Type} (names : Option NumSet) (state next : State C F)
    (run : cutStateOpt names state = some next) : next.stackMax = state.stackMax := by
  cases names with
  | none => simpa [cutStateOpt] using congrArg (fun x : State C F => x.stackMax) (Option.some.inj run).symm
  | some names =>
    simp only [cutStateOpt, cutState] at run
    cases found : cutEnv names state.locals <;> simp [found] at run
    subst next
    rfl

/-- A successful cut makes an input stack-maximum update redundant. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "cut_state_opt_swap_input"]
theorem cutStateOpt_swapInput {C F : Type} (names : Option NumSet) (state next : State C F)
    (safe : Bool) (peak : Nat) (run : cutStateOpt names state = some next) :
    { next with stackMax := state.stackMax, safeForSpace := safe, peakHeapLength := peak } =
      { next with safeForSpace := safe, peakHeapLength := peak } := by
  rw [← cutStateOpt_stackMax names state next run]

end Flapjack.Compiler.Backend.DataProps

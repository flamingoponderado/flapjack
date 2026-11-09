import Flapjack.Compiler.Backend.Semantics.DataSem.State

/-! Record-update identities for data-language states. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack.Compiler.Backend.DataSem

/-- Updating a state field to its current value is redundant. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "s_peak_heap"]
theorem state_resourceUpdates {C F : Type} (state : State C F) (mx : Option Nat)
    (clock : Nat) (safe : Bool) (peak : Nat) :
    { state with peakHeapLength := state.peakHeapLength } = state ∧
    { state with safeForSpace := state.safeForSpace } = state ∧
    { state with stackMax := state.stackMax } = state ∧
    { state with localsSize := state.localsSize } = state ∧
    { state with stack := state.stack, stackMax := mx, clock := clock, safeForSpace := safe } =
      { state with stackMax := mx, clock := clock, safeForSpace := safe } ∧
    { state with handler := state.handler, safeForSpace := safe, peakHeapLength := peak } =
      { state with safeForSpace := safe, peakHeapLength := peak } := by
  cases state
  simp

end Flapjack.Compiler.Backend.DataProps

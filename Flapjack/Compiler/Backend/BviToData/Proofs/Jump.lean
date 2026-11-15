module

public import Flapjack.Compiler.Backend.Semantics.DataProps.Jump

@[expose] public section

/-! Exception-jump field updates used by the BVI-to-data proof. -/

namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Changing resource and frame-size fields commutes with a successful jump. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "jump_exc_sfs_lss_peak_safe"]
theorem jumpExc_peakSafeFrames {C F : Type} (state next : State C F) (safe : Bool) (peak : Nat)
    (localsSize : Option Nat) (sizes : Spt Nat) (stackMax : Option Nat) (run : jumpExc state = some next) :
    jumpExc { state with safeForSpace := safe, peakHeapLength := peak, localsSize := localsSize, stackFrameSizes := sizes, stackMax := stackMax } =
      some { next with safeForSpace := safe, peakHeapLength := peak, stackFrameSizes := sizes, stackMax := stackMax } := by
  have shape := jumpExc_transport state state next rfl rfl run
  have shape : next = { state with stack := next.stack, handler := next.handler, locals := next.locals, localsSize := next.localsSize } :=
    Option.some.inj (run.symm.trans shape)
  have changed := jumpExc_transport state { state with safeForSpace := safe, peakHeapLength := peak, localsSize := localsSize, stackFrameSizes := sizes, stackMax := stackMax } next rfl rfl run
  rw [changed]
  cases state
  cases next
  simp_all

/-- Changing resource fields commutes with a successful jump. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "jump_exc_peak_safe"]
theorem jumpExc_peakSafe {C F : Type} (state next : State C F) (safe : Bool) (peak : Nat)
    (localsSize stackMax : Option Nat) (run : jumpExc state = some next) :
    jumpExc { state with safeForSpace := safe, peakHeapLength := peak, localsSize := localsSize, stackMax := stackMax } =
      some { next with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } := by
  have shape := jumpExc_transport state state next rfl rfl run
  have shape : next = { state with stack := next.stack, handler := next.handler, locals := next.locals, localsSize := next.localsSize } :=
    Option.some.inj (run.symm.trans shape)
  have frames : next.stackFrameSizes = state.stackFrameSizes := by
    simpa using congrArg (fun s : State C F => s.stackFrameSizes) shape
  simpa [frames] using jumpExc_peakSafeFrames state next safe peak localsSize state.stackFrameSizes stackMax run

/-- A successful jump restores its saved local size, independent of the incoming one. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "jump_exc_lss"]
theorem jumpExc_localsSize {C F : Type} (state next : State C F) (localsSize : Option Nat)
    (run : jumpExc state = some next) : jumpExc { state with localsSize := localsSize } = some next := by
  have shape := jumpExc_transport state state next rfl rfl run
  have shape : next = { state with stack := next.stack, handler := next.handler, locals := next.locals, localsSize := next.localsSize } :=
    Option.some.inj (run.symm.trans shape)
  have changed := jumpExc_transport state { state with localsSize := localsSize } next rfl rfl run
  rw [changed]
  cases state
  cases next
  simp_all
end Flapjack.Compiler.Backend.BviToData

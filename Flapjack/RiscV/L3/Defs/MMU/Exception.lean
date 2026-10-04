import Flapjack.RiscV.L3.Support

/-! Complete original MMU exception-raising equation. -/
namespace Flapjack.RiscV.L3

/-- HOL types are intrinsically nonempty; Nonempty records that kind obligation,
as in the reviewed generic HD/EL/THE/LINV ports, without a chosen Lean default.
The return value is canonical unspecified ARB. Only the first exception is kept. -/
noncomputable def «raise'exception» {Ta : Type} [Nonempty Ta] (e : exception) :
    riscv_state → Ta × riscv_state := fun state =>
  (Flapjack.holArb Ta,
    if state.exception == exception.NoException then { state with exception := e } else state)

/-- Flapjack generic regression of the complete result, with no chosen-default
premise. This equation is derived infrastructure rather than a separate HOL port. -/
theorem raiseException_eq {Ta : Type} [Nonempty Ta] (e : exception) (state : riscv_state) :
    «raise'exception» (Ta := Ta) e state =
      (Flapjack.holArb Ta,
        if state.exception == exception.NoException then { state with exception := e } else state) := by
  rfl

end Flapjack.RiscV.L3

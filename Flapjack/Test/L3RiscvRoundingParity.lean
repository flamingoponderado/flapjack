import Flapjack.RiscV.L3.Defs

/-! Kernel replay of all original static rounding inputs and all dynamic FRM
inputs, plus all six L3 rounding constructors. Only procID and UCSR.fpcsr.FRM
are read; other original ARB fields are unread native defaults. These equations
use the four-constructor rounding carrier and no real-valued FP operation. -/
namespace Flapjack.Test.L3RiscvRoundingParity
open Flapjack.RiscV.L3 Flapjack

private def state (frm : BitVec 3) : riscv_state :=
  { (default : riscv_state) with
    procID := 0
    c_UCSR := fun _ => { (default : UserCSR) with
      fpcsr := { (default : FPCSR) with FRM := frm } } }

private def modes : List (Option HolRounding) :=
  [some .roundTiesToEven, some .roundTowardZero,
   some .roundTowardNegative, some .roundTowardPositive, none, none, none,
   some .roundTiesToEven]

example : ([Rounding.RNE, .RTZ, .RDN, .RUP, .RMM, .RDYN].map l3round) =
    [some .roundTiesToEven, some .roundTowardZero,
     some .roundTowardNegative, some .roundTowardPositive, none, none] := by decide
example : ([0,1,2,3,4,5,6,7].map fun n => round (BitVec.ofNat 3 n) (state 0)) =
    modes := by decide
example : ([0,1,2,3,4,5,6,7].map fun n => round 7 (state (BitVec.ofNat 3 n))) =
    modes.take 7 ++ [none] := by decide
end Flapjack.Test.L3RiscvRoundingParity

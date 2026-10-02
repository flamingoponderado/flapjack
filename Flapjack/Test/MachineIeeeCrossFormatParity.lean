import Flapjack.Misc.MachineIeee.Convert
import Flapjack.Misc.BinaryIeeeDirectedFp32
import Flapjack.Misc.BinaryIeeeDirectedFp64

/-! Fresh original rows in machine_ieee_cross_format_probe.out.
NaN rows observe all six flags, not an unspecified choice payload. Finite tie
checks observe the result and Precision only; the captured full underflow flags
are not claimed kernel-replayed by those projection checks. -/
namespace Flapjack.Test.MachineIeeeCrossFormatParity
open Flapjack
set_option maxRecDepth 200000
set_option maxHeartbeats 0
example : (holFp32ToFp64WithFlags 0x7f800000) = (holClearFlags, 0x7ff0000000000000) := by
  decide +kernel
example : (holFp32ToFp64WithFlags 0xff800000) = (holClearFlags, 0xfff0000000000000) := by
  decide +kernel
example : (holFp32ToFp64WithFlags 0x7fc00000).1 = holClearFlags := by
  decide +kernel
example : (holFp32ToFp64WithFlags 0x7f800001).1 = { holClearFlags with invalidOp := true } := by
  decide +kernel
example : (holFp64ToFp32WithFlags .roundTiesToEven 0x7ff0000000000000) = (holClearFlags, 0x7f800000) := by
  decide +kernel
example : (holFp64ToFp32WithFlags .roundTiesToEven 0xfff0000000000000) = (holClearFlags, 0xff800000) := by
  decide +kernel
example : (holFp64ToFp32WithFlags .roundTiesToEven 0x7ff8000000000000).1 = holClearFlags := by
  decide +kernel
example : (holFp64ToFp32WithFlags .roundTiesToEven 0x7ff0000000000001).1 = { holClearFlags with invalidOp := true } := by
  decide +kernel
example : holFp32ToFp64WithFlags 0x0 = (holClearFlags, 0x0) := by
  simp only [holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel
example : holFp32ToFp64WithFlags 0x3f800000 = (holClearFlags, 0x3ff0000000000000) := by
  simp only [holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel
example : holFp32ToFp64WithFlags 0x1 = (holClearFlags, 0x36a0000000000000) := by
  simp only [holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags, holFloatRound_fp64]
  decide +kernel
example : holFp64ToFp32WithFlags .roundTiesToEven 0x0 = (holClearFlags, 0x0) := by
  simp only [holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel
example : holFp64ToFp32WithFlags .roundTiesToEven 0x3ff0000000000000 = (holClearFlags, 0x3f800000) := by
  simp only [holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel
example : (holFp64ToFp32WithFlags .roundTiesToEven 0x3ff0000010000000).2 = 0x3f800000 := by
  simp only [holFp64ToFp32WithFlags, holMachineConvert, holRealToFp32WithFlags,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel
example : (holFp64ToFp32WithFlags .roundTiesToEven 0x3ff0000010000000).1.precision = true := by
  simp only [holFp64ToFp32WithFlags, holMachineConvert, holRealToFp32WithFlags,
    holFloatRoundWithFlags, holFloatRound_fp32]
  decide +kernel
end Flapjack.Test.MachineIeeeCrossFormatParity

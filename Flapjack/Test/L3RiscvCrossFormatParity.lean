import Flapjack.RiscV.L3.Defs
import Flapjack.Misc.BinaryIeeeDirectedFp32
import Flapjack.Misc.BinaryIeeeDirectedFp64

/-! All33 original cross-precision full-state observations from
l3_riscv_cross_format_probe.out. Unobserved ARB fields instantiate defaults.
Finite numerical choices use proved complete all-mode agreements; the rational
rendering assumption remains SOUNDNESS item8. NaN payload choices are covered
by full source helper review, not fixed by these finite/infinity regressions. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 2048
namespace Flapjack.Test.L3RiscvCrossFormatParity
open Flapjack.RiscV.L3 Flapjack
private def state (a : BitVec 64) (frm : BitVec 3) : riscv_state :=
  { (default : riscv_state) with
    procID := 7
    c_gpr := fun _ _ => 99
    c_fpr := fun c r => if c = 7 then if r = 1 then a else 0xcafe000000000000
      else 0xbbbb000000000000
    c_NextFetch := fun _ => none
    c_update := fun _ => { (default : StateDelta) with data1 := some 42 }
    c_UCSR := fun _ => { (default : UserCSR) with
      fpcsr := { (default : FPCSR) with NV := false, NX := true, FRM := frm } }
    c_MCSR := fun _ => { (default : MachineCSR) with
      mstatus := { (default : mstatus) with MFS := 0, MSD := false } } }
private def observe (s : riscv_state) :=
  (FPRD 3 s, FPRD 1 s, (MCSR s).mstatus.MFS, (MCSR s).mstatus.MSD,
    (Delta s).data1, (fcsr s).NV, (fcsr s).NX, s.c_fpr 8 3,
    match NextFetch s with
    | some (.Trap t) => decide (t.trap = ExceptionType.Illegal_Instr ∧ t.badaddr = none)
    | _ => false)

-- Original fcvt_s_d_zero_rte
example : observe («dfn'FCVT_S_D» (3,1,0) (state 0x0 0)) =
    (0xCAFE000000000000,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_D», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_d_negative_zero_rte
example : observe («dfn'FCVT_S_D» (3,1,0) (state 0x8000000000000000 0)) =
    (0xCAFE000000000000,0x8000000000000000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_D», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_d_negative_zero_rtz
example : observe («dfn'FCVT_S_D» (3,1,1) (state 0x8000000000000000 0)) =
    (0xCAFE000000000000,0x8000000000000000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_D», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_d_negative_zero_down
example : observe («dfn'FCVT_S_D» (3,1,2) (state 0x8000000000000000 0)) =
    (0xCAFE000080000000,0x8000000000000000,3,true,(some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_D», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_d_negative_zero_up
example : observe («dfn'FCVT_S_D» (3,1,3) (state 0x8000000000000000 0)) =
    (0xCAFE000000000000,0x8000000000000000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_D», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_d_one_rte
example : observe («dfn'FCVT_S_D» (3,1,0) (state 0x3ff0000000000000 0)) =
    (0xCAFE00003F800000,0x3FF0000000000000,3,true,(some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_D», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_d_one_rtz
example : observe («dfn'FCVT_S_D» (3,1,1) (state 0x3ff0000000000000 0)) =
    (0xCAFE00003F800000,0x3FF0000000000000,3,true,(some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_D», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_d_one_down
example : observe («dfn'FCVT_S_D» (3,1,2) (state 0x3ff0000000000000 0)) =
    (0xCAFE00003F800000,0x3FF0000000000000,3,true,(some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_D», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_d_one_up
example : observe («dfn'FCVT_S_D» (3,1,3) (state 0x3ff0000000000000 0)) =
    (0xCAFE00003F800000,0x3FF0000000000000,3,true,(some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_D», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_d_one_dynamic_up
example : observe («dfn'FCVT_S_D» (3,1,7) (state 0x3ff0000000000000 3)) =
    (0xCAFE00003F800000,0x3FF0000000000000,3,true,(some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_D», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_d_one_invalid_static
example : observe («dfn'FCVT_S_D» (3,1,4) (state 0x3ff0000000000000 0)) =
    (0xCAFE000000000000,0x3FF0000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_S_D», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_d_one_invalid_dynamic
example : observe («dfn'FCVT_S_D» (3,1,7) (state 0x3ff0000000000000 4)) =
    (0xCAFE000000000000,0x3FF0000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_S_D», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_d_tie_rte
example : observe («dfn'FCVT_S_D» (3,1,0) (state 0x3ff0000010000000 0)) =
    (0xCAFE00003F800000,0x3FF0000010000000,3,true,(some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_D», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_d_tie_rtz
example : observe («dfn'FCVT_S_D» (3,1,1) (state 0x3ff0000010000000 0)) =
    (0xCAFE00003F800000,0x3FF0000010000000,3,true,(some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_D», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_d_tie_down
example : observe («dfn'FCVT_S_D» (3,1,2) (state 0x3ff0000010000000 0)) =
    (0xCAFE00003F800000,0x3FF0000010000000,3,true,(some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_D», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_d_tie_up
example : observe («dfn'FCVT_S_D» (3,1,3) (state 0x3ff0000010000000 0)) =
    (0xCAFE00003F800001,0x3FF0000010000000,3,true,(some 0x3F800001),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_D», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_d_pinf_rte
example : observe («dfn'FCVT_S_D» (3,1,0) (state 0x7ff0000000000000 0)) =
    (0xCAFE00007F800000,0x7FF0000000000000,3,true,(some 0x7F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_D», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_d_ninf_rte
example : observe («dfn'FCVT_S_D» (3,1,0) (state 0xfff0000000000000 0)) =
    (0xCAFE0000FF800000,0xFFF0000000000000,3,true,(some 0xFF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_D», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_s_zero_rte
example : observe («dfn'FCVT_D_S» (3,1,0) (state 0x0 0)) =
    (0,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_S», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_s_negative_zero_rte
example : observe («dfn'FCVT_D_S» (3,1,0) (state 0x80000000 0)) =
    (0,0x80000000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_S», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_s_negative_zero_rtz
example : observe («dfn'FCVT_D_S» (3,1,1) (state 0x80000000 0)) =
    (0,0x80000000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_S», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_s_negative_zero_down
example : observe («dfn'FCVT_D_S» (3,1,2) (state 0x80000000 0)) =
    (0,0x80000000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_S», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_s_negative_zero_up
example : observe («dfn'FCVT_D_S» (3,1,3) (state 0x80000000 0)) =
    (0,0x80000000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_S», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_s_one_rte
example : observe («dfn'FCVT_D_S» (3,1,0) (state 0x3f800000 0)) =
    (0x3FF0000000000000,0x3F800000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_S», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_s_one_rtz
example : observe («dfn'FCVT_D_S» (3,1,1) (state 0x3f800000 0)) =
    (0x3FF0000000000000,0x3F800000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_S», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_s_one_down
example : observe («dfn'FCVT_D_S» (3,1,2) (state 0x3f800000 0)) =
    (0x3FF0000000000000,0x3F800000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_S», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_s_one_up
example : observe («dfn'FCVT_D_S» (3,1,3) (state 0x3f800000 0)) =
    (0x3FF0000000000000,0x3F800000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_S», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_s_one_dynamic_up
example : observe («dfn'FCVT_D_S» (3,1,7) (state 0x3f800000 3)) =
    (0x3FF0000000000000,0x3F800000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_S», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_s_one_invalid_static
example : observe («dfn'FCVT_D_S» (3,1,4) (state 0x3f800000 0)) =
    (0xCAFE000000000000,0x3F800000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_D_S», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_s_one_invalid_dynamic
example : observe («dfn'FCVT_D_S» (3,1,7) (state 0x3f800000 4)) =
    (0xCAFE000000000000,0x3F800000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_D_S», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_s_min_subnormal_rte
example : observe («dfn'FCVT_D_S» (3,1,0) (state 0x1 0)) =
    (0x36A0000000000000,1,3,true,(some 0x36A0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_S», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_s_pinf_rte
example : observe («dfn'FCVT_D_S» (3,1,0) (state 0x7f800000 0)) =
    (0x7FF0000000000000,0x7F800000,3,true,(some 0x7FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_S», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_s_ninf_rte
example : observe («dfn'FCVT_D_S» (3,1,0) (state 0xff800000 0)) =
    (0xFFF0000000000000,0xFF800000,3,true,(some 0xFFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_S», holFp32ToFp64, holFp64ToFp32,
    holFp32ToFp64WithFlags, holFp64ToFp32WithFlags, holMachineConvert,
    holRealToFp32WithFlags, holRealToFp64WithFlags, holFloatRoundWithFlags,
    holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

end Flapjack.Test.L3RiscvCrossFormatParity

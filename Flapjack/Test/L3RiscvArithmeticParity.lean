import Flapjack.RiscV.L3.Defs
import Flapjack.Misc.BinaryIeeeDirectedFp32
import Flapjack.Misc.BinaryIeeeDirectedFp64

/-! All140 original arithmetic regressions from l3_riscv_arithmetic_probe.out.
132 full ten-field numeric tuples and8 complete symbolic invalid-division state
equations. Unobserved ARB fields instantiate defaults; no NaN payload is chosen.
Rational rounding inherits SOUNDNESS item8, not HOL-to-Lean equivalence. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 2048
namespace Flapjack.Test.L3RiscvArithmeticParity
open Flapjack.RiscV.L3 Flapjack
private def state (a b : BitVec 64) (frm : BitVec 3) : riscv_state :=
  { (default : riscv_state) with
    procID := 7
    c_gpr := fun _ _ => 99
    c_fpr := fun c r => if c = 7 then if r = 1 then a else if r = 2 then b
      else 0xcafe000000000000 else 0xbbbb000000000000
    c_NextFetch := fun _ => none
    c_update := fun _ => { (default : StateDelta) with data1 := some 42 }
    c_UCSR := fun _ => { (default : UserCSR) with
      fpcsr := { (default : FPCSR) with NV := false, NX := true, FRM := frm } }
    c_MCSR := fun _ => { (default : MachineCSR) with
      mstatus := { (default : mstatus) with MFS := 0, MSD := false } } }
private def observe (s : riscv_state) :=
  (FPRD 3 s, FPRD 1 s, FPRD 2 s, (MCSR s).mstatus.MFS, (MCSR s).mstatus.MSD,
    (Delta s).data1, (fcsr s).NV, (fcsr s).NX, s.c_fpr 8 3,
    match NextFetch s with
    | some (.Trap t) => decide (t.trap = ExceptionType.Illegal_Instr ∧ t.badaddr = none)
    | _ => false)

-- Original fadd_s_one_two_rte
example : observe («dfn'FADD_S» (3,1,2,0) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE000040400000,0x3F800000,0x40000000,3,true,(some 0x40400000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_one_two_rtz
example : observe («dfn'FADD_S» (3,1,2,1) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE000040400000,0x3F800000,0x40000000,3,true,(some 0x40400000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_one_two_down
example : observe («dfn'FADD_S» (3,1,2,2) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE000040400000,0x3F800000,0x40000000,3,true,(some 0x40400000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_one_two_up
example : observe («dfn'FADD_S» (3,1,2,3) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE000040400000,0x3F800000,0x40000000,3,true,(some 0x40400000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_one_two_dynamic_up
example : observe («dfn'FADD_S» (3,1,2,7) (state 0x3f800000 0x40000000 3)) =
    (0xCAFE000040400000,0x3F800000,0x40000000,3,true,(some 0x40400000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_one_two_invalid_static
example : observe («dfn'FADD_S» (3,1,2,4) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE000000000000,0x3F800000,0x40000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_one_two_invalid_dynamic
example : observe («dfn'FADD_S» (3,1,2,7) (state 0x3f800000 0x40000000 4)) =
    (0xCAFE000000000000,0x3F800000,0x40000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_negative_one_two_rte
example : observe («dfn'FADD_S» (3,1,2,0) (state 0xbf800000 0x40000000 0)) =
    (0xCAFE00003F800000,0xBF800000,0x40000000,3,true,(some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_zero_negative_one_rte
example : observe («dfn'FADD_S» (3,1,2,0) (state 0x0 0xbf800000 0)) =
    (0xCAFE0000BF800000,0,0xBF800000,3,true,(some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_negative_zero_zero_rte
example : observe («dfn'FADD_S» (3,1,2,0) (state 0x80000000 0x0 0)) =
    (0xCAFE000000000000,0x80000000,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_negative_zero_zero_rtz
example : observe («dfn'FADD_S» (3,1,2,1) (state 0x80000000 0x0 0)) =
    (0xCAFE000000000000,0x80000000,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_negative_zero_zero_down
example : observe («dfn'FADD_S» (3,1,2,2) (state 0x80000000 0x0 0)) =
    (0xCAFE000080000000,0x80000000,0,3,true,(some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_negative_zero_zero_up
example : observe («dfn'FADD_S» (3,1,2,3) (state 0x80000000 0x0 0)) =
    (0xCAFE000000000000,0x80000000,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_cancel_rte
example : observe («dfn'FADD_S» (3,1,2,0) (state 0x3f800000 0xbf800000 0)) =
    (0xCAFE000000000000,0x3F800000,0xBF800000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_cancel_rtz
example : observe («dfn'FADD_S» (3,1,2,1) (state 0x3f800000 0xbf800000 0)) =
    (0xCAFE000000000000,0x3F800000,0xBF800000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_cancel_down
example : observe («dfn'FADD_S» (3,1,2,2) (state 0x3f800000 0xbf800000 0)) =
    (0xCAFE000080000000,0x3F800000,0xBF800000,3,true,(some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_cancel_up
example : observe («dfn'FADD_S» (3,1,2,3) (state 0x3f800000 0xbf800000 0)) =
    (0xCAFE000000000000,0x3F800000,0xBF800000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_tie_rte
example : observe («dfn'FADD_S» (3,1,2,0) (state 0x3f800000 0x33800000 0)) =
    (0xCAFE00003F800000,0x3F800000,0x33800000,3,true,(some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_tie_rtz
example : observe («dfn'FADD_S» (3,1,2,1) (state 0x3f800000 0x33800000 0)) =
    (0xCAFE00003F800000,0x3F800000,0x33800000,3,true,(some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_tie_down
example : observe («dfn'FADD_S» (3,1,2,2) (state 0x3f800000 0x33800000 0)) =
    (0xCAFE00003F800000,0x3F800000,0x33800000,3,true,(some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_tie_up
example : observe («dfn'FADD_S» (3,1,2,3) (state 0x3f800000 0x33800000 0)) =
    (0xCAFE00003F800001,0x3F800000,0x33800000,3,true,(some 0x3F800001),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_s_pinf_one_rte
example : observe («dfn'FADD_S» (3,1,2,0) (state 0x7f800000 0x3f800000 0)) =
    (0xCAFE00007F800000,0x7F800000,0x3F800000,3,true,(some 0x7F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_s_one_two_rte
example : observe («dfn'FSUB_S» (3,1,2,0) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE0000BF800000,0x3F800000,0x40000000,3,true,(some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_s_one_two_rtz
example : observe («dfn'FSUB_S» (3,1,2,1) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE0000BF800000,0x3F800000,0x40000000,3,true,(some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_s_one_two_down
example : observe («dfn'FSUB_S» (3,1,2,2) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE0000BF800000,0x3F800000,0x40000000,3,true,(some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_s_one_two_up
example : observe («dfn'FSUB_S» (3,1,2,3) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE0000BF800000,0x3F800000,0x40000000,3,true,(some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_s_one_two_dynamic_up
example : observe («dfn'FSUB_S» (3,1,2,7) (state 0x3f800000 0x40000000 3)) =
    (0xCAFE0000BF800000,0x3F800000,0x40000000,3,true,(some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_s_one_two_invalid_static
example : observe («dfn'FSUB_S» (3,1,2,4) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE000000000000,0x3F800000,0x40000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FSUB_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_s_one_two_invalid_dynamic
example : observe («dfn'FSUB_S» (3,1,2,7) (state 0x3f800000 0x40000000 4)) =
    (0xCAFE000000000000,0x3F800000,0x40000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FSUB_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_s_negative_one_two_rte
example : observe («dfn'FSUB_S» (3,1,2,0) (state 0xbf800000 0x40000000 0)) =
    (0xCAFE0000C0400000,0xBF800000,0x40000000,3,true,(some 0xC0400000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_s_zero_negative_one_rte
example : observe («dfn'FSUB_S» (3,1,2,0) (state 0x0 0xbf800000 0)) =
    (0xCAFE00003F800000,0,0xBF800000,3,true,(some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_s_negative_zero_zero_rte
example : observe («dfn'FSUB_S» (3,1,2,0) (state 0x80000000 0x0 0)) =
    (0xCAFE000080000000,0x80000000,0,3,true,(some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_s_negative_zero_zero_rtz
example : observe («dfn'FSUB_S» (3,1,2,1) (state 0x80000000 0x0 0)) =
    (0xCAFE000080000000,0x80000000,0,3,true,(some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_s_negative_zero_zero_down
example : observe («dfn'FSUB_S» (3,1,2,2) (state 0x80000000 0x0 0)) =
    (0xCAFE000080000000,0x80000000,0,3,true,(some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_s_negative_zero_zero_up
example : observe («dfn'FSUB_S» (3,1,2,3) (state 0x80000000 0x0 0)) =
    (0xCAFE000080000000,0x80000000,0,3,true,(some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_s_cancel_rte
example : observe («dfn'FSUB_S» (3,1,2,0) (state 0x3f800000 0x3f800000 0)) =
    (0xCAFE000000000000,0x3F800000,0x3F800000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_s_cancel_rtz
example : observe («dfn'FSUB_S» (3,1,2,1) (state 0x3f800000 0x3f800000 0)) =
    (0xCAFE000000000000,0x3F800000,0x3F800000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_s_cancel_down
example : observe («dfn'FSUB_S» (3,1,2,2) (state 0x3f800000 0x3f800000 0)) =
    (0xCAFE000080000000,0x3F800000,0x3F800000,3,true,(some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_s_cancel_up
example : observe («dfn'FSUB_S» (3,1,2,3) (state 0x3f800000 0x3f800000 0)) =
    (0xCAFE000000000000,0x3F800000,0x3F800000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_s_one_pinf_rte
example : observe («dfn'FSUB_S» (3,1,2,0) (state 0x3f800000 0x7f800000 0)) =
    (0xCAFE0000FF800000,0x3F800000,0x7F800000,3,true,(some 0xFF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_s_one_two_rte
example : observe («dfn'FMUL_S» (3,1,2,0) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE000040000000,0x3F800000,0x40000000,3,true,(some 0x40000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_s_one_two_rtz
example : observe («dfn'FMUL_S» (3,1,2,1) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE000040000000,0x3F800000,0x40000000,3,true,(some 0x40000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_s_one_two_down
example : observe («dfn'FMUL_S» (3,1,2,2) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE000040000000,0x3F800000,0x40000000,3,true,(some 0x40000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_s_one_two_up
example : observe («dfn'FMUL_S» (3,1,2,3) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE000040000000,0x3F800000,0x40000000,3,true,(some 0x40000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_s_one_two_dynamic_up
example : observe («dfn'FMUL_S» (3,1,2,7) (state 0x3f800000 0x40000000 3)) =
    (0xCAFE000040000000,0x3F800000,0x40000000,3,true,(some 0x40000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_s_one_two_invalid_static
example : observe («dfn'FMUL_S» (3,1,2,4) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE000000000000,0x3F800000,0x40000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FMUL_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_s_one_two_invalid_dynamic
example : observe («dfn'FMUL_S» (3,1,2,7) (state 0x3f800000 0x40000000 4)) =
    (0xCAFE000000000000,0x3F800000,0x40000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FMUL_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_s_negative_one_two_rte
example : observe («dfn'FMUL_S» (3,1,2,0) (state 0xbf800000 0x40000000 0)) =
    (0xCAFE0000C0000000,0xBF800000,0x40000000,3,true,(some 0xC0000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_s_zero_negative_one_rte
example : observe («dfn'FMUL_S» (3,1,2,0) (state 0x0 0xbf800000 0)) =
    (0xCAFE000080000000,0,0xBF800000,3,true,(some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_s_negative_zero_zero_rte
example : observe («dfn'FMUL_S» (3,1,2,0) (state 0x80000000 0x0 0)) =
    (0xCAFE000080000000,0x80000000,0,3,true,(some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_s_negative_zero_zero_rtz
example : observe («dfn'FMUL_S» (3,1,2,1) (state 0x80000000 0x0 0)) =
    (0xCAFE000080000000,0x80000000,0,3,true,(some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_s_negative_zero_zero_down
example : observe («dfn'FMUL_S» (3,1,2,2) (state 0x80000000 0x0 0)) =
    (0xCAFE000080000000,0x80000000,0,3,true,(some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_s_negative_zero_zero_up
example : observe («dfn'FMUL_S» (3,1,2,3) (state 0x80000000 0x0 0)) =
    (0xCAFE000080000000,0x80000000,0,3,true,(some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_s_pinf_negative_one_rte
example : observe («dfn'FMUL_S» (3,1,2,0) (state 0x7f800000 0xbf800000 0)) =
    (0xCAFE0000FF800000,0x7F800000,0xBF800000,3,true,(some 0xFF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_s_one_two_rte
example : observe («dfn'FDIV_S» (3,1,2,0) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE00003F000000,0x3F800000,0x40000000,3,true,(some 0x3F000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_s_one_two_rtz
example : observe («dfn'FDIV_S» (3,1,2,1) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE00003F000000,0x3F800000,0x40000000,3,true,(some 0x3F000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_s_one_two_down
example : observe («dfn'FDIV_S» (3,1,2,2) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE00003F000000,0x3F800000,0x40000000,3,true,(some 0x3F000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_s_one_two_up
example : observe («dfn'FDIV_S» (3,1,2,3) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE00003F000000,0x3F800000,0x40000000,3,true,(some 0x3F000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_s_one_two_dynamic_up
example : observe («dfn'FDIV_S» (3,1,2,7) (state 0x3f800000 0x40000000 3)) =
    (0xCAFE00003F000000,0x3F800000,0x40000000,3,true,(some 0x3F000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_s_one_two_invalid_static
example : observe («dfn'FDIV_S» (3,1,2,4) (state 0x3f800000 0x40000000 0)) =
    (0xCAFE000000000000,0x3F800000,0x40000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FDIV_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_s_one_two_invalid_dynamic
example : observe («dfn'FDIV_S» (3,1,2,7) (state 0x3f800000 0x40000000 4)) =
    (0xCAFE000000000000,0x3F800000,0x40000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FDIV_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_s_negative_one_two_rte
example : observe («dfn'FDIV_S» (3,1,2,0) (state 0xbf800000 0x40000000 0)) =
    (0xCAFE0000BF000000,0xBF800000,0x40000000,3,true,(some 0xBF000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_s_zero_negative_one_rte
example : observe («dfn'FDIV_S» (3,1,2,0) (state 0x0 0xbf800000 0)) =
    (0xCAFE000080000000,0,0xBF800000,3,true,(some 0x80000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original complete symbolic state equation fdiv_s_negative_zero_zero_rte
example : «dfn'FDIV_S» (3,1,2,0) (state 0x80000000 0x0 0) =
    writeFPRS (3, holFloatToFp32 (holFloatSomeQnan
      (.fpDiv .roundTiesToEven (holFp32ToFloat 0x80000000) (holFp32ToFloat 0)))) (state 0x80000000 0x0 0) := by
  change writeFPRS (3, holFloatToFp32
    (holFloatDiv .roundTiesToEven (holFp32ToFloat 0x80000000) (holFp32ToFloat 0)).2) (state 0x80000000 0x0 0) = _
  have hx : holFloatValue (holFp32ToFloat 0x80000000) = .float 0 := by decide +kernel
  have hy : holFloatValue (holFp32ToFloat 0) = .float 0 := by decide +kernel
  simp only [holFloatDiv, hx, hy, if_true]


-- Original complete symbolic state equation fdiv_s_negative_zero_zero_rtz
example : «dfn'FDIV_S» (3,1,2,1) (state 0x80000000 0x0 0) =
    writeFPRS (3, holFloatToFp32 (holFloatSomeQnan
      (.fpDiv .roundTowardZero (holFp32ToFloat 0x80000000) (holFp32ToFloat 0)))) (state 0x80000000 0x0 0) := by
  change writeFPRS (3, holFloatToFp32
    (holFloatDiv .roundTowardZero (holFp32ToFloat 0x80000000) (holFp32ToFloat 0)).2) (state 0x80000000 0x0 0) = _
  have hx : holFloatValue (holFp32ToFloat 0x80000000) = .float 0 := by decide +kernel
  have hy : holFloatValue (holFp32ToFloat 0) = .float 0 := by decide +kernel
  simp only [holFloatDiv, hx, hy, if_true]


-- Original complete symbolic state equation fdiv_s_negative_zero_zero_down
example : «dfn'FDIV_S» (3,1,2,2) (state 0x80000000 0x0 0) =
    writeFPRS (3, holFloatToFp32 (holFloatSomeQnan
      (.fpDiv .roundTowardNegative (holFp32ToFloat 0x80000000) (holFp32ToFloat 0)))) (state 0x80000000 0x0 0) := by
  change writeFPRS (3, holFloatToFp32
    (holFloatDiv .roundTowardNegative (holFp32ToFloat 0x80000000) (holFp32ToFloat 0)).2) (state 0x80000000 0x0 0) = _
  have hx : holFloatValue (holFp32ToFloat 0x80000000) = .float 0 := by decide +kernel
  have hy : holFloatValue (holFp32ToFloat 0) = .float 0 := by decide +kernel
  simp only [holFloatDiv, hx, hy, if_true]


-- Original complete symbolic state equation fdiv_s_negative_zero_zero_up
example : «dfn'FDIV_S» (3,1,2,3) (state 0x80000000 0x0 0) =
    writeFPRS (3, holFloatToFp32 (holFloatSomeQnan
      (.fpDiv .roundTowardPositive (holFp32ToFloat 0x80000000) (holFp32ToFloat 0)))) (state 0x80000000 0x0 0) := by
  change writeFPRS (3, holFloatToFp32
    (holFloatDiv .roundTowardPositive (holFp32ToFloat 0x80000000) (holFp32ToFloat 0)).2) (state 0x80000000 0x0 0) = _
  have hx : holFloatValue (holFp32ToFloat 0x80000000) = .float 0 := by decide +kernel
  have hy : holFloatValue (holFp32ToFloat 0) = .float 0 := by decide +kernel
  simp only [holFloatDiv, hx, hy, if_true]


-- Original fdiv_s_one_zero_rte
example : observe («dfn'FDIV_S» (3,1,2,0) (state 0x3f800000 0x0 0)) =
    (0xCAFE00007F800000,0x3F800000,0,3,true,(some 0x7F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_s_one_pinf_rte
example : observe («dfn'FDIV_S» (3,1,2,0) (state 0x3f800000 0x7f800000 0)) =
    (0xCAFE000000000000,0x3F800000,0x7F800000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_s_pinf_negative_one_rte
example : observe («dfn'FDIV_S» (3,1,2,0) (state 0x7f800000 0xbf800000 0)) =
    (0xCAFE0000FF800000,0x7F800000,0xBF800000,3,true,(some 0xFF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_S», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_one_two_rte
example : observe («dfn'FADD_D» (3,1,2,0) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0x4008000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0x4008000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_one_two_rtz
example : observe («dfn'FADD_D» (3,1,2,1) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0x4008000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0x4008000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_one_two_down
example : observe («dfn'FADD_D» (3,1,2,2) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0x4008000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0x4008000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_one_two_up
example : observe («dfn'FADD_D» (3,1,2,3) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0x4008000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0x4008000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_one_two_dynamic_up
example : observe («dfn'FADD_D» (3,1,2,7) (state 0x3ff0000000000000 0x4000000000000000 3)) =
    (0x4008000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0x4008000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_one_two_invalid_static
example : observe («dfn'FADD_D» (3,1,2,4) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0xCAFE000000000000,0x3FF0000000000000,0x4000000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_one_two_invalid_dynamic
example : observe («dfn'FADD_D» (3,1,2,7) (state 0x3ff0000000000000 0x4000000000000000 4)) =
    (0xCAFE000000000000,0x3FF0000000000000,0x4000000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_negative_one_two_rte
example : observe («dfn'FADD_D» (3,1,2,0) (state 0xbff0000000000000 0x4000000000000000 0)) =
    (0x3FF0000000000000,0xBFF0000000000000,0x4000000000000000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_zero_negative_one_rte
example : observe («dfn'FADD_D» (3,1,2,0) (state 0x0 0xbff0000000000000 0)) =
    (0xBFF0000000000000,0,0xBFF0000000000000,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_negative_zero_zero_rte
example : observe («dfn'FADD_D» (3,1,2,0) (state 0x8000000000000000 0x0 0)) =
    (0,0x8000000000000000,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_negative_zero_zero_rtz
example : observe («dfn'FADD_D» (3,1,2,1) (state 0x8000000000000000 0x0 0)) =
    (0,0x8000000000000000,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_negative_zero_zero_down
example : observe («dfn'FADD_D» (3,1,2,2) (state 0x8000000000000000 0x0 0)) =
    (0x8000000000000000,0x8000000000000000,0,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_negative_zero_zero_up
example : observe («dfn'FADD_D» (3,1,2,3) (state 0x8000000000000000 0x0 0)) =
    (0,0x8000000000000000,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_cancel_rte
example : observe («dfn'FADD_D» (3,1,2,0) (state 0x3ff0000000000000 0xbff0000000000000 0)) =
    (0,0x3FF0000000000000,0xBFF0000000000000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_cancel_rtz
example : observe («dfn'FADD_D» (3,1,2,1) (state 0x3ff0000000000000 0xbff0000000000000 0)) =
    (0,0x3FF0000000000000,0xBFF0000000000000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_cancel_down
example : observe («dfn'FADD_D» (3,1,2,2) (state 0x3ff0000000000000 0xbff0000000000000 0)) =
    (0x8000000000000000,0x3FF0000000000000,0xBFF0000000000000,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_cancel_up
example : observe («dfn'FADD_D» (3,1,2,3) (state 0x3ff0000000000000 0xbff0000000000000 0)) =
    (0,0x3FF0000000000000,0xBFF0000000000000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_tie_rte
example : observe («dfn'FADD_D» (3,1,2,0) (state 0x3ff0000000000000 0x3ca0000000000000 0)) =
    (0x3FF0000000000000,0x3FF0000000000000,0x3CA0000000000000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_tie_rtz
example : observe («dfn'FADD_D» (3,1,2,1) (state 0x3ff0000000000000 0x3ca0000000000000 0)) =
    (0x3FF0000000000000,0x3FF0000000000000,0x3CA0000000000000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_tie_down
example : observe («dfn'FADD_D» (3,1,2,2) (state 0x3ff0000000000000 0x3ca0000000000000 0)) =
    (0x3FF0000000000000,0x3FF0000000000000,0x3CA0000000000000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_tie_up
example : observe («dfn'FADD_D» (3,1,2,3) (state 0x3ff0000000000000 0x3ca0000000000000 0)) =
    (0x3FF0000000000001,0x3FF0000000000000,0x3CA0000000000000,3,true,(some 0x3FF0000000000001),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fadd_d_pinf_one_rte
example : observe («dfn'FADD_D» (3,1,2,0) (state 0x7ff0000000000000 0x3ff0000000000000 0)) =
    (0x7FF0000000000000,0x7FF0000000000000,0x3FF0000000000000,3,true,(some 0x7FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FADD_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_d_one_two_rte
example : observe («dfn'FSUB_D» (3,1,2,0) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0xBFF0000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_d_one_two_rtz
example : observe («dfn'FSUB_D» (3,1,2,1) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0xBFF0000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_d_one_two_down
example : observe («dfn'FSUB_D» (3,1,2,2) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0xBFF0000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_d_one_two_up
example : observe («dfn'FSUB_D» (3,1,2,3) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0xBFF0000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_d_one_two_dynamic_up
example : observe («dfn'FSUB_D» (3,1,2,7) (state 0x3ff0000000000000 0x4000000000000000 3)) =
    (0xBFF0000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_d_one_two_invalid_static
example : observe («dfn'FSUB_D» (3,1,2,4) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0xCAFE000000000000,0x3FF0000000000000,0x4000000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FSUB_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_d_one_two_invalid_dynamic
example : observe («dfn'FSUB_D» (3,1,2,7) (state 0x3ff0000000000000 0x4000000000000000 4)) =
    (0xCAFE000000000000,0x3FF0000000000000,0x4000000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FSUB_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_d_negative_one_two_rte
example : observe («dfn'FSUB_D» (3,1,2,0) (state 0xbff0000000000000 0x4000000000000000 0)) =
    (0xC008000000000000,0xBFF0000000000000,0x4000000000000000,3,true,(some 0xC008000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_d_zero_negative_one_rte
example : observe («dfn'FSUB_D» (3,1,2,0) (state 0x0 0xbff0000000000000 0)) =
    (0x3FF0000000000000,0,0xBFF0000000000000,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_d_negative_zero_zero_rte
example : observe («dfn'FSUB_D» (3,1,2,0) (state 0x8000000000000000 0x0 0)) =
    (0x8000000000000000,0x8000000000000000,0,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_d_negative_zero_zero_rtz
example : observe («dfn'FSUB_D» (3,1,2,1) (state 0x8000000000000000 0x0 0)) =
    (0x8000000000000000,0x8000000000000000,0,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_d_negative_zero_zero_down
example : observe («dfn'FSUB_D» (3,1,2,2) (state 0x8000000000000000 0x0 0)) =
    (0x8000000000000000,0x8000000000000000,0,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_d_negative_zero_zero_up
example : observe («dfn'FSUB_D» (3,1,2,3) (state 0x8000000000000000 0x0 0)) =
    (0x8000000000000000,0x8000000000000000,0,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_d_cancel_rte
example : observe («dfn'FSUB_D» (3,1,2,0) (state 0x3ff0000000000000 0x3ff0000000000000 0)) =
    (0,0x3FF0000000000000,0x3FF0000000000000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_d_cancel_rtz
example : observe («dfn'FSUB_D» (3,1,2,1) (state 0x3ff0000000000000 0x3ff0000000000000 0)) =
    (0,0x3FF0000000000000,0x3FF0000000000000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_d_cancel_down
example : observe («dfn'FSUB_D» (3,1,2,2) (state 0x3ff0000000000000 0x3ff0000000000000 0)) =
    (0x8000000000000000,0x3FF0000000000000,0x3FF0000000000000,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_d_cancel_up
example : observe («dfn'FSUB_D» (3,1,2,3) (state 0x3ff0000000000000 0x3ff0000000000000 0)) =
    (0,0x3FF0000000000000,0x3FF0000000000000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fsub_d_one_pinf_rte
example : observe («dfn'FSUB_D» (3,1,2,0) (state 0x3ff0000000000000 0x7ff0000000000000 0)) =
    (0xFFF0000000000000,0x3FF0000000000000,0x7FF0000000000000,3,true,(some 0xFFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FSUB_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_d_one_two_rte
example : observe («dfn'FMUL_D» (3,1,2,0) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0x4000000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0x4000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_d_one_two_rtz
example : observe («dfn'FMUL_D» (3,1,2,1) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0x4000000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0x4000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_d_one_two_down
example : observe («dfn'FMUL_D» (3,1,2,2) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0x4000000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0x4000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_d_one_two_up
example : observe («dfn'FMUL_D» (3,1,2,3) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0x4000000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0x4000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_d_one_two_dynamic_up
example : observe («dfn'FMUL_D» (3,1,2,7) (state 0x3ff0000000000000 0x4000000000000000 3)) =
    (0x4000000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0x4000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_d_one_two_invalid_static
example : observe («dfn'FMUL_D» (3,1,2,4) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0xCAFE000000000000,0x3FF0000000000000,0x4000000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FMUL_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_d_one_two_invalid_dynamic
example : observe («dfn'FMUL_D» (3,1,2,7) (state 0x3ff0000000000000 0x4000000000000000 4)) =
    (0xCAFE000000000000,0x3FF0000000000000,0x4000000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FMUL_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_d_negative_one_two_rte
example : observe («dfn'FMUL_D» (3,1,2,0) (state 0xbff0000000000000 0x4000000000000000 0)) =
    (0xC000000000000000,0xBFF0000000000000,0x4000000000000000,3,true,(some 0xC000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_d_zero_negative_one_rte
example : observe («dfn'FMUL_D» (3,1,2,0) (state 0x0 0xbff0000000000000 0)) =
    (0x8000000000000000,0,0xBFF0000000000000,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_d_negative_zero_zero_rte
example : observe («dfn'FMUL_D» (3,1,2,0) (state 0x8000000000000000 0x0 0)) =
    (0x8000000000000000,0x8000000000000000,0,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_d_negative_zero_zero_rtz
example : observe («dfn'FMUL_D» (3,1,2,1) (state 0x8000000000000000 0x0 0)) =
    (0x8000000000000000,0x8000000000000000,0,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_d_negative_zero_zero_down
example : observe («dfn'FMUL_D» (3,1,2,2) (state 0x8000000000000000 0x0 0)) =
    (0x8000000000000000,0x8000000000000000,0,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_d_negative_zero_zero_up
example : observe («dfn'FMUL_D» (3,1,2,3) (state 0x8000000000000000 0x0 0)) =
    (0x8000000000000000,0x8000000000000000,0,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fmul_d_pinf_negative_one_rte
example : observe («dfn'FMUL_D» (3,1,2,0) (state 0x7ff0000000000000 0xbff0000000000000 0)) =
    (0xFFF0000000000000,0x7FF0000000000000,0xBFF0000000000000,3,true,(some 0xFFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FMUL_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_d_one_two_rte
example : observe («dfn'FDIV_D» (3,1,2,0) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0x3FE0000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0x3FE0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_d_one_two_rtz
example : observe («dfn'FDIV_D» (3,1,2,1) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0x3FE0000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0x3FE0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_d_one_two_down
example : observe («dfn'FDIV_D» (3,1,2,2) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0x3FE0000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0x3FE0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_d_one_two_up
example : observe («dfn'FDIV_D» (3,1,2,3) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0x3FE0000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0x3FE0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_d_one_two_dynamic_up
example : observe («dfn'FDIV_D» (3,1,2,7) (state 0x3ff0000000000000 0x4000000000000000 3)) =
    (0x3FE0000000000000,0x3FF0000000000000,0x4000000000000000,3,true,(some 0x3FE0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_d_one_two_invalid_static
example : observe («dfn'FDIV_D» (3,1,2,4) (state 0x3ff0000000000000 0x4000000000000000 0)) =
    (0xCAFE000000000000,0x3FF0000000000000,0x4000000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FDIV_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_d_one_two_invalid_dynamic
example : observe («dfn'FDIV_D» (3,1,2,7) (state 0x3ff0000000000000 0x4000000000000000 4)) =
    (0xCAFE000000000000,0x3FF0000000000000,0x4000000000000000,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FDIV_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_d_negative_one_two_rte
example : observe («dfn'FDIV_D» (3,1,2,0) (state 0xbff0000000000000 0x4000000000000000 0)) =
    (0xBFE0000000000000,0xBFF0000000000000,0x4000000000000000,3,true,(some 0xBFE0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_d_zero_negative_one_rte
example : observe («dfn'FDIV_D» (3,1,2,0) (state 0x0 0xbff0000000000000 0)) =
    (0x8000000000000000,0,0xBFF0000000000000,3,true,(some 0x8000000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original complete symbolic state equation fdiv_d_negative_zero_zero_rte
example : «dfn'FDIV_D» (3,1,2,0) (state 0x8000000000000000 0x0 0) =
    writeFPRD (3, holFloatToFp64 (holFloatSomeQnan
      (.fpDiv .roundTiesToEven (holFp64ToFloat 0x8000000000000000) (holFp64ToFloat 0)))) (state 0x8000000000000000 0x0 0) := by
  change writeFPRD (3, holFloatToFp64
    (holFloatDiv .roundTiesToEven (holFp64ToFloat 0x8000000000000000) (holFp64ToFloat 0)).2) (state 0x8000000000000000 0x0 0) = _
  have hx : holFloatValue (holFp64ToFloat 0x8000000000000000) = .float 0 := by decide +kernel
  have hy : holFloatValue (holFp64ToFloat 0) = .float 0 := by decide +kernel
  simp only [holFloatDiv, hx, hy, if_true]


-- Original complete symbolic state equation fdiv_d_negative_zero_zero_rtz
example : «dfn'FDIV_D» (3,1,2,1) (state 0x8000000000000000 0x0 0) =
    writeFPRD (3, holFloatToFp64 (holFloatSomeQnan
      (.fpDiv .roundTowardZero (holFp64ToFloat 0x8000000000000000) (holFp64ToFloat 0)))) (state 0x8000000000000000 0x0 0) := by
  change writeFPRD (3, holFloatToFp64
    (holFloatDiv .roundTowardZero (holFp64ToFloat 0x8000000000000000) (holFp64ToFloat 0)).2) (state 0x8000000000000000 0x0 0) = _
  have hx : holFloatValue (holFp64ToFloat 0x8000000000000000) = .float 0 := by decide +kernel
  have hy : holFloatValue (holFp64ToFloat 0) = .float 0 := by decide +kernel
  simp only [holFloatDiv, hx, hy, if_true]


-- Original complete symbolic state equation fdiv_d_negative_zero_zero_down
example : «dfn'FDIV_D» (3,1,2,2) (state 0x8000000000000000 0x0 0) =
    writeFPRD (3, holFloatToFp64 (holFloatSomeQnan
      (.fpDiv .roundTowardNegative (holFp64ToFloat 0x8000000000000000) (holFp64ToFloat 0)))) (state 0x8000000000000000 0x0 0) := by
  change writeFPRD (3, holFloatToFp64
    (holFloatDiv .roundTowardNegative (holFp64ToFloat 0x8000000000000000) (holFp64ToFloat 0)).2) (state 0x8000000000000000 0x0 0) = _
  have hx : holFloatValue (holFp64ToFloat 0x8000000000000000) = .float 0 := by decide +kernel
  have hy : holFloatValue (holFp64ToFloat 0) = .float 0 := by decide +kernel
  simp only [holFloatDiv, hx, hy, if_true]


-- Original complete symbolic state equation fdiv_d_negative_zero_zero_up
example : «dfn'FDIV_D» (3,1,2,3) (state 0x8000000000000000 0x0 0) =
    writeFPRD (3, holFloatToFp64 (holFloatSomeQnan
      (.fpDiv .roundTowardPositive (holFp64ToFloat 0x8000000000000000) (holFp64ToFloat 0)))) (state 0x8000000000000000 0x0 0) := by
  change writeFPRD (3, holFloatToFp64
    (holFloatDiv .roundTowardPositive (holFp64ToFloat 0x8000000000000000) (holFp64ToFloat 0)).2) (state 0x8000000000000000 0x0 0) = _
  have hx : holFloatValue (holFp64ToFloat 0x8000000000000000) = .float 0 := by decide +kernel
  have hy : holFloatValue (holFp64ToFloat 0) = .float 0 := by decide +kernel
  simp only [holFloatDiv, hx, hy, if_true]


-- Original fdiv_d_one_zero_rte
example : observe («dfn'FDIV_D» (3,1,2,0) (state 0x3ff0000000000000 0x0 0)) =
    (0x7FF0000000000000,0x3FF0000000000000,0,3,true,(some 0x7FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_d_one_pinf_rte
example : observe («dfn'FDIV_D» (3,1,2,0) (state 0x3ff0000000000000 0x7ff0000000000000 0)) =
    (0,0x3FF0000000000000,0x7FF0000000000000,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

-- Original fdiv_d_pinf_negative_one_rte
example : observe («dfn'FDIV_D» (3,1,2,0) (state 0x7ff0000000000000 0xbff0000000000000 0)) =
    (0xFFF0000000000000,0x7FF0000000000000,0xBFF0000000000000,3,true,(some 0xFFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FDIV_D», holFloatAdd, holFloatSub, holFloatMul, holFloatDiv,
    holFloatRoundWithFlags, holFloatRound_fp32, holFloatRound_fp64]
  decide +kernel

end Flapjack.Test.L3RiscvArithmeticParity

import Flapjack.RiscV.L3.Defs
import Flapjack.Misc.BinaryIeeeDirectedFp32
import Flapjack.Misc.BinaryIeeeDirectedFp64

/-! All144 original integer-to-FP state observations. Unobserved ARB fields
are instantiated by defaults. Numeric choice is rewritten using the complete
all-mode32/64 agreements; these are regression replays, not HOL real equivalence.
The rational representation assumption remains SOUNDNESS item8. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 2048
namespace Flapjack.Test.L3RiscvIntToFpParity
open Flapjack.RiscV.L3 Flapjack
private def state (a : BitVec 64) (frm : BitVec 3) : riscv_state :=
  { (default : riscv_state) with
    procID := 7
    c_gpr := fun _ r => if r = 1 then a else 99
    c_fpr := fun c _ => if c = 7 then 0xcafe000000000000 else 0xbbbb000000000000
    c_NextFetch := fun _ => none
    c_update := fun _ => { (default : StateDelta) with data1 := some 42 }
    c_UCSR := fun _ => { (default : UserCSR) with
      fpcsr := { (default : FPCSR) with NV := false, NX := true, FRM := frm } }
    c_MCSR := fun _ => { (default : MachineCSR) with
      mstatus := { (default : mstatus) with MFS := 0, MSD := false } } }
private def observe (s : riscv_state) :=
  (FPRD 3 s, GPR 1 s, (MCSR s).mstatus.MFS, (MCSR s).mstatus.MSD,
    (Delta s).data1, (fcsr s).NV, (fcsr s).NX, s.c_fpr 8 3,
    match NextFetch s with
    | some (.Trap t) => decide (t.trap = ExceptionType.Illegal_Instr ∧ t.badaddr = none)
    | _ => false)

-- Original fcvt_s_w_zero
example : observe («dfn'FCVT_S_W» (3,1,0) (state 0 0)) =
    (0xCAFE000000000000,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_W», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_wu_zero
example : observe («dfn'FCVT_S_WU» (3,1,0) (state 0 0)) =
    (0xCAFE000000000000,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_WU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_l_zero
example : observe («dfn'FCVT_S_L» (3,1,0) (state 0 0)) =
    (0xCAFE000000000000,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_L», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_lu_zero
example : observe («dfn'FCVT_S_LU» (3,1,0) (state 0 0)) =
    (0xCAFE000000000000,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_LU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_d_w_zero
example : observe («dfn'FCVT_D_W» (3,1,0) (state 0 0)) =
    (0,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_W», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_wu_zero
example : observe («dfn'FCVT_D_WU» (3,1,0) (state 0 0)) =
    (0,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_WU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_l_zero
example : observe («dfn'FCVT_D_L» (3,1,0) (state 0 0)) =
    (0,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_L», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_lu_zero
example : observe («dfn'FCVT_D_LU» (3,1,0) (state 0 0)) =
    (0,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_LU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_w_one
example : observe («dfn'FCVT_S_W» (3,1,0) (state 1 0)) =
    (0xCAFE00003F800000,1,3,true,(some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_W», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_wu_one
example : observe («dfn'FCVT_S_WU» (3,1,0) (state 1 0)) =
    (0xCAFE00003F800000,1,3,true,(some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_WU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_l_one
example : observe («dfn'FCVT_S_L» (3,1,0) (state 1 0)) =
    (0xCAFE00003F800000,1,3,true,(some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_L», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_lu_one
example : observe («dfn'FCVT_S_LU» (3,1,0) (state 1 0)) =
    (0xCAFE00003F800000,1,3,true,(some 0x3F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_LU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_d_w_one
example : observe («dfn'FCVT_D_W» (3,1,0) (state 1 0)) =
    (0x3FF0000000000000,1,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_W», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_wu_one
example : observe («dfn'FCVT_D_WU» (3,1,0) (state 1 0)) =
    (0x3FF0000000000000,1,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_WU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_l_one
example : observe («dfn'FCVT_D_L» (3,1,0) (state 1 0)) =
    (0x3FF0000000000000,1,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_L», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_lu_one
example : observe («dfn'FCVT_D_LU» (3,1,0) (state 1 0)) =
    (0x3FF0000000000000,1,3,true,(some 0x3FF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_LU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_w_negative_one
example : observe («dfn'FCVT_S_W» (3,1,0) (state 18446744073709551615 0)) =
    (0xCAFE0000BF800000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_W», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_wu_negative_one
example : observe («dfn'FCVT_S_WU» (3,1,0) (state 18446744073709551615 0)) =
    (0xCAFE00004F800000,0xFFFFFFFFFFFFFFFF,3,true,(some 0x4F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_WU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_l_negative_one
example : observe («dfn'FCVT_S_L» (3,1,0) (state 18446744073709551615 0)) =
    (0xCAFE0000BF800000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_L», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_lu_negative_one
example : observe («dfn'FCVT_S_LU» (3,1,0) (state 18446744073709551615 0)) =
    (0xCAFE00005F800000,0xFFFFFFFFFFFFFFFF,3,true,(some 0x5F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_LU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_d_w_negative_one
example : observe («dfn'FCVT_D_W» (3,1,0) (state 18446744073709551615 0)) =
    (0xBFF0000000000000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_W», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_wu_negative_one
example : observe («dfn'FCVT_D_WU» (3,1,0) (state 18446744073709551615 0)) =
    (0x41EFFFFFFFE00000,0xFFFFFFFFFFFFFFFF,3,true,(some 0x41EFFFFFFFE00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_WU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_l_negative_one
example : observe («dfn'FCVT_D_L» (3,1,0) (state 18446744073709551615 0)) =
    (0xBFF0000000000000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_L», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_lu_negative_one
example : observe («dfn'FCVT_D_LU» (3,1,0) (state 18446744073709551615 0)) =
    (0x43F0000000000000,0xFFFFFFFFFFFFFFFF,3,true,(some 0x43F0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_LU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_w_tie_even
example : observe («dfn'FCVT_S_W» (3,1,0) (state 16777217 0)) =
    (0xCAFE00004B800000,0x1000001,3,true,(some 0x4B800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_W», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_wu_tie_even
example : observe («dfn'FCVT_S_WU» (3,1,0) (state 16777217 0)) =
    (0xCAFE00004B800000,0x1000001,3,true,(some 0x4B800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_WU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_l_tie_even
example : observe («dfn'FCVT_S_L» (3,1,0) (state 16777217 0)) =
    (0xCAFE00004B800000,0x1000001,3,true,(some 0x4B800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_L», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_lu_tie_even
example : observe («dfn'FCVT_S_LU» (3,1,0) (state 16777217 0)) =
    (0xCAFE00004B800000,0x1000001,3,true,(some 0x4B800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_LU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_d_w_tie_even
example : observe («dfn'FCVT_D_W» (3,1,0) (state 16777217 0)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_W», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_wu_tie_even
example : observe («dfn'FCVT_D_WU» (3,1,0) (state 16777217 0)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_WU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_l_tie_even
example : observe («dfn'FCVT_D_L» (3,1,0) (state 16777217 0)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_L», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_lu_tie_even
example : observe («dfn'FCVT_D_LU» (3,1,0) (state 16777217 0)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_LU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_w_tie_zero
example : observe («dfn'FCVT_S_W» (3,1,1) (state 16777217 0)) =
    (0xCAFE00004B800000,0x1000001,3,true,(some 0x4B800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_W», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_wu_tie_zero
example : observe («dfn'FCVT_S_WU» (3,1,1) (state 16777217 0)) =
    (0xCAFE00004B800000,0x1000001,3,true,(some 0x4B800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_WU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_l_tie_zero
example : observe («dfn'FCVT_S_L» (3,1,1) (state 16777217 0)) =
    (0xCAFE00004B800000,0x1000001,3,true,(some 0x4B800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_L», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_lu_tie_zero
example : observe («dfn'FCVT_S_LU» (3,1,1) (state 16777217 0)) =
    (0xCAFE00004B800000,0x1000001,3,true,(some 0x4B800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_LU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_d_w_tie_zero
example : observe («dfn'FCVT_D_W» (3,1,1) (state 16777217 0)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_W», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_wu_tie_zero
example : observe («dfn'FCVT_D_WU» (3,1,1) (state 16777217 0)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_WU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_l_tie_zero
example : observe («dfn'FCVT_D_L» (3,1,1) (state 16777217 0)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_L», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_lu_tie_zero
example : observe («dfn'FCVT_D_LU» (3,1,1) (state 16777217 0)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_LU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_w_tie_down
example : observe («dfn'FCVT_S_W» (3,1,2) (state 16777217 0)) =
    (0xCAFE00004B800000,0x1000001,3,true,(some 0x4B800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_W», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_wu_tie_down
example : observe («dfn'FCVT_S_WU» (3,1,2) (state 16777217 0)) =
    (0xCAFE00004B800000,0x1000001,3,true,(some 0x4B800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_WU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_l_tie_down
example : observe («dfn'FCVT_S_L» (3,1,2) (state 16777217 0)) =
    (0xCAFE00004B800000,0x1000001,3,true,(some 0x4B800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_L», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_lu_tie_down
example : observe («dfn'FCVT_S_LU» (3,1,2) (state 16777217 0)) =
    (0xCAFE00004B800000,0x1000001,3,true,(some 0x4B800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_LU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_d_w_tie_down
example : observe («dfn'FCVT_D_W» (3,1,2) (state 16777217 0)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_W», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_wu_tie_down
example : observe («dfn'FCVT_D_WU» (3,1,2) (state 16777217 0)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_WU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_l_tie_down
example : observe («dfn'FCVT_D_L» (3,1,2) (state 16777217 0)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_L», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_lu_tie_down
example : observe («dfn'FCVT_D_LU» (3,1,2) (state 16777217 0)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_LU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_w_tie_up
example : observe («dfn'FCVT_S_W» (3,1,3) (state 16777217 0)) =
    (0xCAFE00004B800001,0x1000001,3,true,(some 0x4B800001),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_W», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_wu_tie_up
example : observe («dfn'FCVT_S_WU» (3,1,3) (state 16777217 0)) =
    (0xCAFE00004B800001,0x1000001,3,true,(some 0x4B800001),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_WU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_l_tie_up
example : observe («dfn'FCVT_S_L» (3,1,3) (state 16777217 0)) =
    (0xCAFE00004B800001,0x1000001,3,true,(some 0x4B800001),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_L», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_lu_tie_up
example : observe («dfn'FCVT_S_LU» (3,1,3) (state 16777217 0)) =
    (0xCAFE00004B800001,0x1000001,3,true,(some 0x4B800001),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_LU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_d_w_tie_up
example : observe («dfn'FCVT_D_W» (3,1,3) (state 16777217 0)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_W», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_wu_tie_up
example : observe («dfn'FCVT_D_WU» (3,1,3) (state 16777217 0)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_WU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_l_tie_up
example : observe («dfn'FCVT_D_L» (3,1,3) (state 16777217 0)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_L», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_lu_tie_up
example : observe («dfn'FCVT_D_LU» (3,1,3) (state 16777217 0)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_LU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_w_negative_tie
example : observe («dfn'FCVT_S_W» (3,1,0) (state 18446744073692774399 0)) =
    (0xCAFE0000CB800000,0xFFFFFFFFFEFFFFFF,3,true,(some 0xCB800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_W», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_wu_negative_tie
example : observe («dfn'FCVT_S_WU» (3,1,0) (state 18446744073692774399 0)) =
    (0xCAFE00004F7F0000,0xFFFFFFFFFEFFFFFF,3,true,(some 0x4F7F0000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_WU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_l_negative_tie
example : observe («dfn'FCVT_S_L» (3,1,0) (state 18446744073692774399 0)) =
    (0xCAFE0000CB800000,0xFFFFFFFFFEFFFFFF,3,true,(some 0xCB800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_L», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_lu_negative_tie
example : observe («dfn'FCVT_S_LU» (3,1,0) (state 18446744073692774399 0)) =
    (0xCAFE00005F800000,0xFFFFFFFFFEFFFFFF,3,true,(some 0x5F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_LU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_d_w_negative_tie
example : observe («dfn'FCVT_D_W» (3,1,0) (state 18446744073692774399 0)) =
    (0xC170000010000000,0xFFFFFFFFFEFFFFFF,3,true,(some 0xC170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_W», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_wu_negative_tie
example : observe («dfn'FCVT_D_WU» (3,1,0) (state 18446744073692774399 0)) =
    (0x41EFDFFFFFE00000,0xFFFFFFFFFEFFFFFF,3,true,(some 0x41EFDFFFFFE00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_WU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_l_negative_tie
example : observe («dfn'FCVT_D_L» (3,1,0) (state 18446744073692774399 0)) =
    (0xC170000010000000,0xFFFFFFFFFEFFFFFF,3,true,(some 0xC170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_L», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_lu_negative_tie
example : observe («dfn'FCVT_D_LU» (3,1,0) (state 18446744073692774399 0)) =
    (0x43EFFFFFFFFFE000,0xFFFFFFFFFEFFFFFF,3,true,(some 0x43EFFFFFFFFFE000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_LU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_w_negative_down
example : observe («dfn'FCVT_S_W» (3,1,2) (state 18446744073692774399 0)) =
    (0xCAFE0000CB800001,0xFFFFFFFFFEFFFFFF,3,true,(some 0xCB800001),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_W», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_wu_negative_down
example : observe («dfn'FCVT_S_WU» (3,1,2) (state 18446744073692774399 0)) =
    (0xCAFE00004F7EFFFF,0xFFFFFFFFFEFFFFFF,3,true,(some 0x4F7EFFFF),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_WU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_l_negative_down
example : observe («dfn'FCVT_S_L» (3,1,2) (state 18446744073692774399 0)) =
    (0xCAFE0000CB800001,0xFFFFFFFFFEFFFFFF,3,true,(some 0xCB800001),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_L», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_lu_negative_down
example : observe («dfn'FCVT_S_LU» (3,1,2) (state 18446744073692774399 0)) =
    (0xCAFE00005F7FFFFF,0xFFFFFFFFFEFFFFFF,3,true,(some 0x5F7FFFFF),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_LU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_d_w_negative_down
example : observe («dfn'FCVT_D_W» (3,1,2) (state 18446744073692774399 0)) =
    (0xC170000010000000,0xFFFFFFFFFEFFFFFF,3,true,(some 0xC170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_W», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_wu_negative_down
example : observe («dfn'FCVT_D_WU» (3,1,2) (state 18446744073692774399 0)) =
    (0x41EFDFFFFFE00000,0xFFFFFFFFFEFFFFFF,3,true,(some 0x41EFDFFFFFE00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_WU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_l_negative_down
example : observe («dfn'FCVT_D_L» (3,1,2) (state 18446744073692774399 0)) =
    (0xC170000010000000,0xFFFFFFFFFEFFFFFF,3,true,(some 0xC170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_L», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_lu_negative_down
example : observe («dfn'FCVT_D_LU» (3,1,2) (state 18446744073692774399 0)) =
    (0x43EFFFFFFFFFDFFF,0xFFFFFFFFFEFFFFFF,3,true,(some 0x43EFFFFFFFFFDFFF),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_LU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_w_negative_up
example : observe («dfn'FCVT_S_W» (3,1,3) (state 18446744073692774399 0)) =
    (0xCAFE0000CB800000,0xFFFFFFFFFEFFFFFF,3,true,(some 0xCB800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_W», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_wu_negative_up
example : observe («dfn'FCVT_S_WU» (3,1,3) (state 18446744073692774399 0)) =
    (0xCAFE00004F7F0000,0xFFFFFFFFFEFFFFFF,3,true,(some 0x4F7F0000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_WU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_l_negative_up
example : observe («dfn'FCVT_S_L» (3,1,3) (state 18446744073692774399 0)) =
    (0xCAFE0000CB800000,0xFFFFFFFFFEFFFFFF,3,true,(some 0xCB800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_L», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_lu_negative_up
example : observe («dfn'FCVT_S_LU» (3,1,3) (state 18446744073692774399 0)) =
    (0xCAFE00005F800000,0xFFFFFFFFFEFFFFFF,3,true,(some 0x5F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_LU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_d_w_negative_up
example : observe («dfn'FCVT_D_W» (3,1,3) (state 18446744073692774399 0)) =
    (0xC170000010000000,0xFFFFFFFFFEFFFFFF,3,true,(some 0xC170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_W», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_wu_negative_up
example : observe («dfn'FCVT_D_WU» (3,1,3) (state 18446744073692774399 0)) =
    (0x41EFDFFFFFE00000,0xFFFFFFFFFEFFFFFF,3,true,(some 0x41EFDFFFFFE00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_WU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_l_negative_up
example : observe («dfn'FCVT_D_L» (3,1,3) (state 18446744073692774399 0)) =
    (0xC170000010000000,0xFFFFFFFFFEFFFFFF,3,true,(some 0xC170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_L», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_lu_negative_up
example : observe («dfn'FCVT_D_LU» (3,1,3) (state 18446744073692774399 0)) =
    (0x43EFFFFFFFFFE000,0xFFFFFFFFFEFFFFFF,3,true,(some 0x43EFFFFFFFFFE000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_LU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_w_large_even
example : observe («dfn'FCVT_S_W» (3,1,0) (state 18446744073709551615 0)) =
    (0xCAFE0000BF800000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_W», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_wu_large_even
example : observe («dfn'FCVT_S_WU» (3,1,0) (state 18446744073709551615 0)) =
    (0xCAFE00004F800000,0xFFFFFFFFFFFFFFFF,3,true,(some 0x4F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_WU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_l_large_even
example : observe («dfn'FCVT_S_L» (3,1,0) (state 18446744073709551615 0)) =
    (0xCAFE0000BF800000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_L», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_lu_large_even
example : observe («dfn'FCVT_S_LU» (3,1,0) (state 18446744073709551615 0)) =
    (0xCAFE00005F800000,0xFFFFFFFFFFFFFFFF,3,true,(some 0x5F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_LU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_d_w_large_even
example : observe («dfn'FCVT_D_W» (3,1,0) (state 18446744073709551615 0)) =
    (0xBFF0000000000000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_W», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_wu_large_even
example : observe («dfn'FCVT_D_WU» (3,1,0) (state 18446744073709551615 0)) =
    (0x41EFFFFFFFE00000,0xFFFFFFFFFFFFFFFF,3,true,(some 0x41EFFFFFFFE00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_WU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_l_large_even
example : observe («dfn'FCVT_D_L» (3,1,0) (state 18446744073709551615 0)) =
    (0xBFF0000000000000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_L», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_lu_large_even
example : observe («dfn'FCVT_D_LU» (3,1,0) (state 18446744073709551615 0)) =
    (0x43F0000000000000,0xFFFFFFFFFFFFFFFF,3,true,(some 0x43F0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_LU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_w_large_zero
example : observe («dfn'FCVT_S_W» (3,1,1) (state 18446744073709551615 0)) =
    (0xCAFE0000BF800000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_W», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_wu_large_zero
example : observe («dfn'FCVT_S_WU» (3,1,1) (state 18446744073709551615 0)) =
    (0xCAFE00004F7FFFFF,0xFFFFFFFFFFFFFFFF,3,true,(some 0x4F7FFFFF),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_WU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_l_large_zero
example : observe («dfn'FCVT_S_L» (3,1,1) (state 18446744073709551615 0)) =
    (0xCAFE0000BF800000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_L», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_lu_large_zero
example : observe («dfn'FCVT_S_LU» (3,1,1) (state 18446744073709551615 0)) =
    (0xCAFE00005F7FFFFF,0xFFFFFFFFFFFFFFFF,3,true,(some 0x5F7FFFFF),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_LU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_d_w_large_zero
example : observe («dfn'FCVT_D_W» (3,1,1) (state 18446744073709551615 0)) =
    (0xBFF0000000000000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_W», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_wu_large_zero
example : observe («dfn'FCVT_D_WU» (3,1,1) (state 18446744073709551615 0)) =
    (0x41EFFFFFFFE00000,0xFFFFFFFFFFFFFFFF,3,true,(some 0x41EFFFFFFFE00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_WU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_l_large_zero
example : observe («dfn'FCVT_D_L» (3,1,1) (state 18446744073709551615 0)) =
    (0xBFF0000000000000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_L», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_lu_large_zero
example : observe («dfn'FCVT_D_LU» (3,1,1) (state 18446744073709551615 0)) =
    (0x43EFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF,3,true,(some 0x43EFFFFFFFFFFFFF),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_LU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_w_large_down
example : observe («dfn'FCVT_S_W» (3,1,2) (state 18446744073709551615 0)) =
    (0xCAFE0000BF800000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_W», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_wu_large_down
example : observe («dfn'FCVT_S_WU» (3,1,2) (state 18446744073709551615 0)) =
    (0xCAFE00004F7FFFFF,0xFFFFFFFFFFFFFFFF,3,true,(some 0x4F7FFFFF),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_WU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_l_large_down
example : observe («dfn'FCVT_S_L» (3,1,2) (state 18446744073709551615 0)) =
    (0xCAFE0000BF800000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_L», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_lu_large_down
example : observe («dfn'FCVT_S_LU» (3,1,2) (state 18446744073709551615 0)) =
    (0xCAFE00005F7FFFFF,0xFFFFFFFFFFFFFFFF,3,true,(some 0x5F7FFFFF),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_LU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_d_w_large_down
example : observe («dfn'FCVT_D_W» (3,1,2) (state 18446744073709551615 0)) =
    (0xBFF0000000000000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_W», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_wu_large_down
example : observe («dfn'FCVT_D_WU» (3,1,2) (state 18446744073709551615 0)) =
    (0x41EFFFFFFFE00000,0xFFFFFFFFFFFFFFFF,3,true,(some 0x41EFFFFFFFE00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_WU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_l_large_down
example : observe («dfn'FCVT_D_L» (3,1,2) (state 18446744073709551615 0)) =
    (0xBFF0000000000000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_L», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_lu_large_down
example : observe («dfn'FCVT_D_LU» (3,1,2) (state 18446744073709551615 0)) =
    (0x43EFFFFFFFFFFFFF,0xFFFFFFFFFFFFFFFF,3,true,(some 0x43EFFFFFFFFFFFFF),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_LU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_w_large_up
example : observe («dfn'FCVT_S_W» (3,1,3) (state 18446744073709551615 0)) =
    (0xCAFE0000BF800000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_W», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_wu_large_up
example : observe («dfn'FCVT_S_WU» (3,1,3) (state 18446744073709551615 0)) =
    (0xCAFE00004F800000,0xFFFFFFFFFFFFFFFF,3,true,(some 0x4F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_WU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_l_large_up
example : observe («dfn'FCVT_S_L» (3,1,3) (state 18446744073709551615 0)) =
    (0xCAFE0000BF800000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBF800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_L», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_lu_large_up
example : observe («dfn'FCVT_S_LU» (3,1,3) (state 18446744073709551615 0)) =
    (0xCAFE00005F800000,0xFFFFFFFFFFFFFFFF,3,true,(some 0x5F800000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_LU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_d_w_large_up
example : observe («dfn'FCVT_D_W» (3,1,3) (state 18446744073709551615 0)) =
    (0xBFF0000000000000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_W», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_wu_large_up
example : observe («dfn'FCVT_D_WU» (3,1,3) (state 18446744073709551615 0)) =
    (0x41EFFFFFFFE00000,0xFFFFFFFFFFFFFFFF,3,true,(some 0x41EFFFFFFFE00000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_WU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_l_large_up
example : observe («dfn'FCVT_D_L» (3,1,3) (state 18446744073709551615 0)) =
    (0xBFF0000000000000,0xFFFFFFFFFFFFFFFF,3,true,(some 0xBFF0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_L», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_lu_large_up
example : observe («dfn'FCVT_D_LU» (3,1,3) (state 18446744073709551615 0)) =
    (0x43F0000000000000,0xFFFFFFFFFFFFFFFF,3,true,(some 0x43F0000000000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_LU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_w_zero_up
example : observe («dfn'FCVT_S_W» (3,1,3) (state 0 0)) =
    (0xCAFE000000000000,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_W», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_wu_zero_up
example : observe («dfn'FCVT_S_WU» (3,1,3) (state 0 0)) =
    (0xCAFE000000000000,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_WU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_l_zero_up
example : observe («dfn'FCVT_S_L» (3,1,3) (state 0 0)) =
    (0xCAFE000000000000,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_L», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_lu_zero_up
example : observe («dfn'FCVT_S_LU» (3,1,3) (state 0 0)) =
    (0xCAFE000000000000,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_LU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_d_w_zero_up
example : observe («dfn'FCVT_D_W» (3,1,3) (state 0 0)) =
    (0,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_W», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_wu_zero_up
example : observe («dfn'FCVT_D_WU» (3,1,3) (state 0 0)) =
    (0,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_WU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_l_zero_up
example : observe («dfn'FCVT_D_L» (3,1,3) (state 0 0)) =
    (0,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_L», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_lu_zero_up
example : observe («dfn'FCVT_D_LU» (3,1,3) (state 0 0)) =
    (0,0,3,true,(some 0),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_LU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_w_dynamic_up
example : observe («dfn'FCVT_S_W» (3,1,7) (state 16777217 3)) =
    (0xCAFE00004B800001,0x1000001,3,true,(some 0x4B800001),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_W», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_wu_dynamic_up
example : observe («dfn'FCVT_S_WU» (3,1,7) (state 16777217 3)) =
    (0xCAFE00004B800001,0x1000001,3,true,(some 0x4B800001),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_WU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_l_dynamic_up
example : observe («dfn'FCVT_S_L» (3,1,7) (state 16777217 3)) =
    (0xCAFE00004B800001,0x1000001,3,true,(some 0x4B800001),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_L», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_lu_dynamic_up
example : observe («dfn'FCVT_S_LU» (3,1,7) (state 16777217 3)) =
    (0xCAFE00004B800001,0x1000001,3,true,(some 0x4B800001),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_S_LU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_d_w_dynamic_up
example : observe («dfn'FCVT_D_W» (3,1,7) (state 16777217 3)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_W», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_wu_dynamic_up
example : observe («dfn'FCVT_D_WU» (3,1,7) (state 16777217 3)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_WU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_l_dynamic_up
example : observe («dfn'FCVT_D_L» (3,1,7) (state 16777217 3)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_L», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_lu_dynamic_up
example : observe («dfn'FCVT_D_LU» (3,1,7) (state 16777217 3)) =
    (0x4170000010000000,0x1000001,3,true,(some 0x4170000010000000),false,true,0xBBBB000000000000,false) := by
  simp only [«dfn'FCVT_D_LU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_w_illegal
example : observe («dfn'FCVT_S_W» (3,1,4) (state 1 0)) =
    (0xCAFE000000000000,1,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_S_W», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_wu_illegal
example : observe («dfn'FCVT_S_WU» (3,1,4) (state 1 0)) =
    (0xCAFE000000000000,1,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_S_WU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_l_illegal
example : observe («dfn'FCVT_S_L» (3,1,4) (state 1 0)) =
    (0xCAFE000000000000,1,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_S_L», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_lu_illegal
example : observe («dfn'FCVT_S_LU» (3,1,4) (state 1 0)) =
    (0xCAFE000000000000,1,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_S_LU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_d_w_illegal
example : observe («dfn'FCVT_D_W» (3,1,4) (state 1 0)) =
    (0xCAFE000000000000,1,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_D_W», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_wu_illegal
example : observe («dfn'FCVT_D_WU» (3,1,4) (state 1 0)) =
    (0xCAFE000000000000,1,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_D_WU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_l_illegal
example : observe («dfn'FCVT_D_L» (3,1,4) (state 1 0)) =
    (0xCAFE000000000000,1,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_D_L», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_lu_illegal
example : observe («dfn'FCVT_D_LU» (3,1,4) (state 1 0)) =
    (0xCAFE000000000000,1,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_D_LU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_s_w_dynamic_illegal
example : observe («dfn'FCVT_S_W» (3,1,7) (state 1 4)) =
    (0xCAFE000000000000,1,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_S_W», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_wu_dynamic_illegal
example : observe («dfn'FCVT_S_WU» (3,1,7) (state 1 4)) =
    (0xCAFE000000000000,1,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_S_WU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_l_dynamic_illegal
example : observe («dfn'FCVT_S_L» (3,1,7) (state 1 4)) =
    (0xCAFE000000000000,1,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_S_L», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_s_lu_dynamic_illegal
example : observe («dfn'FCVT_S_LU» (3,1,7) (state 1 4)) =
    (0xCAFE000000000000,1,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_S_LU», holRealToFloat, holFloatRound_fp32]
  decide +kernel

-- Original fcvt_d_w_dynamic_illegal
example : observe («dfn'FCVT_D_W» (3,1,7) (state 1 4)) =
    (0xCAFE000000000000,1,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_D_W», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_wu_dynamic_illegal
example : observe («dfn'FCVT_D_WU» (3,1,7) (state 1 4)) =
    (0xCAFE000000000000,1,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_D_WU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_l_dynamic_illegal
example : observe («dfn'FCVT_D_L» (3,1,7) (state 1 4)) =
    (0xCAFE000000000000,1,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_D_L», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

-- Original fcvt_d_lu_dynamic_illegal
example : observe («dfn'FCVT_D_LU» (3,1,7) (state 1 4)) =
    (0xCAFE000000000000,1,0,false,(some 42),false,true,0xBBBB000000000000,true) := by
  simp only [«dfn'FCVT_D_LU», holIntToFp64, holRealToFp64, holRealToFloat, holFloatRound_fp64]
  decide +kernel

end Flapjack.Test.L3RiscvIntToFpParity

import Flapjack.RiscV.L3.Defs

/-! Native kernel replays of full original L3 float-to-integer conversions.
The fixed-width inputs, GPR destination, preserved source FP register/NV and
Illegal_Instr trap observation match the original HOL fixture. These are
regression observations; the IEEE rational representation assumption and full
model correspondence obligations remain explicit in the source manifest. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
namespace Flapjack.Test.L3RiscvFpToIntParity
open Flapjack.RiscV.L3 Flapjack
private def state (a : BitVec 64) (frm : BitVec 3) : riscv_state :=
  { (default : riscv_state) with
    procID := 0
    c_gpr := fun _ r => if r = 3 then 99 else 0
    c_fpr := fun _ r => if r = 1 then a else 0
    c_NextFetch := fun _ => none
    c_UCSR := fun _ => { (default : UserCSR) with
      fpcsr := { (default : FPCSR) with NV := false, FRM := frm } }
    c_MCSR := fun _ => { (default : MachineCSR) with mstatus := default } }
private def observe (s : riscv_state) : BitVec 64 × BitVec 64 × Bool × Bool :=
  (GPR 3 s, FPRD 1 s, (fcsr s).NV,
    match NextFetch s with
    | some (.Trap t) => decide (t.trap = .Illegal_Instr ∧ t.badaddr = none)
    | _ => false)

-- Original fcvt_w_s_tie_even
example : observe («dfn'FCVT_W_S» (3,1,0) (state 0x40200000 0)) =
    (2, 0x40200000, false, false) := by decide +kernel

-- Original fcvt_wu_s_tie_even
example : observe («dfn'FCVT_WU_S» (3,1,0) (state 0x40200000 0)) =
    (2, 0x40200000, false, false) := by decide +kernel

-- Original fcvt_l_s_tie_even
example : observe («dfn'FCVT_L_S» (3,1,0) (state 0x40200000 0)) =
    (2, 0x40200000, false, false) := by decide +kernel

-- Original fcvt_lu_s_tie_even
example : observe («dfn'FCVT_LU_S» (3,1,0) (state 0x40200000 0)) =
    (2, 0x40200000, false, false) := by decide +kernel

-- Original fcvt_w_s_tie_odd
example : observe («dfn'FCVT_W_S» (3,1,0) (state 0x40600000 0)) =
    (4, 0x40600000, false, false) := by decide +kernel

-- Original fcvt_wu_s_tie_odd
example : observe («dfn'FCVT_WU_S» (3,1,0) (state 0x40600000 0)) =
    (4, 0x40600000, false, false) := by decide +kernel

-- Original fcvt_l_s_tie_odd
example : observe («dfn'FCVT_L_S» (3,1,0) (state 0x40600000 0)) =
    (4, 0x40600000, false, false) := by decide +kernel

-- Original fcvt_lu_s_tie_odd
example : observe («dfn'FCVT_LU_S» (3,1,0) (state 0x40600000 0)) =
    (4, 0x40600000, false, false) := by decide +kernel

-- Original fcvt_w_s_negative_zero
example : observe («dfn'FCVT_W_S» (3,1,1) (state 0xc0200000 0)) =
    (0xFFFFFFFFFFFFFFFE, 0xC0200000, false, false) := by decide +kernel

-- Original fcvt_wu_s_negative_zero
example : observe («dfn'FCVT_WU_S» (3,1,1) (state 0xc0200000 0)) =
    (0, 0xC0200000, false, false) := by decide +kernel

-- Original fcvt_l_s_negative_zero
example : observe («dfn'FCVT_L_S» (3,1,1) (state 0xc0200000 0)) =
    (0xFFFFFFFFFFFFFFFE, 0xC0200000, false, false) := by decide +kernel

-- Original fcvt_lu_s_negative_zero
example : observe («dfn'FCVT_LU_S» (3,1,1) (state 0xc0200000 0)) =
    (0, 0xC0200000, false, false) := by decide +kernel

-- Original fcvt_w_s_negative_floor
example : observe («dfn'FCVT_W_S» (3,1,2) (state 0xc0200000 0)) =
    (0xFFFFFFFFFFFFFFFD, 0xC0200000, false, false) := by decide +kernel

-- Original fcvt_wu_s_negative_floor
example : observe («dfn'FCVT_WU_S» (3,1,2) (state 0xc0200000 0)) =
    (0, 0xC0200000, false, false) := by decide +kernel

-- Original fcvt_l_s_negative_floor
example : observe («dfn'FCVT_L_S» (3,1,2) (state 0xc0200000 0)) =
    (0xFFFFFFFFFFFFFFFD, 0xC0200000, false, false) := by decide +kernel

-- Original fcvt_lu_s_negative_floor
example : observe («dfn'FCVT_LU_S» (3,1,2) (state 0xc0200000 0)) =
    (0, 0xC0200000, false, false) := by decide +kernel

-- Original fcvt_w_s_negative_ceil
example : observe («dfn'FCVT_W_S» (3,1,3) (state 0xc0200000 0)) =
    (0xFFFFFFFFFFFFFFFE, 0xC0200000, false, false) := by decide +kernel

-- Original fcvt_wu_s_negative_ceil
example : observe («dfn'FCVT_WU_S» (3,1,3) (state 0xc0200000 0)) =
    (0, 0xC0200000, false, false) := by decide +kernel

-- Original fcvt_l_s_negative_ceil
example : observe («dfn'FCVT_L_S» (3,1,3) (state 0xc0200000 0)) =
    (0xFFFFFFFFFFFFFFFE, 0xC0200000, false, false) := by decide +kernel

-- Original fcvt_lu_s_negative_ceil
example : observe («dfn'FCVT_LU_S» (3,1,3) (state 0xc0200000 0)) =
    (0, 0xC0200000, false, false) := by decide +kernel

-- Original fcvt_w_s_qnan
example : observe («dfn'FCVT_W_S» (3,1,0) (state 0x7fc00000 0)) =
    (0x7FFFFFFF, 0x7FC00000, false, false) := by decide +kernel

-- Original fcvt_wu_s_qnan
example : observe («dfn'FCVT_WU_S» (3,1,0) (state 0x7fc00000 0)) =
    (0xFFFFFFFF, 0x7FC00000, false, false) := by decide +kernel

-- Original fcvt_l_s_qnan
example : observe («dfn'FCVT_L_S» (3,1,0) (state 0x7fc00000 0)) =
    (0x7FFFFFFFFFFFFFFF, 0x7FC00000, false, false) := by decide +kernel

-- Original fcvt_lu_s_qnan
example : observe («dfn'FCVT_LU_S» (3,1,0) (state 0x7fc00000 0)) =
    (0xFFFFFFFFFFFFFFFF, 0x7FC00000, false, false) := by decide +kernel

-- Original fcvt_w_s_posinf
example : observe («dfn'FCVT_W_S» (3,1,0) (state 0x7f800000 0)) =
    (0x7FFFFFFF, 0x7F800000, false, false) := by decide +kernel

-- Original fcvt_wu_s_posinf
example : observe («dfn'FCVT_WU_S» (3,1,0) (state 0x7f800000 0)) =
    (0xFFFFFFFF, 0x7F800000, false, false) := by decide +kernel

-- Original fcvt_l_s_posinf
example : observe («dfn'FCVT_L_S» (3,1,0) (state 0x7f800000 0)) =
    (0x7FFFFFFFFFFFFFFF, 0x7F800000, false, false) := by decide +kernel

-- Original fcvt_lu_s_posinf
example : observe («dfn'FCVT_LU_S» (3,1,0) (state 0x7f800000 0)) =
    (0xFFFFFFFFFFFFFFFF, 0x7F800000, false, false) := by decide +kernel

-- Original fcvt_w_s_neginf
example : observe («dfn'FCVT_W_S» (3,1,0) (state 0xff800000 0)) =
    (0xFFFFFFFF80000000, 0xFF800000, false, false) := by decide +kernel

-- Original fcvt_wu_s_neginf
example : observe («dfn'FCVT_WU_S» (3,1,0) (state 0xff800000 0)) =
    (0, 0xFF800000, false, false) := by decide +kernel

-- Original fcvt_l_s_neginf
example : observe («dfn'FCVT_L_S» (3,1,0) (state 0xff800000 0)) =
    (0x8000000000000000, 0xFF800000, false, false) := by decide +kernel

-- Original fcvt_lu_s_neginf
example : observe («dfn'FCVT_LU_S» (3,1,0) (state 0xff800000 0)) =
    (0, 0xFF800000, false, false) := by decide +kernel

-- Original fcvt_w_s_overflow
example : observe («dfn'FCVT_W_S» (3,1,0) (state 0x5f800000 0)) =
    (0x7FFFFFFF, 0x5F800000, false, false) := by decide +kernel

-- Original fcvt_wu_s_overflow
example : observe («dfn'FCVT_WU_S» (3,1,0) (state 0x5f800000 0)) =
    (0xFFFFFFFF, 0x5F800000, false, false) := by decide +kernel

-- Original fcvt_l_s_overflow
example : observe («dfn'FCVT_L_S» (3,1,0) (state 0x5f800000 0)) =
    (0x7FFFFFFFFFFFFFFF, 0x5F800000, false, false) := by decide +kernel

-- Original fcvt_lu_s_overflow
example : observe («dfn'FCVT_LU_S» (3,1,0) (state 0x5f800000 0)) =
    (0xFFFFFFFFFFFFFFFF, 0x5F800000, false, false) := by decide +kernel

-- Original fcvt_w_s_negative_range
example : observe («dfn'FCVT_W_S» (3,1,0) (state 0xdf800000 0)) =
    (0xFFFFFFFF80000000, 0xDF800000, false, false) := by decide +kernel

-- Original fcvt_wu_s_negative_range
example : observe («dfn'FCVT_WU_S» (3,1,0) (state 0xdf800000 0)) =
    (0, 0xDF800000, false, false) := by decide +kernel

-- Original fcvt_l_s_negative_range
example : observe («dfn'FCVT_L_S» (3,1,0) (state 0xdf800000 0)) =
    (0x8000000000000000, 0xDF800000, false, false) := by decide +kernel

-- Original fcvt_lu_s_negative_range
example : observe («dfn'FCVT_LU_S» (3,1,0) (state 0xdf800000 0)) =
    (0, 0xDF800000, false, false) := by decide +kernel

-- Original fcvt_w_s_dynamic_ceil
example : observe («dfn'FCVT_W_S» (3,1,7) (state 0x40200000 3)) =
    (3, 0x40200000, false, false) := by decide +kernel

-- Original fcvt_wu_s_dynamic_ceil
example : observe («dfn'FCVT_WU_S» (3,1,7) (state 0x40200000 3)) =
    (3, 0x40200000, false, false) := by decide +kernel

-- Original fcvt_l_s_dynamic_ceil
example : observe («dfn'FCVT_L_S» (3,1,7) (state 0x40200000 3)) =
    (3, 0x40200000, false, false) := by decide +kernel

-- Original fcvt_lu_s_dynamic_ceil
example : observe («dfn'FCVT_LU_S» (3,1,7) (state 0x40200000 3)) =
    (3, 0x40200000, false, false) := by decide +kernel

-- Original fcvt_w_s_invalid
example : observe («dfn'FCVT_W_S» (3,1,4) (state 0x3f800000 0)) =
    (99, 0x3F800000, false, true) := by decide +kernel

-- Original fcvt_wu_s_invalid
example : observe («dfn'FCVT_WU_S» (3,1,4) (state 0x3f800000 0)) =
    (99, 0x3F800000, false, true) := by decide +kernel

-- Original fcvt_l_s_invalid
example : observe («dfn'FCVT_L_S» (3,1,4) (state 0x3f800000 0)) =
    (99, 0x3F800000, false, true) := by decide +kernel

-- Original fcvt_lu_s_invalid
example : observe («dfn'FCVT_LU_S» (3,1,4) (state 0x3f800000 0)) =
    (99, 0x3F800000, false, true) := by decide +kernel

-- Original fcvt_w_d_tie_even
example : observe («dfn'FCVT_W_D» (3,1,0) (state 0x4004000000000000 0)) =
    (2, 0x4004000000000000, false, false) := by decide +kernel

-- Original fcvt_wu_d_tie_even
example : observe («dfn'FCVT_WU_D» (3,1,0) (state 0x4004000000000000 0)) =
    (2, 0x4004000000000000, false, false) := by decide +kernel

-- Original fcvt_l_d_tie_even
example : observe («dfn'FCVT_L_D» (3,1,0) (state 0x4004000000000000 0)) =
    (2, 0x4004000000000000, false, false) := by decide +kernel

-- Original fcvt_lu_d_tie_even
example : observe («dfn'FCVT_LU_D» (3,1,0) (state 0x4004000000000000 0)) =
    (2, 0x4004000000000000, false, false) := by decide +kernel

-- Original fcvt_w_d_tie_odd
example : observe («dfn'FCVT_W_D» (3,1,0) (state 0x400c000000000000 0)) =
    (4, 0x400C000000000000, false, false) := by decide +kernel

-- Original fcvt_wu_d_tie_odd
example : observe («dfn'FCVT_WU_D» (3,1,0) (state 0x400c000000000000 0)) =
    (4, 0x400C000000000000, false, false) := by decide +kernel

-- Original fcvt_l_d_tie_odd
example : observe («dfn'FCVT_L_D» (3,1,0) (state 0x400c000000000000 0)) =
    (4, 0x400C000000000000, false, false) := by decide +kernel

-- Original fcvt_lu_d_tie_odd
example : observe («dfn'FCVT_LU_D» (3,1,0) (state 0x400c000000000000 0)) =
    (4, 0x400C000000000000, false, false) := by decide +kernel

-- Original fcvt_w_d_negative_zero
example : observe («dfn'FCVT_W_D» (3,1,1) (state 0xc004000000000000 0)) =
    (0xFFFFFFFFFFFFFFFE, 0xC004000000000000, false, false) := by decide +kernel

-- Original fcvt_wu_d_negative_zero
example : observe («dfn'FCVT_WU_D» (3,1,1) (state 0xc004000000000000 0)) =
    (0, 0xC004000000000000, false, false) := by decide +kernel

-- Original fcvt_l_d_negative_zero
example : observe («dfn'FCVT_L_D» (3,1,1) (state 0xc004000000000000 0)) =
    (0xFFFFFFFFFFFFFFFE, 0xC004000000000000, false, false) := by decide +kernel

-- Original fcvt_lu_d_negative_zero
example : observe («dfn'FCVT_LU_D» (3,1,1) (state 0xc004000000000000 0)) =
    (0, 0xC004000000000000, false, false) := by decide +kernel

-- Original fcvt_w_d_negative_floor
example : observe («dfn'FCVT_W_D» (3,1,2) (state 0xc004000000000000 0)) =
    (0xFFFFFFFFFFFFFFFD, 0xC004000000000000, false, false) := by decide +kernel

-- Original fcvt_wu_d_negative_floor
example : observe («dfn'FCVT_WU_D» (3,1,2) (state 0xc004000000000000 0)) =
    (0, 0xC004000000000000, false, false) := by decide +kernel

-- Original fcvt_l_d_negative_floor
example : observe («dfn'FCVT_L_D» (3,1,2) (state 0xc004000000000000 0)) =
    (0xFFFFFFFFFFFFFFFD, 0xC004000000000000, false, false) := by decide +kernel

-- Original fcvt_lu_d_negative_floor
example : observe («dfn'FCVT_LU_D» (3,1,2) (state 0xc004000000000000 0)) =
    (0, 0xC004000000000000, false, false) := by decide +kernel

-- Original fcvt_w_d_negative_ceil
example : observe («dfn'FCVT_W_D» (3,1,3) (state 0xc004000000000000 0)) =
    (0xFFFFFFFFFFFFFFFE, 0xC004000000000000, false, false) := by decide +kernel

-- Original fcvt_wu_d_negative_ceil
example : observe («dfn'FCVT_WU_D» (3,1,3) (state 0xc004000000000000 0)) =
    (0, 0xC004000000000000, false, false) := by decide +kernel

-- Original fcvt_l_d_negative_ceil
example : observe («dfn'FCVT_L_D» (3,1,3) (state 0xc004000000000000 0)) =
    (0xFFFFFFFFFFFFFFFE, 0xC004000000000000, false, false) := by decide +kernel

-- Original fcvt_lu_d_negative_ceil
example : observe («dfn'FCVT_LU_D» (3,1,3) (state 0xc004000000000000 0)) =
    (0, 0xC004000000000000, false, false) := by decide +kernel

-- Original fcvt_w_d_qnan
example : observe («dfn'FCVT_W_D» (3,1,0) (state 0x7ff8000000000000 0)) =
    (0x7FFFFFFF, 0x7FF8000000000000, false, false) := by decide +kernel

-- Original fcvt_wu_d_qnan
example : observe («dfn'FCVT_WU_D» (3,1,0) (state 0x7ff8000000000000 0)) =
    (0xFFFFFFFF, 0x7FF8000000000000, false, false) := by decide +kernel

-- Original fcvt_l_d_qnan
example : observe («dfn'FCVT_L_D» (3,1,0) (state 0x7ff8000000000000 0)) =
    (0x7FFFFFFFFFFFFFFF, 0x7FF8000000000000, false, false) := by decide +kernel

-- Original fcvt_lu_d_qnan
example : observe («dfn'FCVT_LU_D» (3,1,0) (state 0x7ff8000000000000 0)) =
    (0xFFFFFFFFFFFFFFFF, 0x7FF8000000000000, false, false) := by decide +kernel

-- Original fcvt_w_d_posinf
example : observe («dfn'FCVT_W_D» (3,1,0) (state 0x7ff0000000000000 0)) =
    (0x7FFFFFFF, 0x7FF0000000000000, false, false) := by decide +kernel

-- Original fcvt_wu_d_posinf
example : observe («dfn'FCVT_WU_D» (3,1,0) (state 0x7ff0000000000000 0)) =
    (0xFFFFFFFF, 0x7FF0000000000000, false, false) := by decide +kernel

-- Original fcvt_l_d_posinf
example : observe («dfn'FCVT_L_D» (3,1,0) (state 0x7ff0000000000000 0)) =
    (0x7FFFFFFFFFFFFFFF, 0x7FF0000000000000, false, false) := by decide +kernel

-- Original fcvt_lu_d_posinf
example : observe («dfn'FCVT_LU_D» (3,1,0) (state 0x7ff0000000000000 0)) =
    (0xFFFFFFFFFFFFFFFF, 0x7FF0000000000000, false, false) := by decide +kernel

-- Original fcvt_w_d_neginf
example : observe («dfn'FCVT_W_D» (3,1,0) (state 0xfff0000000000000 0)) =
    (0xFFFFFFFF80000000, 0xFFF0000000000000, false, false) := by decide +kernel

-- Original fcvt_wu_d_neginf
example : observe («dfn'FCVT_WU_D» (3,1,0) (state 0xfff0000000000000 0)) =
    (0, 0xFFF0000000000000, false, false) := by decide +kernel

-- Original fcvt_l_d_neginf
example : observe («dfn'FCVT_L_D» (3,1,0) (state 0xfff0000000000000 0)) =
    (0x8000000000000000, 0xFFF0000000000000, false, false) := by decide +kernel

-- Original fcvt_lu_d_neginf
example : observe («dfn'FCVT_LU_D» (3,1,0) (state 0xfff0000000000000 0)) =
    (0, 0xFFF0000000000000, false, false) := by decide +kernel

-- Original fcvt_w_d_overflow
example : observe («dfn'FCVT_W_D» (3,1,0) (state 0x43f0000000000000 0)) =
    (0x7FFFFFFF, 0x43F0000000000000, false, false) := by decide +kernel

-- Original fcvt_wu_d_overflow
example : observe («dfn'FCVT_WU_D» (3,1,0) (state 0x43f0000000000000 0)) =
    (0xFFFFFFFF, 0x43F0000000000000, false, false) := by decide +kernel

-- Original fcvt_l_d_overflow
example : observe («dfn'FCVT_L_D» (3,1,0) (state 0x43f0000000000000 0)) =
    (0x7FFFFFFFFFFFFFFF, 0x43F0000000000000, false, false) := by decide +kernel

-- Original fcvt_lu_d_overflow
example : observe («dfn'FCVT_LU_D» (3,1,0) (state 0x43f0000000000000 0)) =
    (0xFFFFFFFFFFFFFFFF, 0x43F0000000000000, false, false) := by decide +kernel

-- Original fcvt_w_d_negative_range
example : observe («dfn'FCVT_W_D» (3,1,0) (state 0xc3f0000000000000 0)) =
    (0xFFFFFFFF80000000, 0xC3F0000000000000, false, false) := by decide +kernel

-- Original fcvt_wu_d_negative_range
example : observe («dfn'FCVT_WU_D» (3,1,0) (state 0xc3f0000000000000 0)) =
    (0, 0xC3F0000000000000, false, false) := by decide +kernel

-- Original fcvt_l_d_negative_range
example : observe («dfn'FCVT_L_D» (3,1,0) (state 0xc3f0000000000000 0)) =
    (0x8000000000000000, 0xC3F0000000000000, false, false) := by decide +kernel

-- Original fcvt_lu_d_negative_range
example : observe («dfn'FCVT_LU_D» (3,1,0) (state 0xc3f0000000000000 0)) =
    (0, 0xC3F0000000000000, false, false) := by decide +kernel

-- Original fcvt_w_d_dynamic_ceil
example : observe («dfn'FCVT_W_D» (3,1,7) (state 0x4004000000000000 3)) =
    (3, 0x4004000000000000, false, false) := by decide +kernel

-- Original fcvt_wu_d_dynamic_ceil
example : observe («dfn'FCVT_WU_D» (3,1,7) (state 0x4004000000000000 3)) =
    (3, 0x4004000000000000, false, false) := by decide +kernel

-- Original fcvt_l_d_dynamic_ceil
example : observe («dfn'FCVT_L_D» (3,1,7) (state 0x4004000000000000 3)) =
    (3, 0x4004000000000000, false, false) := by decide +kernel

-- Original fcvt_lu_d_dynamic_ceil
example : observe («dfn'FCVT_LU_D» (3,1,7) (state 0x4004000000000000 3)) =
    (3, 0x4004000000000000, false, false) := by decide +kernel

-- Original fcvt_w_d_invalid
example : observe («dfn'FCVT_W_D» (3,1,4) (state 0x3ff0000000000000 0)) =
    (99, 0x3FF0000000000000, false, true) := by decide +kernel

-- Original fcvt_wu_d_invalid
example : observe («dfn'FCVT_WU_D» (3,1,4) (state 0x3ff0000000000000 0)) =
    (99, 0x3FF0000000000000, false, true) := by decide +kernel

-- Original fcvt_l_d_invalid
example : observe («dfn'FCVT_L_D» (3,1,4) (state 0x3ff0000000000000 0)) =
    (99, 0x3FF0000000000000, false, true) := by decide +kernel

-- Original fcvt_lu_d_invalid
example : observe («dfn'FCVT_LU_D» (3,1,4) (state 0x3ff0000000000000 0)) =
    (99, 0x3FF0000000000000, false, true) := by decide +kernel

end Flapjack.Test.L3RiscvFpToIntParity

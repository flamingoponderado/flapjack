import Flapjack.RiscV.L3.Defs

/-! Native kernel replays of original L3 FP comparison transitions. Fixture
fields match the original oracle; untouched ARB fields use native defaults.
Binary32 preserves the destination high32 bits, binary64 writes the whole
register. Both integer destination and NV flag are observed for every case.
The generic IEEE real-value rendering remains qualified, not an equivalence
proof or completion of full FP Run/NextRISCV. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
namespace Flapjack.Test.L3RiscvFpCompareParity
open Flapjack.RiscV.L3 Flapjack
private def state (a b : BitVec 64) : riscv_state :=
  { (default : riscv_state) with
    procID := 0
    c_gpr := fun _ r => if r = 3 then 99 else 0
    c_fpr := fun _ r => if r = 1 then a else if r = 2 then b else
      if r = 3 then 0xabc0000000000000 else 0
    c_UCSR := fun _ => { (default : UserCSR) with
      fpcsr := { (default : FPCSR) with NV := false, FRM := 0 } }
    c_MCSR := fun _ => { (default : MachineCSR) with mstatus := default } }
private def observe (s : riscv_state) : BitVec 64 × BitVec 64 × Bool :=
  (GPR 3 s, FPRD 3 s, (fcsr s).NV)

-- Original fmin_s_one_two
example : observe («dfn'FMIN_S» (3,1,2) (state 0x3f800000 0x40000000)) =
    (99, 0xabc000003f800000, false) := by decide +kernel

-- Original fmax_s_one_two
example : observe («dfn'FMAX_S» (3,1,2) (state 0x3f800000 0x40000000)) =
    (99, 0xabc0000040000000, false) := by decide +kernel

-- Original flt_s_one_two
example : observe («dfn'FLT_S» (3,1,2) (state 0x3f800000 0x40000000)) =
    (1, 0xabc0000000000000, false) := by decide +kernel

-- Original fle_s_one_two
example : observe («dfn'FLE_S» (3,1,2) (state 0x3f800000 0x40000000)) =
    (1, 0xabc0000000000000, false) := by decide +kernel

-- Original feq_s_one_two
example : observe («dfn'FEQ_S» (3,1,2) (state 0x3f800000 0x40000000)) =
    (0, 0xabc0000000000000, false) := by decide +kernel

-- Original fmin_s_signed_zero
example : observe («dfn'FMIN_S» (3,1,2) (state 0x0 0x80000000)) =
    (99, 0xabc0000000000000, false) := by decide +kernel

-- Original fmax_s_signed_zero
example : observe («dfn'FMAX_S» (3,1,2) (state 0x0 0x80000000)) =
    (99, 0xabc0000080000000, false) := by decide +kernel

-- Original flt_s_signed_zero
example : observe («dfn'FLT_S» (3,1,2) (state 0x0 0x80000000)) =
    (0, 0xabc0000000000000, false) := by decide +kernel

-- Original fle_s_signed_zero
example : observe («dfn'FLE_S» (3,1,2) (state 0x0 0x80000000)) =
    (1, 0xabc0000000000000, false) := by decide +kernel

-- Original feq_s_signed_zero
example : observe («dfn'FEQ_S» (3,1,2) (state 0x0 0x80000000)) =
    (1, 0xabc0000000000000, false) := by decide +kernel

-- Original fmin_s_qnan_one
example : observe («dfn'FMIN_S» (3,1,2) (state 0x7fc00000 0x3f800000)) =
    (99, 0xabc000003f800000, false) := by decide +kernel

-- Original fmax_s_qnan_one
example : observe («dfn'FMAX_S» (3,1,2) (state 0x7fc00000 0x3f800000)) =
    (99, 0xabc000003f800000, false) := by decide +kernel

-- Original flt_s_qnan_one
example : observe («dfn'FLT_S» (3,1,2) (state 0x7fc00000 0x3f800000)) =
    (0, 0xabc0000000000000, true) := by decide +kernel

-- Original fle_s_qnan_one
example : observe («dfn'FLE_S» (3,1,2) (state 0x7fc00000 0x3f800000)) =
    (0, 0xabc0000000000000, true) := by decide +kernel

-- Original feq_s_qnan_one
example : observe («dfn'FEQ_S» (3,1,2) (state 0x7fc00000 0x3f800000)) =
    (0, 0xabc0000000000000, false) := by decide +kernel

-- Original fmin_s_snan_one
example : observe («dfn'FMIN_S» (3,1,2) (state 0x7f800001 0x3f800000)) =
    (99, 0xabc000007fc00000, false) := by decide +kernel

-- Original fmax_s_snan_one
example : observe («dfn'FMAX_S» (3,1,2) (state 0x7f800001 0x3f800000)) =
    (99, 0xabc000007fc00000, false) := by decide +kernel

-- Original flt_s_snan_one
example : observe («dfn'FLT_S» (3,1,2) (state 0x7f800001 0x3f800000)) =
    (0, 0xabc0000000000000, true) := by decide +kernel

-- Original fle_s_snan_one
example : observe («dfn'FLE_S» (3,1,2) (state 0x7f800001 0x3f800000)) =
    (0, 0xabc0000000000000, true) := by decide +kernel

-- Original feq_s_snan_one
example : observe («dfn'FEQ_S» (3,1,2) (state 0x7f800001 0x3f800000)) =
    (0, 0xabc0000000000000, true) := by decide +kernel

-- Original fmin_s_payload_nan_one
example : observe («dfn'FMIN_S» (3,1,2) (state 0x7fc00001 0x3f800000)) =
    (99, 0xabc000007fc00001, false) := by decide +kernel

-- Original fmax_s_payload_nan_one
example : observe («dfn'FMAX_S» (3,1,2) (state 0x7fc00001 0x3f800000)) =
    (99, 0xabc000007fc00001, false) := by decide +kernel

-- Original flt_s_payload_nan_one
example : observe («dfn'FLT_S» (3,1,2) (state 0x7fc00001 0x3f800000)) =
    (0, 0xabc0000000000000, true) := by decide +kernel

-- Original fle_s_payload_nan_one
example : observe («dfn'FLE_S» (3,1,2) (state 0x7fc00001 0x3f800000)) =
    (0, 0xabc0000000000000, true) := by decide +kernel

-- Original feq_s_payload_nan_one
example : observe («dfn'FEQ_S» (3,1,2) (state 0x7fc00001 0x3f800000)) =
    (0, 0xabc0000000000000, false) := by decide +kernel

-- Original fmin_s_both_nan
example : observe («dfn'FMIN_S» (3,1,2) (state 0x7fc00000 0x7fc00000)) =
    (99, 0xabc000007fc00000, false) := by decide +kernel

-- Original fmax_s_both_nan
example : observe («dfn'FMAX_S» (3,1,2) (state 0x7fc00000 0x7fc00000)) =
    (99, 0xabc000007fc00000, false) := by decide +kernel

-- Original flt_s_both_nan
example : observe («dfn'FLT_S» (3,1,2) (state 0x7fc00000 0x7fc00000)) =
    (0, 0xabc0000000000000, true) := by decide +kernel

-- Original fle_s_both_nan
example : observe («dfn'FLE_S» (3,1,2) (state 0x7fc00000 0x7fc00000)) =
    (0, 0xabc0000000000000, true) := by decide +kernel

-- Original feq_s_both_nan
example : observe («dfn'FEQ_S» (3,1,2) (state 0x7fc00000 0x7fc00000)) =
    (0, 0xabc0000000000000, false) := by decide +kernel

-- Original fmin_s_infinities
example : observe («dfn'FMIN_S» (3,1,2) (state 0x7f800000 0xff800000)) =
    (99, 0xabc00000ff800000, false) := by decide +kernel

-- Original fmax_s_infinities
example : observe («dfn'FMAX_S» (3,1,2) (state 0x7f800000 0xff800000)) =
    (99, 0xabc000007f800000, false) := by decide +kernel

-- Original flt_s_infinities
example : observe («dfn'FLT_S» (3,1,2) (state 0x7f800000 0xff800000)) =
    (0, 0xabc0000000000000, false) := by decide +kernel

-- Original fle_s_infinities
example : observe («dfn'FLE_S» (3,1,2) (state 0x7f800000 0xff800000)) =
    (0, 0xabc0000000000000, false) := by decide +kernel

-- Original feq_s_infinities
example : observe («dfn'FEQ_S» (3,1,2) (state 0x7f800000 0xff800000)) =
    (0, 0xabc0000000000000, false) := by decide +kernel

-- Original fmin_s_subnormals
example : observe («dfn'FMIN_S» (3,1,2) (state 0x1 0x2)) =
    (99, 0xabc0000000000001, false) := by decide +kernel

-- Original fmax_s_subnormals
example : observe («dfn'FMAX_S» (3,1,2) (state 0x1 0x2)) =
    (99, 0xabc0000000000002, false) := by decide +kernel

-- Original flt_s_subnormals
example : observe («dfn'FLT_S» (3,1,2) (state 0x1 0x2)) =
    (1, 0xabc0000000000000, false) := by decide +kernel

-- Original fle_s_subnormals
example : observe («dfn'FLE_S» (3,1,2) (state 0x1 0x2)) =
    (1, 0xabc0000000000000, false) := by decide +kernel

-- Original feq_s_subnormals
example : observe («dfn'FEQ_S» (3,1,2) (state 0x1 0x2)) =
    (0, 0xabc0000000000000, false) := by decide +kernel

-- Original fmin_d_one_two
example : observe («dfn'FMIN_D» (3,1,2) (state 0x3ff0000000000000 0x4000000000000000)) =
    (99, 0x3ff0000000000000, false) := by decide +kernel

-- Original fmax_d_one_two
example : observe («dfn'FMAX_D» (3,1,2) (state 0x3ff0000000000000 0x4000000000000000)) =
    (99, 0x4000000000000000, false) := by decide +kernel

-- Original flt_d_one_two
example : observe («dfn'FLT_D» (3,1,2) (state 0x3ff0000000000000 0x4000000000000000)) =
    (1, 0xabc0000000000000, false) := by decide +kernel

-- Original fle_d_one_two
example : observe («dfn'FLE_D» (3,1,2) (state 0x3ff0000000000000 0x4000000000000000)) =
    (1, 0xabc0000000000000, false) := by decide +kernel

-- Original feq_d_one_two
example : observe («dfn'FEQ_D» (3,1,2) (state 0x3ff0000000000000 0x4000000000000000)) =
    (0, 0xabc0000000000000, false) := by decide +kernel

-- Original fmin_d_signed_zero
example : observe («dfn'FMIN_D» (3,1,2) (state 0x0 0x8000000000000000)) =
    (99, 0, false) := by decide +kernel

-- Original fmax_d_signed_zero
example : observe («dfn'FMAX_D» (3,1,2) (state 0x0 0x8000000000000000)) =
    (99, 0x8000000000000000, false) := by decide +kernel

-- Original flt_d_signed_zero
example : observe («dfn'FLT_D» (3,1,2) (state 0x0 0x8000000000000000)) =
    (0, 0xabc0000000000000, false) := by decide +kernel

-- Original fle_d_signed_zero
example : observe («dfn'FLE_D» (3,1,2) (state 0x0 0x8000000000000000)) =
    (1, 0xabc0000000000000, false) := by decide +kernel

-- Original feq_d_signed_zero
example : observe («dfn'FEQ_D» (3,1,2) (state 0x0 0x8000000000000000)) =
    (1, 0xabc0000000000000, false) := by decide +kernel

-- Original fmin_d_qnan_one
example : observe («dfn'FMIN_D» (3,1,2) (state 0x7ff8000000000000 0x3ff0000000000000)) =
    (99, 0x3ff0000000000000, false) := by decide +kernel

-- Original fmax_d_qnan_one
example : observe («dfn'FMAX_D» (3,1,2) (state 0x7ff8000000000000 0x3ff0000000000000)) =
    (99, 0x3ff0000000000000, false) := by decide +kernel

-- Original flt_d_qnan_one
example : observe («dfn'FLT_D» (3,1,2) (state 0x7ff8000000000000 0x3ff0000000000000)) =
    (0, 0xabc0000000000000, true) := by decide +kernel

-- Original fle_d_qnan_one
example : observe («dfn'FLE_D» (3,1,2) (state 0x7ff8000000000000 0x3ff0000000000000)) =
    (0, 0xabc0000000000000, true) := by decide +kernel

-- Original feq_d_qnan_one
example : observe («dfn'FEQ_D» (3,1,2) (state 0x7ff8000000000000 0x3ff0000000000000)) =
    (0, 0xabc0000000000000, false) := by decide +kernel

-- Original fmin_d_snan_one
example : observe («dfn'FMIN_D» (3,1,2) (state 0x7ff0000000000001 0x3ff0000000000000)) =
    (99, 0x7ff8000000000000, false) := by decide +kernel

-- Original fmax_d_snan_one
example : observe («dfn'FMAX_D» (3,1,2) (state 0x7ff0000000000001 0x3ff0000000000000)) =
    (99, 0x7ff8000000000000, false) := by decide +kernel

-- Original flt_d_snan_one
example : observe («dfn'FLT_D» (3,1,2) (state 0x7ff0000000000001 0x3ff0000000000000)) =
    (0, 0xabc0000000000000, true) := by decide +kernel

-- Original fle_d_snan_one
example : observe («dfn'FLE_D» (3,1,2) (state 0x7ff0000000000001 0x3ff0000000000000)) =
    (0, 0xabc0000000000000, true) := by decide +kernel

-- Original feq_d_snan_one
example : observe («dfn'FEQ_D» (3,1,2) (state 0x7ff0000000000001 0x3ff0000000000000)) =
    (0, 0xabc0000000000000, true) := by decide +kernel

-- Original fmin_d_payload_nan_one
example : observe («dfn'FMIN_D» (3,1,2) (state 0x7ff8000000000001 0x3ff0000000000000)) =
    (99, 0x7ff8000000000001, false) := by decide +kernel

-- Original fmax_d_payload_nan_one
example : observe («dfn'FMAX_D» (3,1,2) (state 0x7ff8000000000001 0x3ff0000000000000)) =
    (99, 0x7ff8000000000001, false) := by decide +kernel

-- Original flt_d_payload_nan_one
example : observe («dfn'FLT_D» (3,1,2) (state 0x7ff8000000000001 0x3ff0000000000000)) =
    (0, 0xabc0000000000000, true) := by decide +kernel

-- Original fle_d_payload_nan_one
example : observe («dfn'FLE_D» (3,1,2) (state 0x7ff8000000000001 0x3ff0000000000000)) =
    (0, 0xabc0000000000000, true) := by decide +kernel

-- Original feq_d_payload_nan_one
example : observe («dfn'FEQ_D» (3,1,2) (state 0x7ff8000000000001 0x3ff0000000000000)) =
    (0, 0xabc0000000000000, false) := by decide +kernel

-- Original fmin_d_both_nan
example : observe («dfn'FMIN_D» (3,1,2) (state 0x7ff8000000000000 0x7ff8000000000000)) =
    (99, 0x7ff8000000000000, false) := by decide +kernel

-- Original fmax_d_both_nan
example : observe («dfn'FMAX_D» (3,1,2) (state 0x7ff8000000000000 0x7ff8000000000000)) =
    (99, 0x7ff8000000000000, false) := by decide +kernel

-- Original flt_d_both_nan
example : observe («dfn'FLT_D» (3,1,2) (state 0x7ff8000000000000 0x7ff8000000000000)) =
    (0, 0xabc0000000000000, true) := by decide +kernel

-- Original fle_d_both_nan
example : observe («dfn'FLE_D» (3,1,2) (state 0x7ff8000000000000 0x7ff8000000000000)) =
    (0, 0xabc0000000000000, true) := by decide +kernel

-- Original feq_d_both_nan
example : observe («dfn'FEQ_D» (3,1,2) (state 0x7ff8000000000000 0x7ff8000000000000)) =
    (0, 0xabc0000000000000, false) := by decide +kernel

-- Original fmin_d_infinities
example : observe («dfn'FMIN_D» (3,1,2) (state 0x7ff0000000000000 0xfff0000000000000)) =
    (99, 0xfff0000000000000, false) := by decide +kernel

-- Original fmax_d_infinities
example : observe («dfn'FMAX_D» (3,1,2) (state 0x7ff0000000000000 0xfff0000000000000)) =
    (99, 0x7ff0000000000000, false) := by decide +kernel

-- Original flt_d_infinities
example : observe («dfn'FLT_D» (3,1,2) (state 0x7ff0000000000000 0xfff0000000000000)) =
    (0, 0xabc0000000000000, false) := by decide +kernel

-- Original fle_d_infinities
example : observe («dfn'FLE_D» (3,1,2) (state 0x7ff0000000000000 0xfff0000000000000)) =
    (0, 0xabc0000000000000, false) := by decide +kernel

-- Original feq_d_infinities
example : observe («dfn'FEQ_D» (3,1,2) (state 0x7ff0000000000000 0xfff0000000000000)) =
    (0, 0xabc0000000000000, false) := by decide +kernel

-- Original fmin_d_subnormals
example : observe («dfn'FMIN_D» (3,1,2) (state 0x1 0x2)) =
    (99, 1, false) := by decide +kernel

-- Original fmax_d_subnormals
example : observe («dfn'FMAX_D» (3,1,2) (state 0x1 0x2)) =
    (99, 2, false) := by decide +kernel

-- Original flt_d_subnormals
example : observe («dfn'FLT_D» (3,1,2) (state 0x1 0x2)) =
    (1, 0xabc0000000000000, false) := by decide +kernel

-- Original fle_d_subnormals
example : observe («dfn'FLE_D» (3,1,2) (state 0x1 0x2)) =
    (1, 0xabc0000000000000, false) := by decide +kernel

-- Original feq_d_subnormals
example : observe («dfn'FEQ_D» (3,1,2) (state 0x1 0x2)) =
    (0, 0xabc0000000000000, false) := by decide +kernel

end Flapjack.Test.L3RiscvFpCompareParity

import Flapjack.RiscV.L3.Defs

/-! Kernel replays of complete original FCLASS state observations. This is
regression evidence, not a HOL-to-Lean equivalence theorem. -/
set_option maxRecDepth 200000
set_option synthInstance.maxSize 2048
namespace Flapjack.Test.L3RiscvFclassParity
open Flapjack.RiscV.L3
private def state (v : BitVec 64) : riscv_state :=
  { (default : riscv_state) with
    procID := 7
    c_gpr := fun _ _ => 99
    c_NextFetch := fun _ => none
    c_fpr := fun c r => if c = 7 && r = 1 then v
      else if c = 7 then 0xcafe000000000000 else 0xbbbb000000000000
    c_update := fun _ => { (default : StateDelta) with data1 := some 42 }
    c_UCSR := fun _ => { (default : UserCSR) with
      fpcsr := { (default : FPCSR) with NV := false, NX := true, FRM := 0 } }
    c_MCSR := fun _ => { (default : MachineCSR) with
      mstatus := { (default : mstatus) with MFS := 0, MSD := false } } }
private def observe (s : riscv_state) :
    BitVec 64 × BitVec 64 × BitVec 64 × Bool × Bool × BitVec 2 × Option (BitVec 64) × BitVec 64 :=
  (GPR 3 s, s.c_gpr 7 0, FPRD 1 s, (fcsr s).NV, (fcsr s).NX,
   (MCSR s).mstatus.MFS, (Delta s).data1, s.c_gpr 8 3)

-- Original fclass_s_neg_inf
example : observe («dfn'FCLASS_S» (3,1) (state 0xff800000)) =
  (1,99,0xFF800000,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_s_neg_normal
example : observe («dfn'FCLASS_S» (3,1) (state 0xbf800000)) =
  (2,99,0xBF800000,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_s_neg_subnormal
example : observe («dfn'FCLASS_S» (3,1) (state 0x80000001)) =
  (4,99,0x80000001,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_s_neg_zero
example : observe («dfn'FCLASS_S» (3,1) (state 0x80000000)) =
  (8,99,0x80000000,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_s_pos_zero
example : observe («dfn'FCLASS_S» (3,1) (state 0x0)) =
  (16,99,0,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_s_pos_subnormal
example : observe («dfn'FCLASS_S» (3,1) (state 0x1)) =
  (32,99,1,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_s_pos_normal
example : observe («dfn'FCLASS_S» (3,1) (state 0x3f800000)) =
  (64,99,0x3F800000,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_s_pos_inf
example : observe («dfn'FCLASS_S» (3,1) (state 0x7f800000)) =
  (128,99,0x7F800000,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_s_snan
example : observe («dfn'FCLASS_S» (3,1) (state 0x7f800001)) =
  (256,99,0x7F800001,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_s_canonical_nan
example : observe («dfn'FCLASS_S» (3,1) (state 0x7fc00000)) =
  (512,99,0x7FC00000,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_s_payload_qnan
example : observe («dfn'FCLASS_S» (3,1) (state 0x7fc00001)) =
  (0,99,0x7FC00001,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_s_neg_qnan
example : observe («dfn'FCLASS_S» (3,1) (state 0xffc00000)) =
  (0,99,0xFFC00000,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_s_neg_snan
example : observe («dfn'FCLASS_S» (3,1) (state 0xff800001)) =
  (256,99,0xFF800001,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_s_dest_zero
example : observe («dfn'FCLASS_S» (0,1) (state 0x3f800000)) =
  (99,99,0x3F800000,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_d_neg_inf
example : observe («dfn'FCLASS_D» (3,1) (state 0xfff0000000000000)) =
  (1,99,0xFFF0000000000000,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_d_neg_normal
example : observe («dfn'FCLASS_D» (3,1) (state 0xbff0000000000000)) =
  (2,99,0xBFF0000000000000,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_d_neg_subnormal
example : observe («dfn'FCLASS_D» (3,1) (state 0x8000000000000001)) =
  (4,99,0x8000000000000001,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_d_neg_zero
example : observe («dfn'FCLASS_D» (3,1) (state 0x8000000000000000)) =
  (8,99,0x8000000000000000,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_d_pos_zero
example : observe («dfn'FCLASS_D» (3,1) (state 0x0)) =
  (16,99,0,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_d_pos_subnormal
example : observe («dfn'FCLASS_D» (3,1) (state 0x1)) =
  (32,99,1,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_d_pos_normal
example : observe («dfn'FCLASS_D» (3,1) (state 0x3ff0000000000000)) =
  (64,99,0x3FF0000000000000,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_d_pos_inf
example : observe («dfn'FCLASS_D» (3,1) (state 0x7ff0000000000000)) =
  (128,99,0x7FF0000000000000,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_d_snan
example : observe («dfn'FCLASS_D» (3,1) (state 0x7ff0000000000001)) =
  (256,99,0x7FF0000000000001,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_d_canonical_nan
example : observe («dfn'FCLASS_D» (3,1) (state 0x7ff8000000000000)) =
  (512,99,0x7FF8000000000000,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_d_payload_qnan
example : observe («dfn'FCLASS_D» (3,1) (state 0x7ff8000000000001)) =
  (0,99,0x7FF8000000000001,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_d_neg_qnan
example : observe («dfn'FCLASS_D» (3,1) (state 0xfff8000000000000)) =
  (0,99,0xFFF8000000000000,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_d_neg_snan
example : observe («dfn'FCLASS_D» (3,1) (state 0xfff0000000000001)) =
  (256,99,0xFFF0000000000001,false,true,0,some 42,99) := by decide +kernel

-- Original fclass_d_dest_zero
example : observe («dfn'FCLASS_D» (0,1) (state 0x3ff0000000000000)) =
  (99,99,0x3FF0000000000000,false,true,0,some 42,99) := by decide +kernel

end Flapjack.Test.L3RiscvFclassParity

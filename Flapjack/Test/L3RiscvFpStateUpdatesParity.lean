import Flapjack.RiscV.L3.Defs

/-! Kernel replay of original full FP write/flag update observations, including
current/other-core separation, preserved flags, registerzero and Delta.data1.
This regression evidence does not replace full source correspondence review. -/
set_option maxRecDepth 200000
set_option synthInstance.maxSize 2048
namespace Flapjack.Test.L3RiscvFpStateUpdatesParity
open Flapjack.RiscV.L3
private def state : riscv_state :=
  { (default : riscv_state) with
    procID := 7
    c_gpr := fun _ _ => 99
    c_NextFetch := fun _ => none
    c_fpr := fun c _ => if c = 7 then 0xcafe000000000000 else 0xbbbb000000000000
    c_update := fun _ => { (default : StateDelta) with data1 := some 42 }
    c_UCSR := fun _ => { (default : UserCSR) with
      fpcsr := { (default : FPCSR) with NV := false, NX := true, FRM := 0 } }
    c_MCSR := fun _ => { (default : MachineCSR) with
      mstatus := { (default : mstatus) with MFS := 0, MSD := false } } }
private def observe (s : riscv_state) :
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 2 × Bool × Option (BitVec 64) × Bool × Bool × BitVec 64 :=
  (FPRD 3 s, GPR 3 s, s.c_gpr 7 0, (MCSR s).mstatus.MFS,
   (MCSR s).mstatus.MSD, (Delta s).data1, (fcsr s).NV, (fcsr s).NX, s.c_fpr 8 3)

-- Original write_fprs
example : observe (writeFPRS (3,0x3f800000) state) =
  (0xCAFE00003F800000, 99, 99, 3, true, some 0x3F800000, false, true, 0xBBBB000000000000) := by decide +kernel

-- Original write_fprd
example : observe (writeFPRD (3,0x3ff0000000000000) state) =
  (0x3FF0000000000000, 99, 99, 3, true, some 0x3FF0000000000000, false, true, 0xBBBB000000000000) := by decide +kernel

-- Original set_invalid
example : observe (setFP_Invalid () state) =
  (0xCAFE000000000000, 99, 99, 3, true, some 42, true, true, 0xBBBB000000000000) := by decide +kernel

-- Original write_gpr_zero
example : observe («write'GPR» (77,0) state) =
  (0xCAFE000000000000, 99, 99, 0, false, some 42, false, true, 0xBBBB000000000000) := by decide +kernel

-- Original write_gpr_three
example : observe («write'GPR» (77,3) state) =
  (0xCAFE000000000000, 77, 99, 0, false, some 42, false, true, 0xBBBB000000000000) := by decide +kernel

end Flapjack.Test.L3RiscvFpStateUpdatesParity

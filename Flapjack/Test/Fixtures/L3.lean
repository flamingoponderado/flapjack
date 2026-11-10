import Flapjack.RiscV.L3.Defs.MMU.Access
set_option maxRecDepth 200000

/-!
# Shared RISC-V L3 parity fixtures

`writeFullWord` normalizes the complete aligned 64-bit PTE word store and
`state` is the arbitrary native state used by the arithmetic and square-root
rows. Both are shared by the L3 parity modules.
-/

namespace Flapjack.Test.Fixtures.L3

open Flapjack.RiscV.L3 Flapjack

/-- Flapjack regression normalization for the complete aligned PTE word store.
No standalone HOL original; the original rawWriteData equation is unchanged. -/
theorem writeFullWord (w : BitVec 64) (s : riscv_state) :
    rawWriteData (BitVec.ofNat 64 0, w, 8) s = «write'MEM» (w, BitVec.ofNat 61 0) s := by
  have hmask : ((BitVec.setWidth 64 (BitVec.ofNat 1 1) <<< (8 * 8)) -
      (BitVec.ofNat 64 1)) = BitVec.allOnes 64 := by decide
  have hidx : holWordExtract 61 63 3 (BitVec.ofNat 64 0) = BitVec.ofNat 61 0 := by decide
  have halign : holWordExtract 3 2 0 (BitVec.ofNat 64 0) = BitVec.ofNat 3 0 := by decide
  simp only [rawWriteData, hmask, hidx, halign]
  simp only [BitVec.toNat_zero, BEq.refl, ↓reduceIte,
    BitVec.not_allOnes, BitVec.and_zero, BitVec.and_allOnes, BitVec.zero_or]

/-- The arbitrary native state used by the arithmetic and square-root rows. -/
def state (a b : BitVec 64) (frm : BitVec 3) : riscv_state :=
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

end Flapjack.Test.Fixtures.L3

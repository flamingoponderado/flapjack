import Flapjack.RiscV.L3.Support
import Std.Tactic.BVDecide

/-! Full signed immediate reconstruction from the original target proof. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack.RiscV.L3

/-- Flapjack bit-list/extract correspondence infrastructure over the full word. -/
private theorem twelve_bits (c : BitVec 64) :
    holV2w 12 [c.getLsbD 11,c.getLsbD 10,c.getLsbD 9,c.getLsbD 8,c.getLsbD 7,c.getLsbD 6,c.getLsbD 5,c.getLsbD 4,c.getLsbD 3,c.getLsbD 2,c.getLsbD 1,c.getLsbD 0] = BitVec.extractLsb' 0 12 c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 := by omega
  rcases cases_i with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  all_goals
    subst i
    simp only [holV2w]
    rw [Flapjack.getLsbD_holFcpWord]
    simp

@[hol "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml" "lem4"]
theorem signed_twelve_bit_reconstruction (c : BitVec 64)
    (h : (0xFFFFFFFFFFFFF800 : BitVec 64).sle c = true ∧
      c.sle 0x7FF = true) :
    (holV2w 12 [c.getLsbD 11,c.getLsbD 10,c.getLsbD 9,c.getLsbD 8,c.getLsbD 7,c.getLsbD 6,c.getLsbD 5,c.getLsbD 4,c.getLsbD 3,c.getLsbD 2,c.getLsbD 1,c.getLsbD 0]).signExtend 64 = c := by
  rw [twelve_bits]
  bv_decide

/-- Original aligned split-immediate reconstruction: both signed limits and
low-two-bit alignment are retained, including the masked low immediate. -/
@[hol "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml" "lem12b"]
theorem split_immediate_reconstruction (c : BitVec 64)
    (h : (0xFFFFFFFF80000000 : BitVec 64).sle c = true ∧
      c.sle 0x7FFFF7FF = true ∧ (BitVec.extractLsb' 0 2 c).setWidth 64 = 0) :
    ((BitVec.extractLsb' 12 20
      (c + (-1 : BitVec 64) * (BitVec.extractLsb' 0 12 c).signExtend 64)).append
        (0 : BitVec 12)).signExtend 64 +
      ((BitVec.extractLsb' 0 12 c) &&& ~~~(2 : BitVec 12)).signExtend 64 = c := by
  bv_decide

end Flapjack.RiscV.TargetProof

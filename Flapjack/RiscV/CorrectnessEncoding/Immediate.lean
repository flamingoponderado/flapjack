import Flapjack.RiscV.L3.Support
import Init.Data.BitVec.Bitblast

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

theorem signed_twelve_bit_reconstruction (c : BitVec 64)
    (h : (0xFFFFFFFFFFFFF800 : BitVec 64).sle c = true ∧
      c.sle 0x7FF = true) :
    (holV2w 12 [c.getLsbD 11,c.getLsbD 10,c.getLsbD 9,c.getLsbD 8,c.getLsbD 7,c.getLsbD 6,c.getLsbD 5,c.getLsbD 4,c.getLsbD 3,c.getLsbD 2,c.getLsbD 1,c.getLsbD 0]).signExtend 64 = c := by
  rw [twelve_bits]
  change (c.setWidth 12).signExtend 64 = c
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide : 12 ≤ 64)]
  have et := BitVec.toInt_signExtend_eq_toInt_bmod_of_le c (by decide : 12 ≤ 64)
  rw [BitVec.signExtend_eq_setWidth_of_le c (by decide : 12 ≤ 64)] at et
  rw [et]
  simp only [BitVec.sle_eq_decide, decide_eq_true_eq] at h
  change -2048 ≤ c.toInt ∧ c.toInt ≤ 2047 at h
  apply Int.bmod_eq_of_le <;> omega

/-- Original aligned split-immediate reconstruction: both signed limits and
low-two-bit alignment are retained, including the masked low immediate. -/
theorem split_immediate_reconstruction (c : BitVec 64)
    (h : (0xFFFFFFFF80000000 : BitVec 64).sle c = true ∧
      c.sle 0x7FFFF7FF = true ∧ (BitVec.extractLsb' 0 2 c).setWidth 64 = 0) :
    ((BitVec.extractLsb' 12 20
      (c + (-1 : BitVec 64) * (BitVec.extractLsb' 0 12 c).signExtend 64)).append
        (0 : BitVec 12)).signExtend 64 +
      ((BitVec.extractLsb' 0 12 c) &&& ~~~(2 : BitVec 12)).signExtend 64 = c := by
  have hbit : c.getLsbD 1 = false := by
    have e := congrArg (fun x : BitVec 64 => x.getLsbD 1) h.2.2
    simpa using e
  have hmask : (BitVec.extractLsb' 0 12 c) &&& ~~~(2 : BitVec 12) =
      BitVec.extractLsb' 0 12 c := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and]
    by_cases ei : i = 1
    · subst i
      rw [hbit]
      rfl
    · have eb : (2 : BitVec 12).getLsbD i = false := by
        change Nat.testBit (2 ^ 1) i = false
        exact Nat.testBit_two_pow_of_ne (Ne.symm ei)
      rw [eb]
      simp only [Bool.not_false, Bool.and_true]
  have em : (-1 : BitVec 64) = (-1#64) := by decide
  rw [hmask, em, ← BitVec.neg_eq_neg_one_mul, ← BitVec.sub_eq_add_neg]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.sle_eq_decide, decide_eq_true_eq] at h
  change -2147483648 ≤ c.toInt ∧ c.toInt ≤ 2147481599 ∧
    (BitVec.extractLsb' 0 2 c).setWidth 64 = 0 at h
  have bound := c.isLt
  have ez : (0 : BitVec 12).toNat = 0 := rfl
  simp only [BitVec.append_eq, BitVec.toNat_add, BitVec.toNat_signExtend,
    BitVec.toNat_append, BitVec.toNat_setWidth, BitVec.msb_eq_decide,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub,
    ez, BitVec.toInt_eq_msb_cond, Nat.or_zero,
    Nat.shiftLeft_eq, Nat.pow_zero, Nat.div_one, decide_eq_true_eq] at *
  repeat (any_goals first | split | split at h)
  all_goals omega

end Flapjack.RiscV.TargetProof

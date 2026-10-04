import Flapjack.RiscV.CorrectnessEncoding.Immediate
/-! Exact original JumpCmp shifted payload reconstruction. Untagged local
composition infrastructure without a separately named HOL original. The
original riscv_target176-257 subtracts two/four halfwords after narrowing
the arithmetic-shifted source offset to word12/word20. These equations retain
that ordering, signed endpoints and all word64 wrap behavior. Only original
near/global offset guards and four-byte source alignment are required. The
PC equations cancel the actual zero/four/eight-byte emitted prefix; no native
execution, decoder, post-state or desired source-target relation is assumed.
Full JumpCmp correctness remains separate dependent work. -/

namespace Flapjack.RiscV.TargetProof.JumpCmp
private theorem near_offset_prefix0_logical (a : BitVec 64)
    (range : -4092 ≤ a.toInt ∧ a.toInt ≤ 4095)
    (aligned : a.toNat % 4 = 0) :
    (((a >>> (1 : Nat)).setWidth 12) - 0#12).signExtend 64 <<< (1 : Nat) = a - 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have bound := a.isLt
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_signExtend,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
    BitVec.toNat_ofNat, BitVec.msb_eq_decide, BitVec.toInt_eq_msb_cond,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, decide_eq_true_eq] at *
  repeat (any_goals first | split | split at range)
  all_goals omega

theorem near_offset_prefix0 (a : BitVec 64)
    (range : -4092 ≤ a.toInt ∧ a.toInt ≤ 4095) (aligned : a.toNat % 4 = 0) :
    (((a.sshiftRight 1).setWidth 12) - 0#12).signExtend 64 <<< (1 : Nat) = a - 0#64 := by
  have bits : (a.sshiftRight 1).setWidth 12 = (a >>> (1 : Nat)).setWidth 12 := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_ushiftRight]
    simp [hi, show ¬64 ≤ i by omega, show 1 + i < 64 by omega]
  rw [bits]
  exact near_offset_prefix0_logical a range aligned


private theorem near_offset_prefix4_logical (a : BitVec 64)
    (range : -4092 ≤ a.toInt ∧ a.toInt ≤ 4095)
    (aligned : a.toNat % 4 = 0) :
    (((a >>> (1 : Nat)).setWidth 12) - 2#12).signExtend 64 <<< (1 : Nat) = a - 4#64 := by
  apply BitVec.eq_of_toNat_eq
  have bound := a.isLt
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_signExtend,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
    BitVec.toNat_ofNat, BitVec.msb_eq_decide, BitVec.toInt_eq_msb_cond,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, decide_eq_true_eq] at *
  repeat (any_goals first | split | split at range)
  all_goals omega

theorem near_offset_prefix4 (a : BitVec 64)
    (range : -4092 ≤ a.toInt ∧ a.toInt ≤ 4095) (aligned : a.toNat % 4 = 0) :
    (((a.sshiftRight 1).setWidth 12) - 2#12).signExtend 64 <<< (1 : Nat) = a - 4#64 := by
  have bits : (a.sshiftRight 1).setWidth 12 = (a >>> (1 : Nat)).setWidth 12 := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_ushiftRight]
    simp [hi, show ¬64 ≤ i by omega, show 1 + i < 64 by omega]
  rw [bits]
  exact near_offset_prefix4_logical a range aligned


private theorem far_offset_prefix4_logical (a : BitVec 64)
    (range : -1048568 ≤ a.toInt ∧ a.toInt ≤ 1048579)
    (aligned : a.toNat % 4 = 0) :
    (((a >>> (1 : Nat)).setWidth 20) - 2#20).signExtend 64 <<< (1 : Nat) = a - 4#64 := by
  apply BitVec.eq_of_toNat_eq
  have bound := a.isLt
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_signExtend,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
    BitVec.toNat_ofNat, BitVec.msb_eq_decide, BitVec.toInt_eq_msb_cond,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, decide_eq_true_eq] at *
  repeat (any_goals first | split | split at range)
  all_goals omega

theorem far_offset_prefix4 (a : BitVec 64)
    (range : -1048568 ≤ a.toInt ∧ a.toInt ≤ 1048579) (aligned : a.toNat % 4 = 0) :
    (((a.sshiftRight 1).setWidth 20) - 2#20).signExtend 64 <<< (1 : Nat) = a - 4#64 := by
  have bits : (a.sshiftRight 1).setWidth 20 = (a >>> (1 : Nat)).setWidth 20 := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_ushiftRight]
    simp [hi, show ¬64 ≤ i by omega, show 1 + i < 64 by omega]
  rw [bits]
  exact far_offset_prefix4_logical a range aligned


private theorem far_offset_prefix8_logical (a : BitVec 64)
    (range : -1048568 ≤ a.toInt ∧ a.toInt ≤ 1048579)
    (aligned : a.toNat % 4 = 0) :
    (((a >>> (1 : Nat)).setWidth 20) - 4#20).signExtend 64 <<< (1 : Nat) = a - 8#64 := by
  apply BitVec.eq_of_toNat_eq
  have bound := a.isLt
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_signExtend,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
    BitVec.toNat_ofNat, BitVec.msb_eq_decide, BitVec.toInt_eq_msb_cond,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, decide_eq_true_eq] at *
  repeat (any_goals first | split | split at range)
  all_goals omega

theorem far_offset_prefix8 (a : BitVec 64)
    (range : -1048568 ≤ a.toInt ∧ a.toInt ≤ 1048579) (aligned : a.toNat % 4 = 0) :
    (((a.sshiftRight 1).setWidth 20) - 4#20).signExtend 64 <<< (1 : Nat) = a - 8#64 := by
  have bits : (a.sshiftRight 1).setWidth 20 = (a >>> (1 : Nat)).setWidth 20 := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_ushiftRight]
    simp [hi, show ¬64 ≤ i by omega, show 1 + i < 64 by omega]
  rw [bits]
  exact far_offset_prefix8_logical a range aligned

theorem prefix_pc (pc a bias : BitVec 64) :
    pc + bias + (a - bias) = pc + a := by
  apply BitVec.eq_of_toNat_eq
  have bp := pc.isLt
  have ba := a.isLt
  have bk := bias.isLt
  simp only [BitVec.toNat_add,BitVec.toNat_sub]
  omega

theorem near_offset_prefix0_pc (pc a : BitVec 64)
    (range : -4092 ≤ a.toInt ∧ a.toInt ≤ 4095) (aligned : a.toNat % 4 = 0) :
    pc + 0#64 +
      ((((a.sshiftRight 1).setWidth 12) - 0#12).signExtend 64 <<< (1 : Nat)) = pc + a := by
  rw [near_offset_prefix0 a range aligned]
  exact prefix_pc pc a 0#64

theorem near_offset_prefix4_pc (pc a : BitVec 64)
    (range : -4092 ≤ a.toInt ∧ a.toInt ≤ 4095) (aligned : a.toNat % 4 = 0) :
    pc + 4#64 +
      ((((a.sshiftRight 1).setWidth 12) - 2#12).signExtend 64 <<< (1 : Nat)) = pc + a := by
  rw [near_offset_prefix4 a range aligned]
  exact prefix_pc pc a 4#64

theorem far_offset_prefix4_pc (pc a : BitVec 64)
    (range : -1048568 ≤ a.toInt ∧ a.toInt ≤ 1048579) (aligned : a.toNat % 4 = 0) :
    pc + 4#64 +
      ((((a.sshiftRight 1).setWidth 20) - 2#20).signExtend 64 <<< (1 : Nat)) = pc + a := by
  rw [far_offset_prefix4 a range aligned]
  exact prefix_pc pc a 4#64

theorem far_offset_prefix8_pc (pc a : BitVec 64)
    (range : -1048568 ≤ a.toInt ∧ a.toInt ≤ 1048579) (aligned : a.toNat % 4 = 0) :
    pc + 8#64 +
      ((((a.sshiftRight 1).setWidth 20) - 4#20).signExtend 64 <<< (1 : Nat)) = pc + a := by
  rw [far_offset_prefix8 a range aligned]
  exact prefix_pc pc a 8#64

end Flapjack.RiscV.TargetProof.JumpCmp

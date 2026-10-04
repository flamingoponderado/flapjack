import Mathlib.Tactic.IntervalCases
import Flapjack.RiscV.L3.Defs.Encode
import Flapjack.RiscV.L3.Step.DecodeAny

/-! Unrestricted conditional-branch Encode/DecodeAny compositions. Local
composition infrastructure without separately named HOL original theorems.
The original SBtype scatters all twelve logical halfword-offset bits as
imm11/imm9..4/rs2/rs1/funct3/imm3..0/imm10/opcode. asImm12 reconstructs
imm11/imm10/imm9..4/imm3..0. No decoder or execution premise, register
restriction, alignment premise or offset restriction is introduced. Full
JumpCmp encoder correctness remains separate work. -/

namespace Flapjack.RiscV.L3
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

private theorem reconstruct5 (w : BitVec 5) : holV2w 5 [w.getLsbD 4, w.getLsbD 3, w.getLsbD 2, w.getLsbD 1, w.getLsbD 0] = w := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [holV2w, Flapjack.getLsbD_holFcpWord]
  interval_cases i <;> simp

private theorem getElem_fcp {width : Nat} (P : Nat → Bool) (i : Nat)
    (hi : i < width) : (Flapjack.holFcpWord (width := width) P)[i] = P i := by
  simpa [hi] using Flapjack.getLsbD_holFcpWord (width := width) P i


/-- Actual native composition for every intrinsic register and offset. -/
theorem decode_encode_beq (rs1 rs2 : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.Branch (.BEQ (rs1, rs2, imm))))) =
      .Branch (.BEQ (rs1, rs2, imm)) := by
  simp only [Step.DecodeAny, Encode, SBtype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  refine ⟨by simpa using reconstruct5 rs1, by simpa using reconstruct5 rs2, ?_⟩
  have test4 (n j : Nat) : (n % 16).testBit j =
      (decide (j < 4) && n.testBit j) := Nat.testBit_mod_two_pow n 4 j
  have test6 (n j : Nat) : (n % 64).testBit j =
      (decide (j < 6) && n.testBit j) := Nat.testBit_mod_two_pow n 6 j
  simp only [asImm12, BitVec.setWidth_eq]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_append]
  interval_cases i
  all_goals simp only [holV2w, getElem_fcp, Flapjack.getLsbD_holFcpWord]
  all_goals simp
  all_goals simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat,
    test4, test6, Nat.testBit_shiftRight]
  all_goals simp

/-- Actual native composition for every intrinsic register and offset. -/
theorem decode_encode_bne (rs1 rs2 : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.Branch (.BNE (rs1, rs2, imm))))) =
      .Branch (.BNE (rs1, rs2, imm)) := by
  simp only [Step.DecodeAny, Encode, SBtype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  refine ⟨by simpa using reconstruct5 rs1, by simpa using reconstruct5 rs2, ?_⟩
  have test4 (n j : Nat) : (n % 16).testBit j =
      (decide (j < 4) && n.testBit j) := Nat.testBit_mod_two_pow n 4 j
  have test6 (n j : Nat) : (n % 64).testBit j =
      (decide (j < 6) && n.testBit j) := Nat.testBit_mod_two_pow n 6 j
  simp only [asImm12, BitVec.setWidth_eq]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_append]
  interval_cases i
  all_goals simp only [holV2w, getElem_fcp, Flapjack.getLsbD_holFcpWord]
  all_goals simp
  all_goals simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat,
    test4, test6, Nat.testBit_shiftRight]
  all_goals simp

/-- Actual native composition for every intrinsic register and offset. -/
theorem decode_encode_blt (rs1 rs2 : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.Branch (.BLT (rs1, rs2, imm))))) =
      .Branch (.BLT (rs1, rs2, imm)) := by
  simp only [Step.DecodeAny, Encode, SBtype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  refine ⟨by simpa using reconstruct5 rs1, by simpa using reconstruct5 rs2, ?_⟩
  have test4 (n j : Nat) : (n % 16).testBit j =
      (decide (j < 4) && n.testBit j) := Nat.testBit_mod_two_pow n 4 j
  have test6 (n j : Nat) : (n % 64).testBit j =
      (decide (j < 6) && n.testBit j) := Nat.testBit_mod_two_pow n 6 j
  simp only [asImm12, BitVec.setWidth_eq]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_append]
  interval_cases i
  all_goals simp only [holV2w, getElem_fcp, Flapjack.getLsbD_holFcpWord]
  all_goals simp
  all_goals simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat,
    test4, test6, Nat.testBit_shiftRight]
  all_goals simp

/-- Actual native composition for every intrinsic register and offset. -/
theorem decode_encode_bltu (rs1 rs2 : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.Branch (.BLTU (rs1, rs2, imm))))) =
      .Branch (.BLTU (rs1, rs2, imm)) := by
  simp only [Step.DecodeAny, Encode, SBtype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  refine ⟨by simpa using reconstruct5 rs1, by simpa using reconstruct5 rs2, ?_⟩
  have test4 (n j : Nat) : (n % 16).testBit j =
      (decide (j < 4) && n.testBit j) := Nat.testBit_mod_two_pow n 4 j
  have test6 (n j : Nat) : (n % 64).testBit j =
      (decide (j < 6) && n.testBit j) := Nat.testBit_mod_two_pow n 6 j
  simp only [asImm12, BitVec.setWidth_eq]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_append]
  interval_cases i
  all_goals simp only [holV2w, getElem_fcp, Flapjack.getLsbD_holFcpWord]
  all_goals simp
  all_goals simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat,
    test4, test6, Nat.testBit_shiftRight]
  all_goals simp

/-- Actual native composition for every intrinsic register and offset. -/
theorem decode_encode_bge (rs1 rs2 : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.Branch (.BGE (rs1, rs2, imm))))) =
      .Branch (.BGE (rs1, rs2, imm)) := by
  simp only [Step.DecodeAny, Encode, SBtype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  refine ⟨by simpa using reconstruct5 rs1, by simpa using reconstruct5 rs2, ?_⟩
  have test4 (n j : Nat) : (n % 16).testBit j =
      (decide (j < 4) && n.testBit j) := Nat.testBit_mod_two_pow n 4 j
  have test6 (n j : Nat) : (n % 64).testBit j =
      (decide (j < 6) && n.testBit j) := Nat.testBit_mod_two_pow n 6 j
  simp only [asImm12, BitVec.setWidth_eq]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_append]
  interval_cases i
  all_goals simp only [holV2w, getElem_fcp, Flapjack.getLsbD_holFcpWord]
  all_goals simp
  all_goals simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat,
    test4, test6, Nat.testBit_shiftRight]
  all_goals simp

/-- Actual native composition for every intrinsic register and offset. -/
theorem decode_encode_bgeu (rs1 rs2 : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.Branch (.BGEU (rs1, rs2, imm))))) =
      .Branch (.BGEU (rs1, rs2, imm)) := by
  simp only [Step.DecodeAny, Encode, SBtype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  refine ⟨by simpa using reconstruct5 rs1, by simpa using reconstruct5 rs2, ?_⟩
  have test4 (n j : Nat) : (n % 16).testBit j =
      (decide (j < 4) && n.testBit j) := Nat.testBit_mod_two_pow n 4 j
  have test6 (n j : Nat) : (n % 64).testBit j =
      (decide (j < 6) && n.testBit j) := Nat.testBit_mod_two_pow n 6 j
  simp only [asImm12, BitVec.setWidth_eq]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_append]
  interval_cases i
  all_goals simp only [holV2w, getElem_fcp, Flapjack.getLsbD_holFcpWord]
  all_goals simp
  all_goals simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat,
    test4, test6, Nat.testBit_shiftRight]
  all_goals simp
end Flapjack.RiscV.L3

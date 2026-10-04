import Mathlib.Tactic.IntervalCases
import Flapjack.RiscV.L3.Defs.Encode
import Flapjack.RiscV.L3.Step.DecodeAny

/-! Unrestricted native JAL/JALR Encode and DecodeAny compositions.
These are local composition infrastructure, with no separately named HOL
original theorem. Original UJtype keeps imm19, imm9..0, imm10, imm18..11,
rd4..0 and opcode bits; asImm20 reconstructs imm19/18..11/10/9..0.
JALR uses the exact Itype rs/rd/imm12 layout. Every intrinsic word5 register,
word20 logical halfword offset and word12 byte offset is retained, including
zero/all-ones, signed offsets and rd=rs. No target-run or decoder premise and
no artificial register/offset restriction is added. These identities supply
native Jump/Call/far JumpCmp prerequisites; full encoder cases remain open. -/

namespace Flapjack.RiscV.L3
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

private theorem reconstruct5 (w : BitVec 5) : holV2w 5 [w.getLsbD 4, w.getLsbD 3, w.getLsbD 2, w.getLsbD 1, w.getLsbD 0] = w := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [holV2w, Flapjack.getLsbD_holFcpWord]
  interval_cases i <;> simp

private theorem reconstruct12 (w : BitVec 12) : holV2w 12 [w.getLsbD 11, w.getLsbD 10, w.getLsbD 9, w.getLsbD 8, w.getLsbD 7, w.getLsbD 6, w.getLsbD 5, w.getLsbD 4, w.getLsbD 3, w.getLsbD 2, w.getLsbD 1, w.getLsbD 0] = w := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [holV2w, Flapjack.getLsbD_holFcpWord]
  interval_cases i <;> simp


private theorem getElem_fcp {width : Nat} (P : Nat → Bool) (i : Nat)
    (hi : i < width) : (Flapjack.holFcpWord (width := width) P)[i] = P i := by
  simpa [hi] using Flapjack.getLsbD_holFcpWord (width := width) P i

/-- Full actual native decoder composition, including aliased link/source
registers. No separately named HOL original, so this remains untagged. -/
theorem decode_encode_jalr (rd rs : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.Branch (.JALR (rd,rs,imm))))) =
      .Branch (.JALR (rd,rs,imm)) := by
  simp only [Step.DecodeAny, Encode, Itype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct5 rs,
    by simpa using reconstruct12 imm⟩

/-- Full actual native decoder composition of the scattered JAL immediate.
No separately named HOL original, so this remains untagged. -/
theorem decode_encode_jal (rd : BitVec 5) (imm : BitVec 20) :
    Step.DecodeAny (.Word (Encode (.Branch (.JAL (rd,imm))))) =
      .Branch (.JAL (rd,imm)) := by
  simp only [Step.DecodeAny,Encode,UJtype,opc,BitVec.setWidth_eq]
  simp only [Decode,boolify32,BitVec.getLsbD_append]
  simp [holWordExtract]
  constructor
  · simpa using reconstruct5 rd
  · have test8 (n j : Nat) : (n % 256).testBit j =
        (decide (j < 8) && n.testBit j) := Nat.testBit_mod_two_pow n 8 j
    have test10 (n j : Nat) : (n % 1024).testBit j =
        (decide (j < 10) && n.testBit j) := Nat.testBit_mod_two_pow n 10 j
    simp only [asImm20,BitVec.setWidth_eq]
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    simp only [BitVec.getLsbD_append]
    interval_cases i
    all_goals simp only [holV2w,getElem_fcp,Flapjack.getLsbD_holFcpWord]
    all_goals simp
    all_goals simp only [BitVec.getElem_eq_testBit_toNat,BitVec.toNat_ofNat,
      test8,test10,Nat.testBit_shiftRight]
    all_goals simp
end Flapjack.RiscV.L3

import Mathlib.Tactic.IntervalCases
import Flapjack.Misc.Alignment
import Flapjack.RiscV.L3.Defs.Encode
import Flapjack.RiscV.L3.Step.DecodeAny

/-! Full native memory encoder decoder compositions. Source comparison:
original LD/LBU/LHU/LWU use Itype opcode0000011 and funct3=011/100/101/110.
SD/SW/SH/SB use Stype opcode0100011 and funct3=011/010/001/000;
offset high7/low5 is reassembled in original decoder order. Every intrinsic
word5 register and word12 offset is unrestricted. There is no separately named
HOL declaration for this composed fact, so the infrastructure is untagged. -/

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

private theorem reconstruct7 (w : BitVec 7) : holV2w 7 [w.getLsbD 6, w.getLsbD 5, w.getLsbD 4, w.getLsbD 3, w.getLsbD 2, w.getLsbD 1, w.getLsbD 0] = w := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [holV2w, Flapjack.getLsbD_holFcpWord]
  interval_cases i <;> simp

private theorem simm_reconstruct (w : BitVec 12) :
    asSImm12 (holWordExtract 7 11 5 w, holWordExtract 5 4 0 w) = w := by
  have high : holWordExtract 7 11 5 w = w.extractLsb' 5 7 := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.extractLsb'_toNat]
  have low : holWordExtract 5 4 0 w = w.extractLsb' 0 5 := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.extractLsb'_toNat]
  simp only [asSImm12, BitVec.setWidth_eq, high, low]
  exact BitVec.extractLsb'_append_extractLsb'

/-- Original native Encode/Decode composition for LD. No separately named
HOL original; all fields are unrestricted and no target-run premise is assumed. -/
theorem decode_encode_ld (r1 r2 : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.Load (.LD (r1, r2, imm))))) =
      .Load (.LD (r1, r2, imm)) := by
  simp only [Step.DecodeAny, Encode, Itype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 r1, by simpa using reconstruct5 r2, by simpa using reconstruct12 imm⟩

/-- Original native Encode/Decode composition for LWU. No separately named
HOL original; all fields are unrestricted and no target-run premise is assumed. -/
theorem decode_encode_lwu (r1 r2 : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.Load (.LWU (r1, r2, imm))))) =
      .Load (.LWU (r1, r2, imm)) := by
  simp only [Step.DecodeAny, Encode, Itype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 r1, by simpa using reconstruct5 r2, by simpa using reconstruct12 imm⟩

/-- Original native Encode/Decode composition for LHU. No separately named
HOL original; all fields are unrestricted and no target-run premise is assumed. -/
theorem decode_encode_lhu (r1 r2 : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.Load (.LHU (r1, r2, imm))))) =
      .Load (.LHU (r1, r2, imm)) := by
  simp only [Step.DecodeAny, Encode, Itype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 r1, by simpa using reconstruct5 r2, by simpa using reconstruct12 imm⟩

/-- Original native Encode/Decode composition for LBU. No separately named
HOL original; all fields are unrestricted and no target-run premise is assumed. -/
theorem decode_encode_lbu (r1 r2 : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.Load (.LBU (r1, r2, imm))))) =
      .Load (.LBU (r1, r2, imm)) := by
  simp only [Step.DecodeAny, Encode, Itype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 r1, by simpa using reconstruct5 r2, by simpa using reconstruct12 imm⟩

/-- Original native Encode/Decode composition for SD. No separately named
HOL original; all fields are unrestricted and no target-run premise is assumed. -/
theorem decode_encode_sd (r1 r2 : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.Store (.SD (r1, r2, imm))))) =
      .Store (.SD (r1, r2, imm)) := by
  simp only [Step.DecodeAny, Encode, Stype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append,
    show holWordExtract 5 4 0 (8#8) = 8#5 from rfl]
  simp
  refine ⟨by simpa using reconstruct5 r1, by simpa using reconstruct5 r2, ?_⟩
  have high := reconstruct7 (holWordExtract 7 11 5 imm)
  have low := reconstruct5 (holWordExtract 5 4 0 imm)
  simp at high low
  rw [high, low]
  exact simm_reconstruct imm

/-- Original native Encode/Decode composition for SW. No separately named
HOL original; all fields are unrestricted and no target-run premise is assumed. -/
theorem decode_encode_sw (r1 r2 : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.Store (.SW (r1, r2, imm))))) =
      .Store (.SW (r1, r2, imm)) := by
  simp only [Step.DecodeAny, Encode, Stype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append,
    show holWordExtract 5 4 0 (8#8) = 8#5 from rfl]
  simp
  refine ⟨by simpa using reconstruct5 r1, by simpa using reconstruct5 r2, ?_⟩
  have high := reconstruct7 (holWordExtract 7 11 5 imm)
  have low := reconstruct5 (holWordExtract 5 4 0 imm)
  simp at high low
  rw [high, low]
  exact simm_reconstruct imm

/-- Original native Encode/Decode composition for SH. No separately named
HOL original; all fields are unrestricted and no target-run premise is assumed. -/
theorem decode_encode_sh (r1 r2 : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.Store (.SH (r1, r2, imm))))) =
      .Store (.SH (r1, r2, imm)) := by
  simp only [Step.DecodeAny, Encode, Stype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append,
    show holWordExtract 5 4 0 (8#8) = 8#5 from rfl]
  simp
  refine ⟨by simpa using reconstruct5 r1, by simpa using reconstruct5 r2, ?_⟩
  have high := reconstruct7 (holWordExtract 7 11 5 imm)
  have low := reconstruct5 (holWordExtract 5 4 0 imm)
  simp at high low
  rw [high, low]
  exact simm_reconstruct imm

/-- Original native Encode/Decode composition for SB. No separately named
HOL original; all fields are unrestricted and no target-run premise is assumed. -/
theorem decode_encode_sb (r1 r2 : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.Store (.SB (r1, r2, imm))))) =
      .Store (.SB (r1, r2, imm)) := by
  simp only [Step.DecodeAny, Encode, Stype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append,
    show holWordExtract 5 4 0 (8#8) = 8#5 from rfl]
  simp
  refine ⟨by simpa using reconstruct5 r1, by simpa using reconstruct5 r2, ?_⟩
  have high := reconstruct7 (holWordExtract 7 11 5 imm)
  have low := reconstruct5 (holWordExtract 5 4 0 imm)
  simp at high low
  rw [high, low]
  exact simm_reconstruct imm

end Flapjack.RiscV.L3

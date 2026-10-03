import Mathlib.Tactic.IntervalCases
import Flapjack.Misc.Alignment
import Flapjack.RiscV.L3.Defs.Encode
import Flapjack.RiscV.L3.Step.DecodeAny

/-! Source audit: pinned riscvScript.sml Itype_def (18997) concatenates
imm[11:0], rs[4:0], funct3=000, rd[4:0], opcode=0010011.
The Decode ADDI clause (15190) reconstructs rd from bits11..7, rs from
19..15 and imm from31..20. The proof below follows those exact clauses;
register zero and every immediate sign bit are unrestricted. -/

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

/-- Full native ADDI decoding infrastructure. No separately named HOL original:
this proves the composition of the reviewed original Encode and Decode clauses
for every intrinsic register and immediate field, without input premises. -/
theorem decode_encode_addi (rd rs : BitVec 5) (imm : BitVec 12) :
    Step.DecodeAny (.Word (Encode (.ArithI (.ADDI (rd, rs, imm))))) =
      .ArithI (.ADDI (rd, rs, imm)) := by
  simp only [Step.DecodeAny, Encode, Itype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct5 rs, by simpa using reconstruct12 imm⟩

end Flapjack.RiscV.L3

import Flapjack.RiscV.CorrectnessEncoding.DecodeBinop

/-! Actual native MULHU/MUL Encode/DecodeAny composition, required by the original
LongMul encoder correctness case. Original MULHU/MUL use opcode0110011, funct3=011/000
and funct7=0000001; all three intrinsic word5 registers remain unrestricted.
No separately named HOL theorem states this composition, so it is untagged
Flapjack proof infrastructure. -/
namespace Flapjack.RiscV.L3
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

private theorem reconstruct5 (w : BitVec 5) : holV2w 5 [w.getLsbD 4, w.getLsbD 3, w.getLsbD 2, w.getLsbD 1, w.getLsbD 0] = w := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [holV2w, Flapjack.getLsbD_holFcpWord]
  interval_cases i <;> simp

/-- Unrestricted composition of the actual native MULHU Encode and DecodeAny
clauses. Used by original LongMul lowering, with arbitrary zero/alias registers.
No separately named HOL theorem exists for this evaluator composition. -/
theorem decode_encode_mulhu (rd rs1 rs2 : BitVec 5) :
    Step.DecodeAny (.Word (Encode (.MulDiv (.MULHU (rd, rs1, rs2))))) =
      .MulDiv (.MULHU (rd, rs1, rs2)) := by
  simp only [Step.DecodeAny, Encode, Rtype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct5 rs1,
    by simpa using reconstruct5 rs2⟩

/-- Unrestricted composition of the actual native MUL Encode and DecodeAny
clauses. Used by original LongMul lowering, with arbitrary zero/alias registers.
No separately named HOL theorem exists for this evaluator composition. -/
theorem decode_encode_mul (rd rs1 rs2 : BitVec 5) :
    Step.DecodeAny (.Word (Encode (.MulDiv (.MUL (rd, rs1, rs2))))) =
      .MulDiv (.MUL (rd, rs1, rs2)) := by
  simp only [Step.DecodeAny, Encode, Rtype, opc, BitVec.setWidth_eq]
  simp only [Decode, boolify32, BitVec.getLsbD_append]
  simp [holWordExtract]
  exact ⟨by simpa using reconstruct5 rd, by simpa using reconstruct5 rs1,
    by simpa using reconstruct5 rs2⟩

end Flapjack.RiscV.L3

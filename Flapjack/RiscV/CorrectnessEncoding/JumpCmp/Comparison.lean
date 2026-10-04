import Flapjack.RiscV.CorrectnessEncoding.JumpCmp.Source
import Flapjack.RiscV.CorrectnessEncoding.ConstNext

/-! Source word_cmp/native branch correspondence for the six simple
comparison forms. Test/NotTest require their actual AND/ANDI prefix and remain
separate cases. Untagged local composition with no named HOL original. -/
namespace Flapjack.RiscV.TargetProof.JumpCmp
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target
theorem signed_less (left right : BitVec 64) :
    holAsmSignedLess left right = left.slt right := by
  have bl := left.isLt
  have br := right.isLt
  simp only [holAsmSignedLess,BitVec.slt_eq_decide,BitVec.toInt_eq_msb_cond,
    BitVec.msb_eq_decide]
  repeat (any_goals first | split)
  all_goals simp_all only [decide_eq_true_eq]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp_all [decide_eq_true_eq]
  all_goals omega
def simple_branch (c : Cmp) (r s : BitVec 5) (imm : BitVec 12) : instruction :=
  match c with
  | .equal | .test => .Branch (.BEQ (r,s,imm))
  | .less => .Branch (.BLT (r,s,imm))
  | .lower => .Branch (.BLTU (r,s,imm))
  | .notEqual | .notTest => .Branch (.BNE (r,s,imm))
  | .notLess => .Branch (.BGE (r,s,imm))
  | .notLower => .Branch (.BGEU (r,s,imm))
theorem simple_branch_next (c : Cmp) (r s : BitVec 5) (imm : BitVec 12)
    (ms : riscv_state) (ok : riscvOk ms = true)
    (simple : c ≠ .test ∧ c ≠ .notTest)
    (bytes : encodedInstructionBytes ms (simple_branch c r s imm)) :
    NextRISCV ms = some (Jump.branchPost ms
      (if wordCmpHOL c (GPR r ms) (GPR s ms) then
        ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat)) else
        ms.c_PC ms.procID+4)) := by
  cases c
  case test => exact False.elim (simple.1 rfl)
  case notTest => exact False.elim (simple.2 rfl)
  case equal =>
    simpa [wordCmpHOL,beq_iff_eq] using beq_next ms r s imm ok bytes.1 bytes.2.1 bytes.2.2.1 bytes.2.2.2
  case less =>
    simpa [wordCmpHOL,signed_less] using blt_next ms r s imm ok bytes.1 bytes.2.1 bytes.2.2.1 bytes.2.2.2
  case lower =>
    simpa [wordCmpHOL,BitVec.ult_eq_decide_lt] using bltu_next ms r s imm ok bytes.1 bytes.2.1 bytes.2.2.1 bytes.2.2.2
  case notEqual =>
    simpa [wordCmpHOL,beq_iff_eq] using bne_next ms r s imm ok bytes.1 bytes.2.1 bytes.2.2.1 bytes.2.2.2
  case notLess =>
    simpa [wordCmpHOL,signed_less,BitVec.slt_eq_decide,BitVec.sle_eq_decide,not_lt] using bge_next ms r s imm ok bytes.1 bytes.2.1 bytes.2.2.1 bytes.2.2.2
  case notLower =>
    simpa [wordCmpHOL,BitVec.ult_eq_decide_lt] using bgeu_next ms r s imm ok bytes.1 bytes.2.1 bytes.2.2.1 bytes.2.2.2

/-- The Test branches compare the actual AND/ANDI result against native zero.
The scratch-value premise is discharged by the executed prefix and interference
projection; this helper is not the tagged full constructor theorem. -/
theorem test_branch_next (c : Cmp) (left right : BitVec 64)
    (imm : BitVec 12) (ms : riscv_state) (ok : riscvOk ms = true)
    (test : c = .test ∨ c = .notTest)
    (scratch : GPR (31#5) ms = left &&& right)
    (bytes : encodedInstructionBytes ms (simple_branch c (31#5) (0#5) imm)) :
    NextRISCV ms = some (Jump.branchPost ms
      (if wordCmpHOL c left right then
        ms.c_PC ms.procID + (imm.signExtend 64 <<< (1 : Nat)) else
        ms.c_PC ms.procID + 4)) := by
  have raw : ms.c_gpr ms.procID (31#5) = left &&& right := by
    simpa [GPR, gpr] using scratch
  rcases test with rfl | rfl
  · simpa [wordCmpHOL, raw, GPR, gpr, beq_iff_eq, AndOp.and] using
      beq_next ms (31#5) (0#5) imm ok bytes.1 bytes.2.1 bytes.2.2.1 bytes.2.2.2
  · simpa [wordCmpHOL, raw, GPR, gpr, beq_iff_eq, AndOp.and] using
      bne_next ms (31#5) (0#5) imm ok bytes.1 bytes.2.1 bytes.2.2.1 bytes.2.2.2

end Flapjack.RiscV.TargetProof.JumpCmp

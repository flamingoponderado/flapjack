import Flapjack.RiscV.CorrectnessEncoding.JumpCmp.Native

/-! Local original JumpCmp source guard/read/post-state compositions.
No separate HOL declaration is claimed; assembling correctness derives all
these facts from the actual original asmStep and initial target relation. -/
namespace Flapjack.RiscV.TargetProof.JumpCmp
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target
theorem source_guard (c : Cmp) (r : Nat) (ri : HolRegImm 64) (a : BitVec 64)
    (h : asmOkExact (.jumpCmp c r ri a) riscvConfig = true) :
    (-1048568 ≤ a.toInt ∧ a.toInt ≤ 1048579) ∧ a.toNat % 4 = 0 ∧
      asmRegOkExact r riscvConfig = true ∧ asmRegImmOkExact (.inr c) ri riscvConfig = true := by
  have original := h
  simp only [asmOkExact,asmCmpOkExact,Bool.and_eq_true] at original
  have offset := original.1
  simp only [asmCjumpOffsetOkExact,asmOffsetOkExact,asmAligned,Bool.and_eq_true] at offset
  have lo : riscvConfig.cjumpOffset.1.toInt = -1048568 := by decide
  have hi : riscvConfig.cjumpOffset.2.toInt = 1048579 := by decide
  have align : riscvConfig.codeAlignment = 2 := rfl
  rw [lo,hi,align] at offset
  exact ⟨⟨of_decide_eq_true offset.1.1,of_decide_eq_true offset.1.2⟩,
    of_decide_eq_true offset.2,original.2⟩
theorem reg_nonzero (r : Nat) (guard : asmRegOkExact r riscvConfig = true) :
    BitVec.ofNat 5 r ≠ 0#5 := by
  have g : r < 32 ∧ r ≠ 0 := by
    have g := guard
    simp [asmRegOkExact,riscvConfig] at g
    exact ⟨of_decide_eq_true g.1,g.2.1⟩
  intro eq
  have n := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat] at n
  norm_num at n
  rw [Nat.mod_eq_of_lt g.1] at n
  exact g.2 n
theorem reg_read (r : Nat) (s : AsmState 64) (ms : riscv_state)
    (guard : asmRegOkExact r riscvConfig = true)
    (rel : targetStateRel riscvTarget s ms) :
    GPR (BitVec.ofNat 5 r) ms = readReg r s := by
  have g : r < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains r = false := by
    simpa [asmRegOkExact] using guard
  have before := rel.2.2.2.1 r g
  change ms.c_gpr ms.procID (BitVec.ofNat 5 r) = s.regs r at before
  simpa [GPR,gpr,reg_nonzero r guard,readReg] using before
theorem source_post (c : Cmp) (r : Nat) (ri : HolRegImm 64) (a : BitVec 64)
    (s1 s2 : AsmState 64) (h : asmStep riscvConfig s1 (.jumpCmp c r ri a) s2) :
    s2 = if wordCmpHOL c (readReg r s1) (regImm ri s1) then
      updPc (s1.pc+a) s1 else
      updPc (s1.pc+BitVec.ofNat 64 (riscvConfig.encode (.jumpCmp c r ri a)).length) s1 := by
  simpa [asmUpd,jumpToOffset] using h.2.2.2.2.1.symm


/-- Immediate guard extracted from the original comparison asm_ok. -/
theorem immediate_bounds (cmp : Cmp) (c : BitVec 64)
    (h : asmRegImmOkExact (.inr cmp) (.imm c) riscvConfig = true) :
    -2048 ≤ c.toInt ∧ c.toInt ≤ 2047 := by
  have different : ((Sum.inr cmp : Sum BinOp Cmp) == .inl .xor) = false := by
    cases cmp <;> rfl
  simpa [asmRegImmOkExact, different, riscvConfig, BitVec.sle_eq_decide,
    decide_eq_true_eq] using h

/-- Reconstruction used by the executed ORI/ANDI prefix, with the original
signed12 guard; the full case derives this guard from asmStep. -/
theorem immediate_reconstruct (c : BitVec 64)
    (bounds : -2048 ≤ c.toInt ∧ c.toInt ≤ 2047) :
    (c.setWidth 12).signExtend 64 = c := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide : 12 ≤ 64)]
  have et := BitVec.toInt_signExtend_eq_toInt_bmod_of_le c (by decide : 12 ≤ 64)
  rw [BitVec.signExtend_eq_setWidth_of_le c (by decide : 12 ≤ 64)] at et
  rw [et]
  apply Int.bmod_eq_of_le <;> omega

end Flapjack.RiscV.TargetProof.JumpCmp

import Flapjack.Mips32.TargetProof.Branch
import Mathlib.Tactic.NormNum

/-! # `encoder_correct mips32Target`: arithmetic and constant instructions -/

namespace Flapjack.Mips32.TargetProof
open ZirenDet.Isa Flapjack Flapjack.Mips32 Flapjack.Compiler.Encoders.Mips32
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps

theorem zext_lo16 (i : W) (h1 : (0 : W).sle i = true) (h2 : i.sle 0xFFFF = true) :
    zext16 (lo16 i) = i := by
  simp only [zext16, lo16]
  simp only [BitVec.sle, decide_eq_true_eq] at h1 h2
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat]
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond] at *
  simp at h1 h2
  split at h1 <;> split at h2 <;> omega

theorem sext_lo16 (i : W) (h1 : (-32768 : W).sle i = true) (h2 : i.sle 32767 = true) :
    sext16 (lo16 i) = i := by
  simp only [sext16, lo16]
  simp only [BitVec.sle, decide_eq_true_eq] at h1 h2
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide)]
  rw [BitVec.toInt_eq_toNat_cond (BitVec.extractLsb' 0 16 i)]
  simp only [BitVec.extractLsb'_toNat]
  rw [BitVec.toInt_eq_toNat_cond] at *
  have : (-32768 : W).toNat = 4294934528 := by decide
  have : (32767 : W).toNat = 32767 := by decide
  simp_all
  try rw [BitVec.toInt_eq_toNat_cond] at h1
  have := i.isLt
  split at h1 <;> split at h2 <;> (repeat' split) <;> omega

theorem neg_range (i : W) (h1 : (-32768 : W).slt i = true) (h2 : i.sle 32767 = true) :
    (-32768 : W).sle (-i) = true ∧ (-i).sle 32767 = true := by
  simp only [BitVec.slt, BitVec.sle, decide_eq_true_eq] at *
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond] at *
  have : (-32768 : W).toNat = 4294934528 := by decide
  have : (32767 : W).toNat = 32767 := by decide
  simp only [BitVec.toNat_neg] at *
  simp_all
  have := i.isLt
  split at h1 <;> split at h2 <;> (repeat' split) <;> omega

theorem case_skip (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst .skip) s2 ∧ targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst .skip) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hs2 := st.upd
  simp only [asmUpd, instUpd, updPc] at hs2
  subst hs2
  apply straightCase' _ _ _ _ st rfl
  · simp [mips32Ast, plain_nop]
  · simp [mips32Ast]
  · simp [mips32Ast, touched, nop]
  · rfl
  · intro a ha; simp [mips32Ast, exec_nop]; exact st.mem a ha
  · intro r hr; simp [mips32Ast, exec_nop]; exact st.reg r hr.lt hr.avoid

theorem case_binop_reg (bop : BinOp) (r1 r2 r3 : Nat) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.arith (.binop bop r1 r2 (.reg r3)))) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.arith (.binop bop r1 r2 (.reg r3)))) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, asmRegImmOkExact, Bool.and_eq_true] at hok
  have o1 := regOk_of_asm hok.1.1.2
  have o2 := regOk_of_asm hok.1.2
  have o3 := regOk_of_asm hok.2
  have hs2 := st.upd
  simp only [asmUpd, instUpd, arithUpd, binopUpd, updPc, updReg, readReg, regImm] at hs2
  subst hs2
  apply straightCase' _ _ _ _ st rfl
  · cases bop <;> simp [mips32Ast] <;> exact plain_of_sequential _ rfl
  · cases bop <;> simp [mips32Ast]
  · cases bop <;> simp [mips32Ast, touched]
  · rfl
  · intro a _
    cases bop <;> simp [mips32Ast, exec, setReg_mem] <;> exact st.mem a ‹_›
  · intro r hr
    cases bop <;>
    simp only [mips32Ast, List.foldl_cons, List.foldl_nil, exec, alu, reg_setReg, reg_mk_gpr,
      hr.regOf_ne_zero, regOf_inj hr.lt o1.lt, st.reg _ o2.lt o2.avoid, st.reg _ o3.lt o3.avoid,
      st.reg _ hr.lt hr.avoid] <;> simp [Opc.ADD, Opc.SUB, Opc.AND, Opc.OR, Opc.XOR]

theorem case_binop_imm (bop : BinOp) (r1 r2 : Nat) (i : W) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.arith (.binop bop r1 r2 (.imm i)))) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.arith (.binop bop r1 r2 (.imm i)))) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, asmRegImmOkExact, Bool.and_eq_true,
    Bool.or_eq_true] at hok
  have o1 := regOk_of_asm hok.1.1.2
  have o2 := regOk_of_asm hok.1.2
  have himm := hok.2
  have hs2 := st.upd
  simp only [asmUpd, instUpd, arithUpd, binopUpd, updPc, updReg, readReg, regImm] at hs2
  subst hs2
  apply straightCase' _ _ _ _ st rfl
  · cases bop <;> simp only [mips32Ast] <;> (try split) <;> simp <;> exact plain_of_sequential _ rfl
  · cases bop <;> simp [mips32Ast]
    split <;> simp
  · cases bop <;> simp [mips32Ast] <;> (try split) <;> simp [touched]
  · rfl
  · intro a _
    cases bop <;> simp only [mips32Ast] <;> (try split) <;>
      simp [exec, setReg_mem] <;> exact st.mem a ‹_›
  · intro r hr
    have hr' := st.reg _ hr.lt hr.avoid
    have h2 := st.reg _ o2.lt o2.avoid
    have fin : ∀ (x : Insn) (v : W), exec ms x =
        ({ ms with pc := ms.nextPc, nextPc := ms.nextPc + 4 } : State).setReg (regOf r1) v →
        ((x :: []).foldl exec ms).reg (regOf r) = (if r = r1 then v else s1.regs r) := by
      intro x v hx
      simp only [List.foldl_cons, List.foldl_nil, hx, reg_setReg, reg_mk_gpr, hr.regOf_ne_zero,
        regOf_inj hr.lt o1.lt, hr', if_false]
    cases bop
    · have hv : (-32768 : W).sle i = true ∧ i.sle 32767 = true := by
        rcases himm with ⟨hx, -⟩ | hv
        · exact absurd hx (by decide)
        · simpa [mips32Config] using hv
      simp only [mips32Ast]
      rw [fin _ (s1.regs r2 + i) (by simp [exec, h2, sext_lo16 i hv.1 hv.2])]
    · have hv : (-32768 : W).slt i = true ∧ i.sle 32767 = true := by
        rcases himm with ⟨hx, -⟩ | hv
        · exact absurd hx (by decide)
        · simpa [mips32Config] using hv
      have hn := neg_range i hv.1 hv.2
      simp only [mips32Ast]
      rw [fin _ (s1.regs r2 - i) (by
        simp [exec, h2, sext_lo16 (-i) hn.1 hn.2, BitVec.sub_eq_add_neg])]
    · have hv : (0 : W).sle i = true ∧ i.sle 0xFFFF = true := by
        rcases himm with ⟨hx, -⟩ | hv
        · exact absurd hx (by decide)
        · simpa [mips32Config] using hv
      simp only [mips32Ast]
      rw [fin _ (s1.regs r2 &&& i) (by simp [exec, h2, zext_lo16 i hv.1 hv.2])]
    · have hv : (0 : W).sle i = true ∧ i.sle 0xFFFF = true := by
        rcases himm with ⟨hx, -⟩ | hv
        · exact absurd hx (by decide)
        · simpa [mips32Config] using hv
      simp only [mips32Ast]
      rw [fin _ (s1.regs r2 ||| i) (by simp [exec, h2, zext_lo16 i hv.1 hv.2])]
    · simp only [mips32Ast]
      by_cases hm : i = -1
      · simp only [hm, if_true]
        rw [fin _ (s1.regs r2 ^^^ -1) (by
          simp [exec, h2]
          congr 1
          rw [show (4294967295#32 : W) = BitVec.allOnes 32 by decide, BitVec.xor_allOnes])]
      · have hv : (0 : W).sle i = true ∧ i.sle 0xFFFF = true := by
          rcases himm with ⟨-, hx⟩ | hv
          · exact absurd (by simpa using hx) hm
          · simpa [mips32Config] using hv
        simp only [hm, if_false]
        rw [fin _ (s1.regs r2 ^^^ i) (by
          simp [exec, h2, zext_lo16 i hv.1 hv.2])]

theorem const_lo (i : W) (h : hi16 i = 0) : 0 ||| zext16 (lo16 i) = i := by
  have h' := congrArg BitVec.toNat h
  simp only [hi16, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at h'
  apply BitVec.eq_of_toNat_eq
  simp [zext16, lo16, BitVec.extractLsb'_toNat]
  have := i.isLt
  simp at h'
  omega

theorem const_full (i : W) : (zext16 (hi16 i) <<< 16) ||| zext16 (lo16 i) = i := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [zext16, hi16, lo16, BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
  by_cases h16 : j < 16
  · simp [h16, hj]
  · simp [h16, hj, show j - 16 < 16 by omega, show 16 + (j - 16) = j by omega]

theorem const_neg (i : W) (h : hi16 i = -1) (hm : (lo16 i).msb = true) :
    0 + sext16 (lo16 i) = i := by
  have hb : ∀ j, 16 ≤ j → j < 32 → i.getLsbD j = true := by
    intro j hj1 hj2
    have := congrArg (fun x : BitVec 16 => x.getLsbD (j - 16)) h
    simp only [hi16, BitVec.getLsbD_extractLsb'] at this
    rw [show 16 + (j - 16) = j by omega, show (-1 : BitVec 16) = BitVec.allOnes 16 by decide,
      BitVec.getLsbD_allOnes] at this
    simpa [show j - 16 < 16 by omega] using this
  have hm' : i.getLsbD 15 = true := by
    simpa [lo16, BitVec.msb_eq_getLsbD_last] using hm
  have e : (0 : W) + sext16 (lo16 i) = sext16 (lo16 i) := by simp
  rw [e]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [sext16, lo16, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb',
    BitVec.msb_eq_getLsbD_last]
  by_cases h16 : j < 16
  · simp [h16, hj]
  · simp [h16, hj]
    simp only [← BitVec.getLsbD_eq_getElem, hm', hb j (by omega) hj]


theorem case_const (r : Nat) (i : W) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.const r i)) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.const r i)) s1 s2 ms := by
  have st := start _ _ _ _ h
  have o := regOk_of_asm (by simpa [asmOkExact, asmInstOkExact] using st.asmOk)
  have hs2 := st.upd
  simp only [asmUpd, instUpd, updPc, updReg] at hs2
  subst hs2
  apply straightCase' _ _ _ _ st rfl
  · simp only [mips32Ast]; split_ifs <;> simp <;>
      first | exact plain_of_sequential _ rfl | exact ⟨plain_of_sequential _ rfl, plain_of_sequential _ rfl⟩
  · simp only [mips32Ast]; split_ifs <;> simp; exact noWrite_of_writes _ rfl
  · apply htouch_of_noMem; simp only [mips32Ast]; split_ifs <;> simp [insnNoMem]
  · rfl
  · intro a ha
    simp only [mips32Ast]; split_ifs <;> simp [exec, setReg_mem] <;> exact st.mem a ha
  · intro r' hr
    have hr' := st.reg _ hr.lt hr.avoid
    simp only [mips32Ast]
    by_cases h1 : hi16 i = 0
    · rw [if_pos h1]
      have e : zext16 (lo16 i) = i := by simpa using const_lo i h1
      simp [exec, reg_setReg, hr.regOf_ne_zero, regOf_inj hr.lt o.lt, hr', e]
    rw [if_neg h1]
    by_cases h2 : hi16 i = -1 ∧ (lo16 i).msb
    · rw [if_pos h2]
      have e : sext16 (lo16 i) = i := by simpa using const_neg i h2.1 h2.2
      simp [exec, reg_setReg, hr.regOf_ne_zero, regOf_inj hr.lt o.lt, hr', e]
    · rw [if_neg h2]
      have e := const_full i
      simp only [List.foldl_cons, List.foldl_nil, exec, reg_setReg, reg_mk_gpr, hr.regOf_ne_zero,
        regOf_inj hr.lt o.lt, hr', o.regOf_ne_zero, alu_or, if_false, if_true]
      by_cases hrr : r' = r
      · simp [hrr]; exact e
      · simp [hrr]

theorem shamt_imm (i : W) (h : i.toNat < 32) :
    (((i.setWidth 5).zeroExtend 32).extractLsb' 0 5).toNat = i.toNat := by
  simp [BitVec.extractLsb'_toNat]; omega

theorem shamt_reg (v : W) (h : v.toNat < 32) : (v.extractLsb' 0 5).toNat = v.toNat := by
  simp [BitVec.extractLsb'_toNat]; omega

theorem case_shift_imm (sh : Flapjack.Shift) (r1 r2 : Nat) (i : W) (s1 s2 : AsmState 32)
    (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.arith (.shift sh r1 r2 (.imm i)))) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.arith (.shift sh r1 r2 (.imm i)))) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, Bool.and_eq_true] at hok
  have o1 := regOk_of_asm hok.1.1.2
  have o2 := regOk_of_asm hok.1.2
  have hi : i.toNat < 32 := by simpa using hok.2.2
  have hs2 := st.upd
  simp only [asmUpd, instUpd, arithUpd, updPc, updReg, readReg, regImm, assertState] at hs2
  subst hs2
  apply straightCase' _ _ _ _ st rfl
  · cases sh <;> simp [mips32Ast] <;> exact plain_of_sequential _ rfl
  · cases sh <;> simp [mips32Ast]
  · apply htouch_of_noMem; cases sh <;> simp [mips32Ast, insnNoMem]
  · rfl
  · intro a ha; cases sh <;> simp [mips32Ast, exec, setReg_mem] <;> exact st.mem a ha
  · intro r hr
    have hr' := st.reg _ hr.lt hr.avoid
    have h2 := st.reg _ o2.lt o2.avoid
    cases sh <;>
      simp [mips32Ast, exec, reg_setReg, hr.regOf_ne_zero, regOf_inj hr.lt o1.lt, hr', h2,
        shamt_imm i hi, wordShift]

theorem case_shift_reg (sh : Flapjack.Shift) (r1 r2 r3 : Nat) (s1 s2 : AsmState 32)
    (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.arith (.shift sh r1 r2 (.reg r3)))) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.arith (.shift sh r1 r2 (.reg r3)))) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, Bool.and_eq_true] at hok
  have o1 := regOk_of_asm hok.1.1.2
  have o2 := regOk_of_asm hok.1.2
  have o3 := regOk_of_asm hok.2.1
  have hs2 := st.upd
  have hfail := st.ok
  simp only [asmUpd, instUpd, arithUpd, updPc, updReg, readReg, regImm, assertState] at hs2
  subst hs2
  have hlt : (s1.regs r3).toNat < 32 := by
    have := st.ok
    simp at this
    exact of_decide_eq_true this.1
  apply straightCase' _ _ _ _ st rfl
  · cases sh <;> simp [mips32Ast] <;> exact plain_of_sequential _ rfl
  · cases sh <;> simp [mips32Ast]
  · apply htouch_of_noMem; cases sh <;> simp [mips32Ast, insnNoMem]
  · rfl
  · intro a ha; cases sh <;> simp [mips32Ast, exec, setReg_mem] <;> exact st.mem a ha
  · intro r hr
    have hr' := st.reg _ hr.lt hr.avoid
    have h2 := st.reg _ o2.lt o2.avoid
    have h3 := st.reg _ o3.lt o3.avoid
    cases sh <;>
      simp [mips32Ast, exec, reg_setReg, hr.regOf_ne_zero, regOf_inj hr.lt o1.lt, hr', h2, h3,
        shamt_reg _ hlt, wordShift]

theorem case_div (r1 r2 r3 : Nat) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.arith (.div r1 r2 r3))) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.arith (.div r1 r2 r3))) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, Bool.and_eq_true] at hok
  have o1 := regOk_of_asm hok.1.1.1
  have o2 := regOk_of_asm hok.1.1.2
  have o3 := regOk_of_asm hok.1.2
  have hs2 := st.upd
  simp only [asmUpd, instUpd, arithUpd, updPc, updReg, readReg, assertState] at hs2
  subst hs2
  apply straightCase' _ _ _ _ st rfl
  · simp [mips32Ast]; exact ⟨plain_of_sequential _ rfl, plain_of_sequential _ rfl⟩
  · simp [mips32Ast]; exact noWrite_of_writes _ rfl
  · apply htouch_of_noMem; simp [mips32Ast, insnNoMem]
  · rfl
  · intro a ha; simp [mips32Ast, exec, setReg_mem] ; exact st.mem a ha
  · intro r hr
    have hr' := st.reg _ hr.lt hr.avoid
    have h2 := st.reg _ o2.lt o2.avoid
    have h3 := st.reg _ o3.lt o3.avoid
    simp [mips32Ast, exec, reg_setReg, hr.regOf_ne_zero, regOf_inj hr.lt o1.lt, hr', h2, h3]

theorem mul64u_hi (a b : W) :
    (mul64u a b).extractLsb' 32 32 = BitVec.ofNat 32 (a.toNat * b.toNat / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt; have hb := b.isLt
  have hab : a.toNat * b.toNat < 2 ^ 64 := by
    calc a.toNat * b.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 64 := by rfl
  have hm : (mul64u a b).toNat = a.toNat * b.toNat := by
    simp only [mul64u, BitVec.toNat_mul, BitVec.toNat_setWidth]
    simp
    omega
  rw [BitVec.extractLsb'_toNat, hm, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]

theorem mul64u_lo (a b : W) :
    (mul64u a b).extractLsb' 0 32 = BitVec.ofNat 32 (a.toNat * b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt; have hb := b.isLt
  have hab : a.toNat * b.toNat < 2 ^ 64 := by
    calc a.toNat * b.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 64 := by rfl
  have hm : (mul64u a b).toNat = a.toNat * b.toNat := by
    simp only [mul64u, BitVec.toNat_mul, BitVec.toNat_setWidth]
    simp
    omega
  rw [BitVec.extractLsb'_toNat, hm, BitVec.toNat_ofNat, Nat.shiftRight_zero]

theorem case_longMul (r1 r2 r3 r4 : Nat) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.arith (.longMul r1 r2 r3 r4))) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.arith (.longMul r1 r2 r3 r4))) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, Bool.and_eq_true] at hok
  have o1 := regOk_of_asm hok.1.1.1.1.1.1
  have o2 := regOk_of_asm hok.1.1.1.1.1.2
  have o3 := regOk_of_asm hok.1.1.1.1.2
  have o4 := regOk_of_asm hok.1.1.1.2
  have hs2 := st.upd
  simp only [asmUpd, instUpd, arithUpd, updPc, updReg, readReg] at hs2
  subst hs2
  apply straightCase' _ _ _ _ st rfl
  · simp [mips32Ast]
    exact ⟨plain_of_sequential _ rfl, plain_of_sequential _ rfl, plain_of_sequential _ rfl⟩
  · simp [mips32Ast]; exact ⟨noWrite_of_writes _ rfl, noWrite_of_writes _ rfl⟩
  · apply htouch_of_noMem; simp [mips32Ast, insnNoMem]
  · rfl
  · intro a ha; simp [mips32Ast, exec, setReg_mem, setHiLo] ; exact st.mem a ha
  · intro r hr
    have hr' := st.reg _ hr.lt hr.avoid
    have h3 := st.reg _ o3.lt o3.avoid
    have h4 := st.reg _ o4.lt o4.avoid
    simp [mips32Ast, exec, reg_setReg, setHiLo, hr.regOf_ne_zero, regOf_inj hr.lt o1.lt,
      regOf_inj hr.lt o2.lt, hr', h3, h4, mul64u_hi, mul64u_lo, setReg_lo]

theorem case_longDiv (r1 r2 r3 r4 r5 : Nat) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.arith (.longDiv r1 r2 r3 r4 r5))) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.arith (.longDiv r1 r2 r3 r4 r5))) s1 s2 ms := by
  have hok := (start _ _ _ _ h).asmOk
  simp [asmOkExact, asmInstOkExact, asmArithOkExact, mips32Config] at hok

theorem case_fp (f : HolFp) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.fp f)) s2 ∧ targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.fp f)) s1 s2 ms := by
  have hok := (start _ _ _ _ h).asmOk
  cases f <;> simp [asmOkExact, asmInstOkExact, asmFpOkExact, asmFpRegOkExact, mips32Config] at hok

theorem ult_iff (x y : W) : x.ult y = true ↔ x.toNat < y.toNat := by simp [BitVec.ult]

theorem carryIn (d : W) :
    (if (0#32).ult d = true then 1#32 else 0#32) = BitVec.ofNat 32 (if d = 0#32 then 0 else 1) := by
  by_cases hd : d = 0#32
  · subst hd; decide
  · have : (0#32).ult d = true := by
      rw [ult_iff]; have : d.toNat ≠ 0 := fun h => hd (BitVec.eq_of_toNat_eq (by simpa using h))
      simp; omega
    simp [hd, this]

theorem ite_or01 (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1#32 else 0#32) ||| if q then 1#32 else 0#32) = if p ∨ q then 1#32 else 0#32 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem carry_sum (b c d : W) :
    b + c + (if (0#32).ult d = true then 1#32 else 0#32) =
      BitVec.ofNat 32 (b.toNat + c.toNat + if d = 0#32 then 0 else 1) := by
  rw [carryIn]
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt; have hc := c.isLt
  split <;> simp

theorem carry_flag (b c d : W) :
    ((if (b + c).ult c = true then 1#32 else 0#32) |||
      if (b + c + if (0#32).ult d = true then 1#32 else 0#32).ult
          (if (0#32).ult d = true then 1#32 else 0#32) = true then 1#32 else 0#32) =
      if 4294967296 ≤ b.toNat + c.toNat + (if d = 0#32 then 0 else 1) then 1#32 else 0#32 := by
  rw [ite_or01, carryIn]
  apply if_congr _ rfl rfl
  rw [ult_iff, ult_iff]
  have hb := b.isLt; have hc := c.isLt
  split <;> simp [BitVec.toNat_add] <;> omega

theorem case_addCarry (r1 r2 r3 r4 : Nat) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.arith (.addCarry r1 r2 r3 r4))) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.arith (.addCarry r1 r2 r3 r4))) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp [asmOkExact, asmInstOkExact, asmArithOkExact, mips32Config] at hok
  have o1 := regOk_of_asm (by simpa [mips32Config] using hok.1.1.1.1)
  have o2 := regOk_of_asm (by simpa [mips32Config] using hok.1.1.1.2)
  have o3 := regOk_of_asm (by simpa [mips32Config] using hok.1.1.2)
  have o4 := regOk_of_asm (by simpa [mips32Config] using hok.1.2)
  have n13 := regOf_ne o1 o3 hok.2.1
  have n14 := regOf_ne o1 o4 hok.2.2
  have hs2 := st.upd
  simp only [asmUpd, instUpd, arithUpd, updPc, updReg, readReg] at hs2
  subst hs2
  apply straightCase' _ _ _ _ st rfl
  · simp [mips32Ast]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact plain_of_sequential _ rfl
  · simp [mips32Ast]; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact noWrite_of_writes _ rfl
  · apply htouch_of_noMem; simp [mips32Ast, insnNoMem]
  · rfl
  · intro a ha; simp [mips32Ast, exec, setReg_mem]; exact st.mem a ha
  · intro r hr
    have hr' := st.reg _ hr.lt hr.avoid
    have h2 := st.reg _ o2.lt o2.avoid
    have h3 := st.reg _ o3.lt o3.avoid
    have h4 := st.reg _ o4.lt o4.avoid
    simp [mips32Ast, exec, reg_setReg, hr.regOf_ne_zero, regOf_inj hr.lt o1.lt,
      regOf_inj hr.lt o4.lt, hr', h2, h3, h4, o1.regOf_ne_zero, o2.regOf_ne_zero, o3.regOf_ne_zero,
      o4.regOf_ne_zero, o1.tmp_ne, o4.tmp_ne, o2.ne_tmp, o3.ne_tmp,
      o4.ne_tmp, hr.ne_tmp, n14, n13.symm, n14.symm, show tmp ≠ 0 by decide]
    rw [carry_flag, carry_sum]
    have n14n : r1 ≠ r4 := hok.2.2
    by_cases e4 : r = r4 <;> by_cases e1 : r = r1 <;> simp [e4, e1] <;>
      first | (subst e4; subst e1; exact absurd rfl n14n) | exact if_congr Iff.rfl rfl rfl

theorem shift_msb (x : W) : x >>> (31 : Nat) = (if x.msb then (1 : W) else 0) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have zero : (0 : W).toNat = 0 := by decide
  have one : (1 : W).toNat = 1 := by decide
  simp only [BitVec.toNat_ushiftRight, BitVec.msb_eq_decide]
  split <;> simp only [zero, one]
  all_goals norm_num [Nat.shiftRight_eq_div_pow] at *
  all_goals omega

theorem add_overflow_sign (a b : W) :
    ((a + b).toInt ≠ a.toInt + b.toInt) ↔
      (!(a.msb ^^ b.msb) && (b.msb ^^ (a+b).msb)) = true := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := (a+b).isLt
  have sum : (a+b).toNat = (a.toNat+b.toNat) % 2^32 := BitVec.toNat_add _ _
  have sa := BitVec.msb_eq_decide a
  have sb := BitVec.msb_eq_decide b
  have sc := BitVec.msb_eq_decide (a+b)
  cases ea : a.msb <;> cases eb : b.msb <;> cases ec : (a+b).msb
  all_goals simp only [BitVec.toInt_eq_msb_cond, ea, eb, ec, Bool.false_xor,
    Bool.true_xor, Bool.not_false, Bool.not_true, Bool.false_and, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte]
  all_goals simp [ea, eb, ec] at sa sb sc
  all_goals norm_num at *
  all_goals omega

theorem add_flag (a b : W) :
    ((~~~(a ^^^ b)) &&& (b ^^^ (a+b))) >>> (31 : Nat) =
      (if (a+b).toInt ≠ a.toInt+b.toInt then (1 : W) else 0) := by
  have sign : ((~~~(a ^^^ b)) &&& (b ^^^ (a+b))).msb = true ↔
      (a+b).toInt ≠ a.toInt+b.toInt := by
    have positive : decide (0 < 32) = true := rfl
    simpa only [positive, BitVec.msb_and, BitVec.msb_not, BitVec.msb_xor,
      Bool.true_and] using (add_overflow_sign a b).symm
  rw [shift_msb]
  by_cases h : ((~~~(a ^^^ b)) &&& (b ^^^ (a+b))).msb = true
  · simp only [h, ↓reduceIte, if_pos (sign.mp h)]
  · simp only [if_neg h, if_neg (fun k => h (sign.mpr k))]

theorem sub_overflow_sign (a b : W) :
    ((a - b).toInt ≠ a.toInt - b.toInt) ↔
      ((a.msb ^^ b.msb) && !(b.msb ^^ (a-b).msb)) = true := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := (a-b).isLt
  have diff : (a-b).toNat = (2^32 - b.toNat + a.toNat) % 2^32 := BitVec.toNat_sub _ _
  have sa := BitVec.msb_eq_decide a
  have sb := BitVec.msb_eq_decide b
  have sc := BitVec.msb_eq_decide (a-b)
  cases ea : a.msb <;> cases eb : b.msb <;> cases ec : (a-b).msb
  all_goals simp only [BitVec.toInt_eq_msb_cond, ea, eb, ec, Bool.false_xor,
    Bool.true_xor, Bool.not_false, Bool.not_true,
    Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
  all_goals simp [ea, eb, ec] at sa sb sc
  all_goals norm_num at *
  all_goals omega

theorem sub_flag (a b : W) :
    ((a ^^^ b) &&& (~~~(b ^^^ (a-b)))) >>> (31 : Nat) =
      (if (a-b).toInt ≠ a.toInt-b.toInt then (1 : W) else 0) := by
  have sign : ((a ^^^ b) &&& (~~~(b ^^^ (a-b)))).msb = true ↔
      (a-b).toInt ≠ a.toInt-b.toInt := by
    have positive : decide (0 < 32) = true := rfl
    simpa only [positive, BitVec.msb_and, BitVec.msb_not, BitVec.msb_xor,
      Bool.true_and] using (sub_overflow_sign a b).symm
  rw [shift_msb]
  by_cases h : ((a ^^^ b) &&& (~~~(b ^^^ (a-b)))).msb = true
  · simp only [h, ↓reduceIte, if_pos (sign.mp h)]
  · simp only [if_neg h, if_neg (fun k => h (sign.mpr k))]

theorem case_addOverflow (r1 r2 r3 r4 : Nat) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.arith (.addOverflow r1 r2 r3 r4))) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.arith (.addOverflow r1 r2 r3 r4))) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp [asmOkExact, asmInstOkExact, asmArithOkExact, mips32Config] at hok
  have o1 := regOk_of_asm (by simpa [mips32Config] using hok.1.1.1.1)
  have o2 := regOk_of_asm (by simpa [mips32Config] using hok.1.1.1.2)
  have o3 := regOk_of_asm (by simpa [mips32Config] using hok.1.1.2)
  have o4 := regOk_of_asm (by simpa [mips32Config] using hok.1.2)
  have n13 := regOf_ne o1 o3 hok.2
  have hs2 := st.upd
  simp only [asmUpd, instUpd, arithUpd, updPc, updReg, readReg] at hs2
  subst hs2
  apply straightCase' _ _ _ _ st rfl
  · simp [mips32Ast]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact plain_of_sequential _ rfl
  · simp [mips32Ast]; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact noWrite_of_writes _ rfl
  · apply htouch_of_noMem; simp [mips32Ast, insnNoMem]
  · rfl
  · intro a ha; simp [mips32Ast, exec, setReg_mem]; exact st.mem a ha
  · intro r hr
    have hr' := st.reg _ hr.lt hr.avoid
    have h2 := st.reg _ o2.lt o2.avoid
    have h3 := st.reg _ o3.lt o3.avoid
    simp [mips32Ast, exec, reg_setReg, hr.regOf_ne_zero, regOf_inj hr.lt o1.lt,
      regOf_inj hr.lt o4.lt, hr', h2, h3, o1.regOf_ne_zero, o2.regOf_ne_zero, o3.regOf_ne_zero,
      o4.regOf_ne_zero, o1.tmp_ne, o4.tmp_ne, o2.ne_tmp,
      o3.ne_tmp, hr.ne_tmp, n13.symm, show tmp ≠ 0 by decide]
    rw [add_flag]
    by_cases e4 : r = r4 <;> by_cases e1 : r = r1 <;> simp [e4, e1, BitVec.toInt_add]
    all_goals (by_cases e14 : r1 = r4 <;> simp [e14])

theorem case_subOverflow (r1 r2 r3 r4 : Nat) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.arith (.subOverflow r1 r2 r3 r4))) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.arith (.subOverflow r1 r2 r3 r4))) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp [asmOkExact, asmInstOkExact, asmArithOkExact, mips32Config] at hok
  have o1 := regOk_of_asm (by simpa [mips32Config] using hok.1.1.1.1)
  have o2 := regOk_of_asm (by simpa [mips32Config] using hok.1.1.1.2)
  have o3 := regOk_of_asm (by simpa [mips32Config] using hok.1.1.2)
  have o4 := regOk_of_asm (by simpa [mips32Config] using hok.1.2)
  have n13 := regOf_ne o1 o3 hok.2
  have hs2 := st.upd
  simp only [asmUpd, instUpd, arithUpd, updPc, updReg, readReg] at hs2
  subst hs2
  apply straightCase' _ _ _ _ st rfl
  · simp [mips32Ast]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact plain_of_sequential _ rfl
  · simp [mips32Ast]; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact noWrite_of_writes _ rfl
  · apply htouch_of_noMem; simp [mips32Ast, insnNoMem]
  · rfl
  · intro a ha; simp [mips32Ast, exec, setReg_mem]; exact st.mem a ha
  · intro r hr
    have hr' := st.reg _ hr.lt hr.avoid
    have h2 := st.reg _ o2.lt o2.avoid
    have h3 := st.reg _ o3.lt o3.avoid
    simp [mips32Ast, exec, reg_setReg, hr.regOf_ne_zero, regOf_inj hr.lt o1.lt,
      regOf_inj hr.lt o4.lt, hr', h2, h3, o1.regOf_ne_zero, o2.regOf_ne_zero, o3.regOf_ne_zero,
      o4.regOf_ne_zero, o1.tmp_ne, o4.tmp_ne, o2.ne_tmp,
      o3.ne_tmp, hr.ne_tmp, n13.symm, show tmp ≠ 0 by decide]
    rw [sub_flag]
    by_cases e4 : r = r4 <;> by_cases e1 : r = r1 <;> simp [e4, e1, BitVec.toInt_sub]
    all_goals (by_cases e14 : r1 = r4 <;> simp [e14])

end Flapjack.Mips32.TargetProof

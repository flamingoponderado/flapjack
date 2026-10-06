import Flapjack.Mips32.TargetProof.Mem

/-! # `encoder_correct mips32Target`: control flow

Branches and jumps end in a delay slot. Short forms branch with a 16-bit word offset; long
forms build the target with `BAL 1` (which links `pc + 8` and falls through after its
delay slot) and `LUI`/`ORI`/`ADDU`, as CakeML's MIPS64 target does with `BLTZAL`. -/

namespace Flapjack.Mips32.TargetProof
open ZirenDet.Isa Flapjack Flapjack.Mips32 Flapjack.Compiler.Encoders.Mips32
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps

theorem boff_branchOffset (a : W) (k : Nat) (hk : k ≤ 2) (ha : a.toNat % 4 = 0)
    (h1 : -131072 ≤ a.toInt - 4 * k) (h2 : a.toInt - 4 * k ≤ 131071) :
    boff (branchOffset a (BitVec.ofNat 16 k)) = a - BitVec.ofNat 32 (4 * k) := by
  apply BitVec.eq_of_toNat_eq
  have hA := a.isLt
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  simp only [boff, branchOffset, BitVec.toNat_shiftLeft, BitVec.toNat_signExtend,
    BitVec.msb_eq_decide, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  split at h1 <;> split at h2 <;> split <;> simp_all <;> omega


theorem seq_nop : Seq nop := seq_of_sequential _ rfl

theorem case_jumpReg (r : Nat) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.jumpReg r) s2 ∧ targetStateRel mips32Target s1 ms) :
    CaseGoal (.jumpReg r) s1 s2 ms := by
  have st := start _ _ _ _ h
  have o := regOk_of_asm (by simpa [asmOkExact] using st.asmOk)
  have hs2 := st.upd
  have hal := st.align
  have hfail := st.ok
  simp only [asmUpd, updPc, readReg, assertState] at hs2
  subst hs2
  have hal' : holAligned 2 (s1.regs r) = true := by
    simp [hal] at hfail; exact hfail.1
  have hv := st.reg _ o.lt o.avoid
  apply branchCase _ _ _ _ st [] (.jr (regOf r)) nop rfl rfl (by simp) (by simp) (decode_jr _)
    (fun t => by simp [exec, touched]) seq_nop rfl decode_nop
  · simp [exec, nop, State.setReg, hv]
  · exact hal'
  · intro a ha; simp [exec, nop, State.setReg]; exact st.mem a ha
  · intro r' hr; simp [exec, nop, State.setReg]; exact st.reg _ hr.lt hr.avoid

theorem jump_aligned (a : W) (h : asmJumpOffsetOkExact mips32Config a = true) : a.toNat % 4 = 0 := by
  simp [asmJumpOffsetOkExact, asmOffsetOkExact, asmAligned, mips32Config] at h
  exact of_decide_eq_true h.2

theorem aligned_of_mod (a : W) (h : a.toNat % 4 = 0) : holAligned 2 a = true := by
  rw [holAligned_iff]; simpa using h

theorem branch_exec (t : State) (off : BitVec 16) (rs rt : Fin 32) :
    (exec t (.beq rs rt off)).pc = t.nextPc ∧ (exec t (.beq rs rt off)).trapped = t.trapped ∧
      (exec t (.beq rs rt off)).mem = t.mem ∧ touched t (.beq rs rt off) = [] := by
  simp only [exec]; split <;> simp [touched]

theorem case_jump (a : W) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.jump a) s2 ∧ targetStateRel mips32Target s1 ms) :
    CaseGoal (.jump a) s1 s2 ms := by
  have st := start _ _ _ _ h
  have ha := jump_aligned a (by simpa [asmOkExact] using st.asmOk)
  have hs2 := st.upd
  simp only [asmUpd, jumpToOffset, updPc] at hs2
  subst hs2
  have hal : holAligned 2 (s1.pc + a) = true := by
    rw [(alignedAddSub 2 s1.pc a (aligned_of_mod a ha)).1, ← st.pc]; exact st.aligned
  by_cases hs : shortRange 4 a = true
  · have hast : mips32Ast (.jump a) = [] ++ [.beq 0 0 (branchOffset a 1), nop] := by
      simp [mips32Ast, hs]
    simp only [shortRange, Bool.and_eq_true, decide_eq_true_eq] at hs
    have hoff := boff_branchOffset a 1 (by decide) ha (by omega) (by omega)
    apply branchCase _ _ _ _ st [] _ nop hast rfl (by simp) (by simp) (decode_beq _ _ _)
      (fun t => branch_exec t _ _ _) seq_nop rfl decode_nop
    · simp [exec, nop, State.setReg, st.nextPc, st.pc]
      rw [hoff]; bv_omega
    · exact hal
    · intro x hx; simp [exec, nop, State.setReg]; exact st.mem x hx
    · intro r hr; simp [exec, nop, State.setReg]; exact st.reg _ hr.lt hr.avoid
  · have hast : mips32Ast (.jump a) =
        [.ori tmp2 ra 0, .bal 1, .lui tmp (hi16 (a - 12)), .ori tmp tmp (lo16 (a - 12)),
          .addu tmp ra tmp] ++ [.jr tmp, .ori ra tmp2 0] := by
      simp [mips32Ast, hs]
    have hdec := decode_mips32Ast (.jump a)
    rw [hast] at hdec
    have hra := st.reg 31 (by decide) (by simp [mips32Config])
    have e := const_full (a - 12)
    apply branchCase _ _ _ _ st _ (.jr tmp) (.ori ra tmp2 0) hast rfl
    · intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact ⟨plain_of_sequential _ rfl, hdec _ (by simp), noWrite_of_writes _ rfl⟩
        | exact ⟨plain_bal_one, hdec _ (by simp), noWrite_of_writes _ rfl⟩
    · intro k hk
      apply touched_nil
      have := List.getElem_mem hk
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at this
      rcases this with h | h | h | h | h <;> rw [h] <;> rfl
    · exact hdec _ (by simp)
    · intro t; simp [exec, touched]
    · exact seq_of_sequential _ rfl
    · rfl
    · exact hdec _ (by simp)
    · have f1 : tmp ≠ 0 := by decide
      have f2 : ra ≠ 0 := by decide
      have f3 : tmp2 ≠ 0 := by decide
      have f4 : tmp ≠ ra := by decide
      have f5 : tmp ≠ tmp2 := by decide
      have f6 : ra ≠ tmp2 := by decide
      simp only [List.foldl_cons, List.foldl_nil, exec, setReg_pc, setReg_nextPc, reg_setReg,
        reg_mk_gpr, alu_or, alu_add, if_true, if_false, f1, f2, f3, f5, f6, f4.symm, f5.symm,
        boff, st.nextPc, show (ra = 31) ↔ True from iff_true_intro rfl]
      erw [e]; rw [st.pc]
      bv_omega
    · exact hal
    · intro x hx; simp [exec, State.setReg]; exact st.mem x hx
    · intro r hr
      have hr' := st.reg _ hr.lt hr.avoid
      have n1 : regOf r ≠ 1 := hr.ne_tmp
      have n30 : regOf r ≠ 30 := hr.ne_tmp2
      simp only [List.foldl_cons, List.foldl_nil, exec, reg_setReg, reg_mk_gpr, alu_or, alu_add,
        tmp, tmp2, ra, hr.regOf_ne_zero, n1, if_false]
      by_cases e31 : regOf r = 31
      · have : r = 31 := (regOf_inj hr.lt (by decide)).1 e31
        subst this
        simp [e31, ← hra, zext16]
      · simp [e31, hr', hr.regOf_ne_zero, n30, zext16]

theorem bal_exec (t : State) (off : BitVec 16) :
    (exec t (.bal off)).pc = t.nextPc ∧ (exec t (.bal off)).trapped = t.trapped ∧
      (exec t (.bal off)).mem = t.mem ∧ touched t (.bal off) = [] := by
  simp [exec, setReg_pc, setReg_trapped, setReg_mem, touched]

theorem jalr_exec (t : State) (rd rs : Fin 32) :
    (exec t (.jalr rd rs)).pc = t.nextPc ∧ (exec t (.jalr rd rs)).trapped = t.trapped ∧
      (exec t (.jalr rd rs)).mem = t.mem ∧ touched t (.jalr rd rs) = [] := by
  simp [exec, setReg_pc, setReg_trapped, setReg_mem, touched]

theorem case_call (a : W) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.call a) s2 ∧ targetStateRel mips32Target s1 ms) :
    CaseGoal (.call a) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp only [asmOkExact, Bool.and_eq_true] at hok
  have ha := jump_aligned a (by simpa [mips32Config] using hok.2)
  have hs2 := st.upd
  have hlr := st.lr
  simp only [asmUpd, jumpToOffset, updPc, updReg, hlr] at hs2
  subst hs2
  have hal : holAligned 2 (s1.pc + a) = true := by
    rw [(alignedAddSub 2 s1.pc a (aligned_of_mod a ha)).1, ← st.pc]; exact st.aligned
  have n1 : ∀ r, RegOk r → regOf r ≠ 1 := fun r hr => hr.ne_tmp
  by_cases hs : shortRange 4 a = true
  · have hast : mips32Ast (.call a) = [] ++ [.bal (branchOffset a 1), nop] := by
      simp [mips32Ast, hs]
    simp only [shortRange, Bool.and_eq_true, decide_eq_true_eq] at hs
    have hoff := boff_branchOffset a 1 (by decide) ha (by omega) (by omega)
    have hlen : (mips32Enc (.call a)).length = 8 := by rw [mips32Enc_length, hast]; rfl
    apply branchCase _ _ _ _ st [] _ nop hast rfl (by simp) (by simp) (decode_bal _)
      (fun t => bal_exec t _) seq_nop rfl decode_nop
    · rw [List.foldl_nil, exec_nop]
      simp only [exec, setReg_nextPc, st.nextPc, ↓reduceIte]
      erw [hoff]; rw [st.pc]; bv_omega
    · exact hal
    · intro x hx; rw [List.foldl_nil, exec_nop]; simp [exec, setReg_mem]; exact st.mem x hx
    · intro r hr
      rw [List.foldl_nil, exec_nop, reg_mk_gpr]
      simp only [exec, reg_setReg, hr.regOf_ne_zero, if_false, hlen]
      by_cases e31 : r = 31
      · subst e31; simp [regOf, st.pc]
      · have : regOf r ≠ 31 := fun h => e31 ((regOf_inj hr.lt (by decide)).1 h)
        simp [this, e31, st.reg _ hr.lt hr.avoid]
  · have hast : mips32Ast (.call a) =
        [.bal 1, .lui tmp (hi16 (a - 8)), .ori tmp tmp (lo16 (a - 8)), .addu tmp ra tmp] ++
          [.jalr ra tmp, nop] := by
      simp [mips32Ast, hs]
    have hdec := decode_mips32Ast (.call a)
    rw [hast] at hdec
    have hlen : (mips32Enc (.call a)).length = 24 := by rw [mips32Enc_length, hast]; rfl
    have e := const_full (a - 8)
    apply branchCase _ _ _ _ st _ (.jalr ra tmp) nop hast rfl
    · intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        first
        | exact ⟨plain_of_sequential _ rfl, hdec _ (by simp), noWrite_of_writes _ rfl⟩
        | exact ⟨plain_bal_one, hdec _ (by simp), noWrite_of_writes _ rfl⟩
    · intro k hk
      apply touched_nil
      have := List.getElem_mem hk
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at this
      rcases this with h | h | h | h <;> rw [h] <;> rfl
    · exact hdec _ (by simp)
    · exact fun t => jalr_exec t _ _
    · exact seq_nop
    · rfl
    · exact decode_nop
    · rw [exec_nop]
      simp only [List.foldl_cons, List.foldl_nil, exec, setReg_pc, setReg_nextPc, reg_setReg,
        reg_mk_gpr, alu_or, alu_add, tmp, ra, ↓reduceIte, boff, st.nextPc]
      simp
      erw [e]; rw [st.pc]
      bv_omega
    · exact hal
    · intro x hx; rw [exec_nop]; simp [exec, setReg_mem]; exact st.mem x hx
    · intro r hr
      have hr' := st.reg _ hr.lt hr.avoid
      have n1 : regOf r ≠ 1 := hr.ne_tmp
      rw [exec_nop, reg_mk_gpr]
      simp only [List.foldl_cons, List.foldl_nil, exec, reg_setReg, reg_mk_gpr, alu_or, alu_add,
        tmp, ra, hr.regOf_ne_zero, n1, if_false, hlen, setReg_pc, setReg_nextPc]
      by_cases e31 : r = 31
      · subst e31; simp [regOf, st.pc, st.nextPc, show boff 1#16 = 4#32 by decide]
        bv_omega
      · have : regOf r ≠ 31 := fun h => e31 ((regOf_inj hr.lt (by decide)).1 h)
        simp [this, e31, hr']

theorem holAsmSignedLess_eq (a b : W) : holAsmSignedLess a b = a.slt b := by
  have ha := a.isLt; have hb := b.isLt
  simp only [holAsmSignedLess, BitVec.slt, BitVec.toInt_eq_toNat_cond]
  split <;> split <;> simp_all <;> omega

theorem bne_exec (t : State) (off : BitVec 16) (rs rt : Fin 32) :
    (exec t (.bne rs rt off)).pc = t.nextPc ∧ (exec t (.bne rs rt off)).trapped = t.trapped ∧
      (exec t (.bne rs rt off)).mem = t.mem ∧ touched t (.bne rs rt off) = [] := by
  simp only [exec]; split <;> simp [touched]

/-- The facts every conditional-branch case reads off `asm_ok`. -/
theorem beq_reg (t : State) (rs rt : Fin 32) (off : BitVec 16) (x : Fin 32) :
    (exec t (.beq rs rt off)).reg x = t.reg x := by
  simp only [exec]; split <;> rfl
theorem bne_reg (t : State) (rs rt : Fin 32) (off : BitVec 16) (x : Fin 32) :
    (exec t (.bne rs rt off)).reg x = t.reg x := by
  simp only [exec]; split <;> rfl

theorem branch_final_mem (pre : List Insn) (br ds : Insn) (ms : State)
    (hpre : ∀ x ∈ pre, NoWrite x) (hbr : ∀ t, (exec t br).mem = t.mem) (hds : NoWrite ds) :
    (exec (exec (pre.foldl exec ms) br) ds).mem = ms.mem := by
  rw [hds, hbr, foldl_noWrite _ _ hpre]

theorem cjump_facts (a : W) (h : asmCjumpOffsetOkExact mips32Config a = true) :
    a.toNat % 4 = 0 ∧ -131072 + 8 ≤ a.toInt ∧ a.toInt ≤ 131071 + 4 := by
  simp [asmCjumpOffsetOkExact, asmOffsetOkExact, asmAligned, mips32Config] at h
  refine ⟨of_decide_eq_true h.2, ?_, ?_⟩
  · have := of_decide_eq_true h.1.1; omega
  · have := of_decide_eq_true h.1.2; omega

/-- A conditional branch: a prefix that writes only the encoder temporary, a branch on a
condition of the state at the branch, and a `nop` delay slot. -/
theorem cmpCase (c : Cmp) (r1 : Nat) (ri : HolRegImm 32) (a : W) (s1 s2 : AsmState 32)
    (ms : State) (st : Start (.jumpCmp c r1 ri a) s1 s2 ms)
    (pre : List Insn) (br : Insn) (cond : State → Bool) (off : BitVec 16)
    (hsplit : mips32Ast (.jumpCmp c r1 ri a) = pre ++ [br, nop])
    (hpre : ∀ x ∈ pre, Plain x ∧ decode (encodeInsn x) = some x ∧ NoWrite x ∧ insnNoMem x = true)
    (hregpre : ∀ r, RegOk r → (pre.foldl exec ms).reg (regOf r) = ms.reg (regOf r))
    (hbrd : decode (encodeInsn br) = some br) (hbrt : ∀ t, touched t br = [])
    (hbr : ∀ t, exec t br =
      { t with pc := t.nextPc, nextPc := if cond t then t.pc + 4 + boff off else t.nextPc + 4 })
    (hcond : cond (pre.foldl exec ms) = wordCmpHOL c (s1.regs r1) (regImm ri s1))
    (htarget : ms.pc + BitVec.ofNat 32 (4 * pre.length) + 4 + boff off = s1.pc + a)
    (hal : holAligned 2 (s1.pc + a) = true) :
    CaseGoal (.jumpCmp c r1 ri a) s1 s2 ms := by
  have hs2 := st.upd
  simp only [asmUpd, jumpToOffset, updPc, readReg] at hs2
  have hlen : (mips32Enc (.jumpCmp c r1 ri a)).length = 4 * (pre.length + 2) := by
    rw [mips32Enc_length, hsplit]; simp
  obtain ⟨f1, f2, f3⟩ := foldl_plain pre ms (fun x hx => (hpre x hx).1) st.nextPc
  have f4 : (pre.foldl exec ms).mem = ms.mem := foldl_noWrite _ _ (fun x hx => (hpre x hx).2.2.1)
  have hbrPc : ∀ t, (exec t br).pc = t.nextPc ∧ (exec t br).trapped = t.trapped ∧
      (exec t br).mem = t.mem ∧ touched t br = [] := fun t => by
    rw [hbr]; exact ⟨rfl, rfl, rfl, hbrt t⟩
  have hp' := fun x hx => (⟨(hpre x hx).1, (hpre x hx).2.1, (hpre x hx).2.2.1⟩ :
    Plain x ∧ decode (encodeInsn x) = some x ∧ NoWrite x)
  have ht' := fun k (hk : k < pre.length) =>
    touched_nil _ (hpre _ (List.getElem_mem hk)).2.2.2 ((pre.take k).foldl exec ms)
  by_cases hc : wordCmpHOL c (s1.regs r1) (regImm ri s1) = true
  · simp only [hc, if_true] at hs2
    subst hs2
    apply branchCase _ _ _ _ st pre br nop hsplit rfl hp' ht' hbrd hbrPc seq_nop rfl
      decode_nop
    · rw [exec_nop, hbr]; simp only [hcond, hc, if_true]; rw [f1, htarget]
    · exact hal
    · intro x hx; rw [exec_nop, hbr]; dsimp only; rw [f4]; exact st.mem x hx
    · intro r hr; rw [exec_nop, reg_mk_gpr, hbr, reg_mk_gpr, hregpre r hr]
      exact st.reg _ hr.lt hr.avoid
  · simp only [hc, if_false, Bool.false_eq_true] at hs2
    subst hs2
    apply branchCase _ _ _ _ st pre br nop hsplit rfl hp' ht' hbrd hbrPc seq_nop rfl
      decode_nop
    · rw [exec_nop, hbr]; simp only [hcond, hc, if_false, Bool.false_eq_true]
      rw [f2, f1, st.pc, hlen]
      apply BitVec.eq_of_toNat_eq; simp; omega
    · rw [hlen, ← st.pc]; exact aligned_add_four _ _ st.aligned
    · intro x hx; rw [exec_nop, hbr]; dsimp only; rw [f4]; exact st.mem x hx
    · intro r hr; rw [exec_nop, reg_mk_gpr, hbr, reg_mk_gpr, hregpre r hr]
      exact st.reg _ hr.lt hr.avoid

theorem exec_beq (t : State) (rs rt : Fin 32) (off : BitVec 16) :
    exec t (.beq rs rt off) = { t with pc := t.nextPc, nextPc :=
      (if (t.reg rs == t.reg rt) then t.pc + 4 + boff off else t.nextPc + 4) } := by
  simp only [exec]; split <;> simp_all
theorem exec_bne (t : State) (rs rt : Fin 32) (off : BitVec 16) :
    exec t (.bne rs rt off) = { t with pc := t.nextPc, nextPc :=
      (if (t.reg rs != t.reg rt) then t.pc + 4 + boff off else t.nextPc + 4) } := by
  simp only [exec]; split <;> simp_all

@[simp] theorem flag_ne_zero (p : Prop) [Decidable p] :
    ((if p then 1#32 else 0#32) != 0#32) = decide p := by
  by_cases h : p <;> simp [h]
@[simp] theorem flag_eq_zero (p : Prop) [Decidable p] :
    ((if p then 1#32 else 0#32) == 0#32) = !decide p := by
  by_cases h : p <;> simp [h]

theorem reg_tmp_write (s : State) (v : W) (r : Nat) (hr : RegOk r) :
    (s.setReg tmp v).reg (regOf r) = s.reg (regOf r) := by
  simp [reg_setReg, hr.regOf_ne_zero, hr.ne_tmp]

theorem case_jumpCmp_reg (c : Cmp) (r1 r2 : Nat) (a : W) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.jumpCmp c r1 (.reg r2) a) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.jumpCmp c r1 (.reg r2) a) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp only [asmOkExact, asmCmpOkExact, asmRegImmOkExact, Bool.and_eq_true] at hok
  obtain ⟨ha, hlo, hhi⟩ := cjump_facts a hok.1
  have o1 := regOk_of_asm hok.2.1
  have o2 := regOk_of_asm hok.2.2
  have v1 := st.reg _ o1.lt o1.avoid
  have v2 := st.reg _ o2.lt o2.avoid
  have hoff1 := boff_branchOffset a 1 (by decide) ha (by omega) (by omega)
  have hoff2 := boff_branchOffset a 2 (by decide) ha (by omega) (by omega)
  have hb : branchOffset a 2 + 1 = branchOffset a (BitVec.ofNat 16 1) := by
    simp only [branchOffset]; bv_omega
  have hal : holAligned 2 (s1.pc + a) = true := by
    rw [(alignedAddSub 2 s1.pc a (aligned_of_mod a ha)).1, ← st.pc]; exact st.aligned
  have tgt0 : ms.pc + BitVec.ofNat 32 (4 * 0) + 4 + boff (branchOffset a 2 + 1) = s1.pc + a := by
    rw [hb, hoff1, st.pc]; bv_omega
  have tgt1 : ms.pc + BitVec.ofNat 32 (4 * 1) + 4 + boff (branchOffset a 2) = s1.pc + a := by
    erw [hoff2]; rw [st.pc]; bv_omega
  have pre1 : ∀ x, insnSequential x = true → insnWrites x = false → insnNoMem x = true →
      x ∈ mips32Ast (.jumpCmp c r1 (.reg r2) a) →
      ∀ y ∈ [x], Plain y ∧ decode (encodeInsn y) = some y ∧ NoWrite y ∧ insnNoMem y = true := by
    intro x hs hw hm hx y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy; subst hy
    exact ⟨plain_of_sequential _ hs, decode_mips32Ast _ _ hx, noWrite_of_writes _ hw, hm⟩
  cases c
  · exact cmpCase _ _ _ _ _ _ _ st [] _ (fun t => t.reg (regOf r1) == t.reg (regOf r2)) _
      (by simp [mips32Ast]) (by simp) (fun _ _ => rfl) (decode_beq _ _ _) (fun _ => by simp [touched])
      (fun t => exec_beq t _ _ _) (by simp [wordCmpHOL, regImm, readReg, v1, v2]) tgt0 hal
  · exact cmpCase _ _ _ _ _ _ _ st [.sltu tmp (regOf r1) (regOf r2)] (.bne tmp 0 (branchOffset a 2))
      (fun t => t.reg tmp != t.reg 0) _
      (by simp [mips32Ast, cmpBranch]) (pre1 _ rfl rfl rfl (by simp [mips32Ast]))
      (fun r hr => by simp [exec, reg_tmp_write _ _ _ hr])
      (decode_bne _ _ _) (fun _ => by simp [touched]) (fun t => exec_bne t _ _ _)
      (by simp [exec, wordCmpHOL, regImm, readReg, v1, v2, tmp, BitVec.ult, BitVec.lt_def]) tgt1 hal
  · exact cmpCase _ _ _ _ _ _ _ st [.slt tmp (regOf r1) (regOf r2)] (.bne tmp 0 (branchOffset a 2))
      (fun t => t.reg tmp != t.reg 0) _
      (by simp [mips32Ast, cmpBranch]) (pre1 _ rfl rfl rfl (by simp [mips32Ast]))
      (fun r hr => by simp [exec, reg_tmp_write _ _ _ hr])
      (by simp) (fun _ => by simp [touched]) (fun t => by exact exec_bne t _ _ _)
      (by simp [exec, wordCmpHOL, regImm, readReg, v1, v2, tmp, holAsmSignedLess_eq]) tgt1 hal
  · exact cmpCase _ _ _ _ _ _ _ st [.and tmp (regOf r1) (regOf r2)] (.beq tmp 0 (branchOffset a 2))
      (fun t => t.reg tmp == t.reg 0) _
      (by simp [mips32Ast, cmpBranch]) (pre1 _ rfl rfl rfl (by simp [mips32Ast]))
      (fun r hr => by simp [exec, reg_tmp_write _ _ _ hr])
      (by simp) (fun _ => by simp [touched]) (fun t => by exact exec_beq t _ _ _)
      (by simp [exec, wordCmpHOL, regImm, readReg, v1, v2, tmp, AndOp.and]) tgt1 hal
  · exact cmpCase _ _ _ _ _ _ _ st [] (.bne (regOf r1) (regOf r2) (branchOffset a 2 + 1))
      (fun t => t.reg (regOf r1) != t.reg (regOf r2)) _
      (by simp [mips32Ast]) (by simp) (fun _ _ => rfl) (decode_bne _ _ _) (fun _ => by simp [touched])
      (fun t => exec_bne t _ _ _) (by simp [wordCmpHOL, regImm, readReg, v1, v2, bne]) tgt0 hal
  · exact cmpCase _ _ _ _ _ _ _ st [.sltu tmp (regOf r1) (regOf r2)] (.beq tmp 0 (branchOffset a 2))
      (fun t => t.reg tmp == t.reg 0) _
      (by simp [mips32Ast, cmpBranch]) (pre1 _ rfl rfl rfl (by simp [mips32Ast]))
      (fun r hr => by simp [exec, reg_tmp_write _ _ _ hr])
      (by simp) (fun _ => by simp [touched]) (fun t => by exact exec_beq t _ _ _)
      (by simp [exec, wordCmpHOL, regImm, readReg, v1, v2, tmp, BitVec.ult, BitVec.lt_def]) tgt1 hal
  · exact cmpCase _ _ _ _ _ _ _ st [.slt tmp (regOf r1) (regOf r2)] (.beq tmp 0 (branchOffset a 2))
      (fun t => t.reg tmp == t.reg 0) _
      (by simp [mips32Ast, cmpBranch]) (pre1 _ rfl rfl rfl (by simp [mips32Ast]))
      (fun r hr => by simp [exec, reg_tmp_write _ _ _ hr])
      (by simp) (fun _ => by simp [touched]) (fun t => by exact exec_beq t _ _ _)
      (by simp [exec, wordCmpHOL, regImm, readReg, v1, v2, tmp, holAsmSignedLess_eq]) tgt1 hal
  · exact cmpCase _ _ _ _ _ _ _ st [.and tmp (regOf r1) (regOf r2)] (.bne tmp 0 (branchOffset a 2))
      (fun t => t.reg tmp != t.reg 0) _
      (by simp [mips32Ast, cmpBranch]) (pre1 _ rfl rfl rfl (by simp [mips32Ast]))
      (fun r hr => by simp [exec, reg_tmp_write _ _ _ hr])
      (by simp) (fun _ => by simp [touched]) (fun t => by exact exec_bne t _ _ _)
      (by simp [exec, wordCmpHOL, regImm, readReg, v1, v2, tmp, AndOp.and]) tgt1 hal

theorem case_jumpCmp_imm (c : Cmp) (r1 : Nat) (i : W) (a : W) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.jumpCmp c r1 (.imm i) a) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.jumpCmp c r1 (.imm i) a) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp only [asmOkExact, asmCmpOkExact, asmRegImmOkExact, Bool.and_eq_true] at hok
  obtain ⟨ha, hlo, hhi⟩ := cjump_facts a hok.1
  have o1 := regOk_of_asm hok.2.1
  have himm := hok.2.2
  have v1 := st.reg _ o1.lt o1.avoid
  have hoff1 := boff_branchOffset a 1 (by decide) ha (by omega) (by omega)
  have hoff2 := boff_branchOffset a 2 (by decide) ha (by omega) (by omega)
  have hb : branchOffset a 2 + 1 = branchOffset a (BitVec.ofNat 16 1) := by
    simp only [branchOffset]; bv_omega
  have hal : holAligned 2 (s1.pc + a) = true := by
    rw [(alignedAddSub 2 s1.pc a (aligned_of_mod a ha)).1, ← st.pc]; exact st.aligned
  have tgt0 : ms.pc + BitVec.ofNat 32 (4 * 0) + 4 + boff (branchOffset a 2 + 1) = s1.pc + a := by
    rw [hb, hoff1, st.pc]; bv_omega
  have tgt1 : ms.pc + BitVec.ofNat 32 (4 * 1) + 4 + boff (branchOffset a 2) = s1.pc + a := by
    erw [hoff2]; rw [st.pc]; bv_omega
  have pre1 : ∀ x, insnSequential x = true → insnWrites x = false → insnNoMem x = true →
      x ∈ mips32Ast (.jumpCmp c r1 (.imm i) a) →
      ∀ y ∈ [x], Plain y ∧ decode (encodeInsn y) = some y ∧ NoWrite y ∧ insnNoMem y = true := by
    intro x hs hw hm hx y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy; subst hy
    exact ⟨plain_of_sequential _ hs, decode_mips32Ast _ _ hx, noWrite_of_writes _ hw, hm⟩
  cases c
  · have hv : (-32768 : W).sle i = true ∧ i.sle 32767 = true := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at himm
      rcases himm with ⟨hx, -⟩ | hv
      · exact absurd hx (by decide)
      · simpa [mips32Config] using hv
    have e := sext_lo16 i hv.1 hv.2
    exact cmpCase _ _ _ _ _ _ _ st [.addiu tmp 0 (lo16 i)] (.beq (regOf r1) tmp (branchOffset a 2))
      (fun t => t.reg (regOf r1) == t.reg tmp) _
      (by simp [mips32Ast]) (pre1 _ rfl rfl rfl (by simp [mips32Ast]))
      (fun r hr => by simp [exec, reg_tmp_write _ _ _ hr])
      (by simp) (fun _ => by simp [touched]) (fun t => by exact exec_beq t _ _ _)
      (by simp [exec, wordCmpHOL, regImm, v1, tmp, e, o1.regOf_ne_zero,
        show regOf r1 ≠ 1 from o1.ne_tmp]) tgt1 hal
  · have hv : (-32768 : W).sle i = true ∧ i.sle 32767 = true := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at himm
      rcases himm with ⟨hx, -⟩ | hv
      · exact absurd hx (by decide)
      · simpa [mips32Config] using hv
    have e := sext_lo16 i hv.1 hv.2
    exact cmpCase _ _ _ _ _ _ _ st [.sltiu tmp (regOf r1) (lo16 i)] (.bne tmp 0 (branchOffset a 2))
      (fun t => t.reg tmp != t.reg 0) _
      (by simp [mips32Ast, cmpBranch]) (pre1 _ rfl rfl rfl (by simp [mips32Ast]))
      (fun r hr => by simp [exec, reg_tmp_write _ _ _ hr])
      (by simp) (fun _ => by simp [touched]) (fun t => by exact exec_bne t _ _ _)
      (by simp [exec, wordCmpHOL, regImm, v1, tmp, BitVec.ult, BitVec.lt_def,
        e, bne]) tgt1 hal
  · have hv : (-32768 : W).sle i = true ∧ i.sle 32767 = true := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at himm
      rcases himm with ⟨hx, -⟩ | hv
      · exact absurd hx (by decide)
      · simpa [mips32Config] using hv
    have e := sext_lo16 i hv.1 hv.2
    exact cmpCase _ _ _ _ _ _ _ st [.slti tmp (regOf r1) (lo16 i)] (.bne tmp 0 (branchOffset a 2))
      (fun t => t.reg tmp != t.reg 0) _
      (by simp [mips32Ast, cmpBranch]) (pre1 _ rfl rfl rfl (by simp [mips32Ast]))
      (fun r hr => by simp [exec, reg_tmp_write _ _ _ hr])
      (by simp) (fun _ => by simp [touched]) (fun t => by exact exec_bne t _ _ _)
      (by simp [exec, wordCmpHOL, regImm, v1, tmp, holAsmSignedLess_eq, e, bne]) tgt1 hal
  · have hv : (0 : W).sle i = true ∧ i.sle 0xFFFF = true := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at himm
      rcases himm with ⟨hx, -⟩ | hv
      · exact absurd hx (by decide)
      · simpa [mips32Config] using hv
    have e := zext_lo16 i hv.1 hv.2
    exact cmpCase _ _ _ _ _ _ _ st [.andi tmp (regOf r1) (lo16 i)] (.beq tmp 0 (branchOffset a 2))
      (fun t => t.reg tmp == t.reg 0) _
      (by simp [mips32Ast, cmpBranch]) (pre1 _ rfl rfl rfl (by simp [mips32Ast]))
      (fun r hr => by simp [exec, reg_tmp_write _ _ _ hr])
      (by simp) (fun _ => by simp [touched]) (fun t => by exact exec_beq t _ _ _)
      (by simp [exec, wordCmpHOL, regImm, v1, tmp, AndOp.and, e]) tgt1 hal
  · have hv : (-32768 : W).sle i = true ∧ i.sle 32767 = true := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at himm
      rcases himm with ⟨hx, -⟩ | hv
      · exact absurd hx (by decide)
      · simpa [mips32Config] using hv
    have e := sext_lo16 i hv.1 hv.2
    exact cmpCase _ _ _ _ _ _ _ st [.addiu tmp 0 (lo16 i)] (.bne (regOf r1) tmp (branchOffset a 2))
      (fun t => t.reg (regOf r1) != t.reg tmp) _
      (by simp [mips32Ast]) (pre1 _ rfl rfl rfl (by simp [mips32Ast]))
      (fun r hr => by simp [exec, reg_tmp_write _ _ _ hr])
      (by simp) (fun _ => by simp [touched]) (fun t => by exact exec_bne t _ _ _)
      (by simp [exec, wordCmpHOL, regImm, v1, tmp, e, bne, o1.regOf_ne_zero,
        show regOf r1 ≠ 1 from o1.ne_tmp]) tgt1 hal
  · have hv : (-32768 : W).sle i = true ∧ i.sle 32767 = true := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at himm
      rcases himm with ⟨hx, -⟩ | hv
      · exact absurd hx (by decide)
      · simpa [mips32Config] using hv
    have e := sext_lo16 i hv.1 hv.2
    exact cmpCase _ _ _ _ _ _ _ st [.sltiu tmp (regOf r1) (lo16 i)] (.beq tmp 0 (branchOffset a 2))
      (fun t => t.reg tmp == t.reg 0) _
      (by simp [mips32Ast, cmpBranch]) (pre1 _ rfl rfl rfl (by simp [mips32Ast]))
      (fun r hr => by simp [exec, reg_tmp_write _ _ _ hr])
      (by simp) (fun _ => by simp [touched]) (fun t => by exact exec_beq t _ _ _)
      (by simp [exec, wordCmpHOL, regImm, v1, tmp, BitVec.ult, BitVec.lt_def,
        e]) tgt1 hal
  · have hv : (-32768 : W).sle i = true ∧ i.sle 32767 = true := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at himm
      rcases himm with ⟨hx, -⟩ | hv
      · exact absurd hx (by decide)
      · simpa [mips32Config] using hv
    have e := sext_lo16 i hv.1 hv.2
    exact cmpCase _ _ _ _ _ _ _ st [.slti tmp (regOf r1) (lo16 i)] (.beq tmp 0 (branchOffset a 2))
      (fun t => t.reg tmp == t.reg 0) _
      (by simp [mips32Ast, cmpBranch]) (pre1 _ rfl rfl rfl (by simp [mips32Ast]))
      (fun r hr => by simp [exec, reg_tmp_write _ _ _ hr])
      (by simp) (fun _ => by simp [touched]) (fun t => by exact exec_beq t _ _ _)
      (by simp [exec, wordCmpHOL, regImm, v1, tmp, holAsmSignedLess_eq, e]) tgt1 hal
  · have hv : (0 : W).sle i = true ∧ i.sle 0xFFFF = true := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at himm
      rcases himm with ⟨hx, -⟩ | hv
      · exact absurd hx (by decide)
      · simpa [mips32Config] using hv
    have e := zext_lo16 i hv.1 hv.2
    exact cmpCase _ _ _ _ _ _ _ st [.andi tmp (regOf r1) (lo16 i)] (.bne tmp 0 (branchOffset a 2))
      (fun t => t.reg tmp != t.reg 0) _
      (by simp [mips32Ast, cmpBranch]) (pre1 _ rfl rfl rfl (by simp [mips32Ast]))
      (fun r hr => by simp [exec, reg_tmp_write _ _ _ hr])
      (by simp) (fun _ => by simp [touched]) (fun t => by exact exec_bne t _ _ _)
      (by simp [exec, wordCmpHOL, regImm, v1, tmp, AndOp.and, e, bne]) tgt1 hal

theorem case_loc (r : Nat) (i : W) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.loc r i) s2 ∧ targetStateRel mips32Target s1 ms) :
    CaseGoal (.loc r i) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp only [asmOkExact, Bool.and_eq_true] at hok
  have o := regOk_of_asm hok.1
  have hra := st.reg 31 (by decide) (by simp [mips32Config])
  have hs2 := st.upd
  simp only [asmUpd, updPc, updReg] at hs2
  subst hs2
  have hbal : boff 1#16 = 4#32 := by decide
  by_cases h31 : r = 31
  · subst h31
    have e := const_full (i - 8)
    apply straightCase' _ _ _ _ st rfl
    · simp [mips32Ast]
      exact ⟨plain_bal_one, plain_of_sequential _ rfl, plain_of_sequential _ rfl,
        plain_of_sequential _ rfl⟩
    · simp [mips32Ast]
      exact ⟨noWrite_of_writes _ rfl, noWrite_of_writes _ rfl, noWrite_of_writes _ rfl⟩
    · apply htouch_of_noMem; simp [mips32Ast, insnNoMem]
    · rfl
    · intro x hx; simp [mips32Ast, exec, setReg_mem]; exact st.mem x hx
    · intro r' hr
      have hr' := st.reg _ hr.lt hr.avoid
      simp only [mips32Ast, List.foldl_cons, List.foldl_nil, exec, reg_setReg,
        reg_mk_gpr, alu_or, alu_add, tmp, ra, hr.regOf_ne_zero, show regOf r' ≠ 1 from hr.ne_tmp,
        setReg_nextPc, ↓reduceIte, show (1 : Fin 32) ≠ 0 by decide, show (31 : Fin 32) ≠ 0 by decide,
        show (31 : Fin 32) ≠ 1 by decide]
      by_cases e31 : r' = 31
      · subst e31
        simp only [show regOf 31 = 31 by rfl, if_true]
        erw [e]; rw [st.pc]; bv_omega
      · have : regOf r' ≠ 31 := fun h => e31 ((regOf_inj hr.lt (by decide)).1 h)
        simp [this, e31, hr']
  · have e := const_full (i - 12)
    have nr : regOf r ≠ 31 := fun h => h31 ((regOf_inj o.lt (by decide)).1 h)
    have nr1 : regOf r ≠ 1 := o.ne_tmp
    have nr0 := o.regOf_ne_zero
    apply straightCase' _ _ _ _ st rfl
    · simp [mips32Ast, h31]
      exact ⟨plain_of_sequential _ rfl, plain_bal_one, plain_of_sequential _ rfl,
        plain_of_sequential _ rfl, plain_of_sequential _ rfl, plain_of_sequential _ rfl⟩
    · simp [mips32Ast, h31]
      exact ⟨noWrite_of_writes _ rfl, noWrite_of_writes _ rfl, noWrite_of_writes _ rfl,
        noWrite_of_writes _ rfl, noWrite_of_writes _ rfl⟩
    · apply htouch_of_noMem; simp [mips32Ast, h31, insnNoMem]
    · rfl
    · intro x hx; simp [mips32Ast, h31, exec, setReg_mem]; exact st.mem x hx
    · intro r' hr
      have hr' := st.reg _ hr.lt hr.avoid
      simp only [mips32Ast, h31, List.foldl_cons, List.foldl_nil, exec, reg_setReg,
        reg_mk_gpr, alu_or, alu_add, tmp, ra, hr.regOf_ne_zero,
        show regOf r' ≠ 1 from hr.ne_tmp, setReg_pc, setReg_nextPc, ↓reduceIte, show (1 : Fin 32) ≠ 0 by decide, show (31 : Fin 32) ≠ 0 by decide,
        nr0, Ne.symm nr, Ne.symm nr1]
      by_cases e31 : r' = 31
      · subst e31
        have hra' : ms.reg 31 = s1.regs 31 := hra
        simp [show regOf 31 = 31 by rfl, hra', Ne.symm h31, zext16]
      by_cases er : r' = r
      · subst er
        simp only [nr, if_true, if_false]
        simp []
        erw [e]; rw [st.nextPc, st.pc]; bv_omega
      · have : regOf r' ≠ 31 := fun h => e31 ((regOf_inj hr.lt (by decide)).1 h)
        have : regOf r' ≠ regOf r := regOf_ne hr o er
        simp [*]

end Flapjack.Mips32.TargetProof

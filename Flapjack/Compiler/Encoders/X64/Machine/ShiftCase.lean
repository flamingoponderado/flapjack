import Flapjack.Compiler.Encoders.X64.Machine.ArithBinopCase

/-!
# The `shift` cases of `encoder_correct x64Target`

`arith (shift sh r1 r2 (.imm i))` lowers to `binopRI (x64_sh sh) r1 i`, which
encodes to the shift-by-one `0xD1` form when `i = 1` and to the `0xC1`
immediate form otherwise.  `arith (shift sh r1 r2 (.reg r3))` lowers to
`binopRR (x64_sh sh) r1 r3`; `asm_ok` forces `r3 = 1` (x86's `cl`), so the
encoded form is the `0xD3` register form.  In both cases `asm_ok` also bounds
the shift amount, and the register form's `assert` (amount below the word
width) is discharged by `asm_step`'s `¬ s2.failed`.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-- `x64_sh` maps into the four shift opcodes. -/
theorem x64Sh_hop (sh : Shift) :
    x64Sh sh = .zror ∨ x64Sh sh = .zshl ∨ x64Sh sh = .zshr ∨ x64Sh sh = .zsar := by
  cases sh <;> simp [x64Sh]

/-- The closed model's shift value is the source `word_shift`. -/
theorem binopValue_x64Sh (sh : Shift) (a i : BitVec 64) :
    binopValue (x64Sh sh) a i = wordShift sh a i.toNat := by
  cases sh <;> rfl

/-- `asm_ok` of an immediate shift splits into its register checks, the
zero/nonzero check and the width bound. -/
theorem shiftImm_ok (sh : Shift) (r1 r2 : Nat) (i : BitVec 64)
    (h : asmOkExact (.inst (.arith (.shift sh r1 r2 (.imm i)))) x64Config = true) :
    r1 = r2 ∧ asmRegOkExact r1 x64Config = true ∧
      asmRegOkExact r2 x64Config = true ∧
      (i ≠ 0#64 ∨ sh = .lsl) ∧ i.toNat < 64 := by
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, x64Config,
    Bool.and_eq_true, Bool.or_eq_true, Bool.not_true, Bool.false_or] at h
  simp at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2.1, h.2.2⟩

/-- `asm_ok` of a register shift splits into its register checks, the
`cl` restriction and the two-register equality. -/
theorem shiftReg_ok (sh : Shift) (r1 r2 r3 : Nat)
    (h : asmOkExact (.inst (.arith (.shift sh r1 r2 (.reg r3)))) x64Config = true) :
    r1 = r2 ∧ asmRegOkExact r1 x64Config = true ∧
      asmRegOkExact r2 x64Config = true ∧
      asmRegOkExact r3 x64Config = true ∧ r3 = 1 := by
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, x64Config,
    Bool.and_eq_true, Bool.or_eq_true, Bool.not_true, Bool.false_or] at h
  simp at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2.1, h.2.2⟩

/-- The immediate shift encoding is the lowering's instruction. -/
theorem x64Enc_shiftImm (sh : Shift) (r1 r2 : Nat) (i : BitVec 64)
    (h : asmOkExact (.inst (.arith (.shift sh r1 r2 (.imm i)))) x64Config = true) :
    x64Target.config.encode (.inst (.arith (.shift sh r1 r2 (.imm i)))) =
      encodeInsn (.binopRI (x64Sh sh) .z64 r1 i) := by
  obtain ⟨-, hr1ok, -, -, hlt⟩ := shiftImm_ok sh r1 r2 i h
  have hr1 : r1 < 16 := jumpReg_reg_lt r1 hr1ok
  have hdst : totalNum2Zreg r1 = r1 := totalNum2Zreg_eq r1 hr1
  have hflat : (x64Ast (.inst (.arith (.shift sh r1 r2 (.imm i))))).flatMap encodeInsn =
      encodeInsn (.binopRI (x64Sh sh) .z64 r1 i) := by
    simp only [x64Ast, x64Inst, hdst]
    simp
  have hne : encodeInsn (.binopRI (x64Sh sh) .z64 r1 i) ≠ [] := by
    by_cases h1 : i = 1
    · rw [h1, encodeInsn_binopRI_D1 (x64Sh sh) r1 hr1 (x64Sh_hop sh)]
      simp [binopRID1Bytes]
    · have hs : -128 ≤ i.toInt ∧ i.toInt ≤ 127 := by
        have ht : i.toInt = (i.toNat : Int) := by
          rw [BitVec.toInt_eq_toNat_cond]
          rw [if_pos (by omega : 2 * i.toNat < 2 ^ 64)]
        constructor <;> omega
      rw [encodeInsn_binopRI_C1 (x64Sh sh) r1 hr1 i (x64Sh_hop sh) h1 hs]
      simp [binopRIC1Bytes]
  exact x64Enc_of_flatMap _ _ hflat hne

/-- The closed model executes an immediate shift. -/
theorem execInsn_binopRI_shift (sh : Shift) (dst : Nat) (imm : BitVec 64) (len : Nat)
    (s : X64State) :
    execInsn (.binopRI (x64Sh sh) .z64 dst imm) len s =
      { (writeRegSized .z64 dst (wordShift sh (readReg s dst) imm.toNat) s) with
        flags := binopFlags (x64Sh sh) (readReg s dst) imm s.flags } := by
  cases sh <;> rfl

/-- One `x64Next` step over an immediate shift writes the shifted value. -/
theorem x64Next_shiftImm (ms : X64State) (sh : Shift) (r : Nat) (i : BitVec 64) (len : Nat)
    (hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.binopRI (x64Sh sh) .z64 r i, len))
    (hlen : (encodeInsn (.binopRI (x64Sh sh) .z64 r i)).length = len)
    (hfailed : ms.failed = false) :
    x64Next ms = { (writeReg ms r (wordShift sh (readReg ms r) i.toNat)) with
      flags := binopFlags (x64Sh sh) (readReg ms r) i ms.flags,
      pc := ms.pc + BitVec.ofNat 64
        (encodeInsn (.binopRI (x64Sh sh) .z64 r i)).length } := by
  rw [hlen]
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec]
  rw [execInsn_binopRI_shift]
  simp only [writeRegSized, writeReg]

/-- The immediate `shift` constructor of `encoder_correct x64Target`. -/
theorem case_shiftImm (sh : Shift) (r1 r2 : Nat) (i : BitVec 64) (s1 s2 : AsmState 64)
    (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.arith (.shift sh r1 r2 (.imm i)))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.arith (.shift sh r1 r2 (.imm i)))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.arith (.shift sh r1 r2 (.imm i)))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  obtain ⟨hr12, hr1ok, -, -, hlt⟩ := shiftImm_ok sh r1 r2 i hok
  have hr1 : r1 < 16 := jumpReg_reg_lt r1 hr1ok
  have hreg1 := regOk_of_asmRegOk r1 hr1ok
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64
      (encodeInsn (.binopRI (x64Sh sh) .z64 r1 i)).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
    rw [x64Enc_shiftImm sh r1 r2 i hok]
  have hs2regs : ∀ x, s2.regs x =
      if x = r1 then wordShift sh (s1.regs r1) i.toNat else s1.regs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, arithUpd, regImm, AsmSem.readReg, updReg,
      assertState, Bool.not_true, Bool.false_or, hr12]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, arithUpd, regImm, updReg, assertState,
      Bool.not_true, Bool.false_or]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, arithUpd, regImm, updReg, assertState,
      Bool.not_true, Bool.false_or]
  have hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, arithUpd, regImm, updReg, assertState,
      Bool.not_true, Bool.false_or]
  have hdom : s2.memDomain = s1.memDomain := hs2dom
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.binopRI (x64Sh sh) .z64 r1 i)) ms.mem
      s1.memDomain := by
    rw [st.pc]
    have h' := st.bytesTarget
    rw [x64Enc_shiftImm sh r1 r2 i hok] at h'
    exact h'
  have hcode : allPcs (x64Target.config.encode
      (.inst (.arith (.shift sh r1 r2 (.imm i))))).length s1.pc 0 ⊆ s1.memDomain :=
    bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
  have finish (hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms))
      (hsafe : StepSafe s1.memDomain ms) :
      CaseGoal (.inst (.arith (.shift sh r1 r2 (.imm i)))) s1 s2 ms := by
    exact encoderCaseStep _ s1 s2 ms 0 hdom hcode
      (by
        intro k hk
        have hk0 : k = 0 := by omega
        subst hk0
        simpa using hsafe)
      (by intro k hk1 hk2; omega) hq
  have hdomN := bytesInMemoryHOL_domain _ _ _ _ hbm
  have hq_of : ∀ (len : Nat), len = (encodeInsn (.binopRI (x64Sh sh) .z64 r1 i)).length →
      (decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
        some (.binopRI (x64Sh sh) .z64 r1 i, len)) →
      targetStateRel x64Target s2 (x64Next^[0 + 1] ms) := by
    intro len hlen hdec
    have hnext := x64Next_shiftImm ms sh r1 i len hdec hlen.symm st.failed
    show targetStateRel x64Target s2 (x64Next ms)
    rw [hnext]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [x64Target_stateOk, x64StateOk, writeReg, st.failed, Bool.not_false]
    · show ms.pc + BitVec.ofNat 64
          (encodeInsn (.binopRI (x64Sh sh) .z64 r1 i)).length = s2.pc
      rw [st.pc, hs2pc]
    · intro a ha
      show ms.mem a = s2.mem a
      rw [hs2mem a]
      rw [hs2dom] at ha
      exact st.mem a ha
    · intro x hx
      show readReg (writeReg ms r1 (wordShift sh (readReg ms r1) i.toNat)) x = s2.regs x
      rw [readReg_writeReg ms r1 _ x hr1 hx.1, hs2regs x]
      by_cases hxr : x = r1
      · rw [if_pos hxr, if_pos hxr, st.reg r1 hreg1]
      · rw [if_neg hxr, if_neg hxr]
        exact st.reg x hx
    · intro x hx
      show readXmm ms x = s2.fpRegs x
      rw [hs2fp x]
      exact st.fp x hx
  have hsafe_of : ∀ (len : Nat),
      (decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
        some (.binopRI (x64Sh sh) .z64 r1 i, len)) →
      len = (encodeInsn (.binopRI (x64Sh sh) .z64 r1 i)).length →
      StepSafe s1.memDomain ms := by
    intro len hdec hlen
    refine ⟨.binopRI (x64Sh sh) .z64 r1 i, len, hdec, ?_, ?_⟩
    · intro j hj
      exact hdomN j (by omega)
    · intro a ha; simp [x64Touched] at ha
  by_cases h1 : i = 1
  · have hlen : (encodeInsn (.binopRI (x64Sh sh) .z64 r1 i)).length = 3 := by
      rw [h1, encodeInsn_binopRI_D1 (x64Sh sh) r1 hr1 (x64Sh_hop sh)]
      simp [binopRID1Bytes]
    have hbm1 : bytesInMemoryHOL ms.pc (encodeInsn (.binopRI (x64Sh sh) .z64 r1 1))
        ms.mem s1.memDomain := by
      rw [← h1]; exact hbm
    have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
        some (.binopRI (x64Sh sh) .z64 r1 i, 3) := by
      rw [h1]
      exact decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbm1
        (decode_binopRI_D1 (x64Sh sh) r1 hr1 (x64Sh_hop sh)) (by rw [← h1, hlen])
    exact finish (hq_of 3 hlen.symm hdec) (hsafe_of 3 hdec hlen.symm)
  · have hs : -128 ≤ i.toInt ∧ i.toInt ≤ 127 := by
      have ht : i.toInt = (i.toNat : Int) := by
        rw [BitVec.toInt_eq_toNat_cond]
        rw [if_pos (by omega : 2 * i.toNat < 2 ^ 64)]
      constructor <;> omega
    have hlen : (encodeInsn (.binopRI (x64Sh sh) .z64 r1 i)).length = 4 := by
      rw [encodeInsn_binopRI_C1 (x64Sh sh) r1 hr1 i (x64Sh_hop sh) h1 hs]
      simp [binopRIC1Bytes]
    have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
        some (.binopRI (x64Sh sh) .z64 r1 i, 4) :=
      decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbm
        (decode_binopRI_C1 (x64Sh sh) r1 hr1 i (x64Sh_hop sh) h1 hs) (by rw [hlen])
    exact finish (hq_of 4 hlen.symm hdec) (hsafe_of 4 hdec hlen.symm)

/-- The register shift encoding is the lowering's instruction. -/
theorem x64Enc_shiftReg (sh : Shift) (r1 r2 r3 : Nat)
    (h : asmOkExact (.inst (.arith (.shift sh r1 r2 (.reg r3)))) x64Config = true) :
    x64Target.config.encode (.inst (.arith (.shift sh r1 r2 (.reg r3)))) =
      encodeInsn (.binopRR (x64Sh sh) .z64 r1 r3) := by
  obtain ⟨-, hr1ok, -, hr3ok, hr3⟩ := shiftReg_ok sh r1 r2 r3 h
  have hr1 : r1 < 16 := jumpReg_reg_lt r1 hr1ok
  have hr3lt : r3 < 16 := jumpReg_reg_lt r3 hr3ok
  have hdst : totalNum2Zreg r1 = r1 := totalNum2Zreg_eq r1 hr1
  have hsrc : totalNum2Zreg r3 = r3 := totalNum2Zreg_eq r3 hr3lt
  have hflat : (x64Ast (.inst (.arith (.shift sh r1 r2 (.reg r3))))).flatMap encodeInsn =
      encodeInsn (.binopRR (x64Sh sh) .z64 r1 r3) := by
    simp only [x64Ast, x64Inst, hdst, hsrc]
    simp
  have hne : encodeInsn (.binopRR (x64Sh sh) .z64 r1 r3) ≠ [] := by
    rw [hr3]
    cases sh <;> interval_cases r1 <;> decide
  exact x64Enc_of_flatMap _ _ hflat hne

/-- The closed model executes a register shift. -/
theorem execInsn_binopRR_shift (sh : Shift) (dst src : Nat) (len : Nat) (s : X64State) :
    execInsn (.binopRR (x64Sh sh) .z64 dst src) len s =
      { (writeRegSized .z64 dst
          (wordShift sh (readReg s dst) (readReg s src).toNat) s) with
        flags := binopFlags (x64Sh sh) (readReg s dst) (readReg s src) s.flags } := by
  cases sh <;> rfl

/-- One `x64Next` step over a register shift writes the shifted value. -/
theorem x64Next_shiftReg (ms : X64State) (d : BitVec 64 → Prop) (sh : Shift) (r : Nat)
    (hr : r < 16)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.binopRR (x64Sh sh) .z64 r 1)) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms = { (writeReg ms r (wordShift sh (readReg ms r) (readReg ms 1).toNat)) with
      flags := binopFlags (x64Sh sh) (readReg ms r) (readReg ms 1) ms.flags,
      pc := ms.pc + BitVec.ofNat 64
        (encodeInsn (.binopRR (x64Sh sh) .z64 r 1)).length } := by
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.binopRR (x64Sh sh) .z64 r 1,
        (encodeInsn (.binopRR (x64Sh sh) .z64 r 1)).length) :=
    decode_bytesInMemory _ ms.pc ms.mem d _ _ hbm
      (decode_binopRR_shift (x64Sh sh) r hr (x64Sh_hop sh)) (by omega)
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec]
  rw [execInsn_binopRR_shift]
  simp only [writeRegSized, writeReg]

/-- The register `shift` constructor of `encoder_correct x64Target`. -/
theorem case_shiftReg (sh : Shift) (r1 r2 r3 : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.arith (.shift sh r1 r2 (.reg r3)))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.arith (.shift sh r1 r2 (.reg r3)))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.arith (.shift sh r1 r2 (.reg r3)))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  obtain ⟨hr12, hr1ok, -, hr3ok, hr3⟩ := shiftReg_ok sh r1 r2 r3 hok
  have hr1 : r1 < 16 := jumpReg_reg_lt r1 hr1ok
  have hr3lt : r3 < 16 := jumpReg_reg_lt r3 hr3ok
  have hreg1 := regOk_of_asmRegOk r1 hr1ok
  have hreg3 : r3 < x64Target.config.regCount ∧
      x64Target.config.avoidRegs.contains r3 = false := regOk_of_asmRegOk r3 hr3ok
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64
      (encodeInsn (.binopRR (x64Sh sh) .z64 r1 r3)).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
    rw [x64Enc_shiftReg sh r1 r2 r3 hok]
  have hs2regs : ∀ x, s2.regs x =
      if x = r1 then wordShift sh (s1.regs r1) (s1.regs 1).toNat else s1.regs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, arithUpd, regImm, AsmSem.readReg, updReg,
      assertState, hr12, hr3]
  have hs2failed : s2.failed =
      (!(decide ((s1.regs 1).toNat < 64)) || s1.failed) := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, arithUpd, regImm, AsmSem.readReg, updReg,
      assertState, hr12, hr3]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, arithUpd, regImm, updReg, assertState, hr3]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, arithUpd, regImm, updReg, assertState, hr3]
  have hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, arithUpd, regImm, updReg, assertState, hr3]
  have hs2f : s2.failed = false := by simpa [Bool.not_eq_true'] using st.ok
  have hn : (s1.regs 1).toNat < 64 := by
    by_contra hge
    have hf : decide ((s1.regs 1).toNat < 64) = false := by
      simp [hge]
    have hs2t : s2.failed = true := by
      rw [← st.upd]
      simp only [asmUpd, instUpd, updPc, arithUpd, regImm, AsmSem.readReg, updReg, assertState,
        hr12, hr3, hf, Bool.not_false, Bool.true_or]
    have hok' : ¬ s2.failed := st.ok
    rw [hs2t] at hok'
    exact hok' rfl
  have hdom : s2.memDomain = s1.memDomain := hs2dom
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.binopRR (x64Sh sh) .z64 r1 r3)) ms.mem
      s1.memDomain := by
    rw [st.pc]
    have h' := st.bytesTarget
    rw [x64Enc_shiftReg sh r1 r2 r3 hok] at h'
    exact h'
  have hcode : allPcs (x64Target.config.encode
      (.inst (.arith (.shift sh r1 r2 (.reg r3))))).length s1.pc 0 ⊆ s1.memDomain :=
    bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
  have finish (hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms))
      (hsafe : StepSafe s1.memDomain ms) :
      CaseGoal (.inst (.arith (.shift sh r1 r2 (.reg r3)))) s1 s2 ms := by
    exact encoderCaseStep _ s1 s2 ms 0 hdom hcode
      (by
        intro k hk
        have hk0 : k = 0 := by omega
        subst hk0
        simpa using hsafe)
      (by intro k hk1 hk2; omega) hq
  have hbm1 : bytesInMemoryHOL ms.pc (encodeInsn (.binopRR (x64Sh sh) .z64 r1 1))
      ms.mem s1.memDomain := by
    rw [← hr3]; exact hbm
  have hs2pc' : s2.pc = s1.pc + BitVec.ofNat 64
      (encodeInsn (.binopRR (x64Sh sh) .z64 r1 1)).length := by
    rw [hs2pc, hr3]
  have hs2regs' : ∀ x, s2.regs x =
      if x = r1 then wordShift sh (s1.regs r1) (s1.regs 1).toNat else s1.regs x := hs2regs
  have hdomN := bytesInMemoryHOL_domain _ _ _ _ hbm1
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.binopRR (x64Sh sh) .z64 r1 1,
        (encodeInsn (.binopRR (x64Sh sh) .z64 r1 1)).length) :=
    decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbm1
      (decode_binopRR_shift (x64Sh sh) r1 hr1 (x64Sh_hop sh)) (by omega)
  have hstepSafe : StepSafe s1.memDomain ms := by
    refine ⟨.binopRR (x64Sh sh) .z64 r1 1, _, hdec, ?_, ?_⟩
    · intro j hj; exact hdomN j hj
    · intro a ha; simp [x64Touched] at ha
  have hnext := x64Next_shiftReg ms s1.memDomain sh r1 hr1 hbm1 st.failed
  have hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms) := by
    show targetStateRel x64Target s2 (x64Next ms)
    rw [hnext]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [x64Target_stateOk, x64StateOk, writeReg, st.failed, Bool.not_false]
    · show ms.pc + BitVec.ofNat 64
          (encodeInsn (.binopRR (x64Sh sh) .z64 r1 1)).length = s2.pc
      rw [st.pc, hs2pc']
    · intro a ha
      show ms.mem a = s2.mem a
      rw [hs2mem a]
      rw [hs2dom] at ha
      exact st.mem a ha
    · intro x hx
      show readReg (writeReg ms r1
          (wordShift sh (readReg ms r1) (readReg ms 1).toNat)) x = s2.regs x
      rw [readReg_writeReg ms r1 _ x hr1 hx.1, hs2regs' x]
      by_cases hxr : x = r1
      · rw [if_pos hxr, if_pos hxr, st.reg r1 hreg1]
        have hone : readReg ms 1 = s1.regs 1 :=
          st.reg 1 (by decide)
        rw [hone]
      · rw [if_neg hxr, if_neg hxr]
        exact st.reg x hx
    · intro x hx
      show readXmm ms x = s2.fpRegs x
      rw [hs2fp x]
      exact st.fp x hx
  exact finish hq hstepSafe

end Flapjack.Compiler.Encoders.X64

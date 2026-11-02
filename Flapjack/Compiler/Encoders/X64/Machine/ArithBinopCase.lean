import Flapjack.Compiler.Encoders.X64.Machine.ConstCase

/-!
# The `binop` register and immediate cases of `encoder_correct x64Target`

`arith (binop op r1 r2 (.reg r3))` lowers either to `mov r1, r3` (when `op = or`
and `r2 = r3`, so `r2 ||| r3 = r3`) or to `binopRR op r1 r3`.  `asm_ok` forces
`r1 = r2` in the latter case, so the register-register operation reads the same
two operands the source semantics does.  The immediate form lowers to
`monop not` for `xor -1` and to `binopRI op r i` otherwise.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-- The instruction the register-register `binop` lowers to. -/
def x64BinopRRInsn (op : BinOp) (r1 r2 r3 : Nat) : X64Insn :=
  if op = .or && r2 = r3 then .movRR .z64 r1 r3 else .binopRR (x64Bop op) .z64 r1 r3

/-- The instruction the immediate `binop` lowers to. -/
def x64BinopRIImmInsn (op : BinOp) (r : Nat) (i : BitVec 64) : X64Insn :=
  if op = .xor && i = -1 then .monop .znot .z64 r else .binopRI (x64Bop op) .z64 r i

/-- `asm_ok` of a register-register `binop` splits into its register checks and
the two-register constraint. -/
theorem binopRR_ok (op : BinOp) (r1 r2 r3 : Nat)
    (h : asmOkExact (.inst (.arith (.binop op r1 r2 (.reg r3)))) x64Config = true) :
    (r1 = r2 ∨ op = .or ∧ r3 = r2) ∧
      asmRegOkExact r1 x64Config = true ∧
      asmRegOkExact r2 x64Config = true ∧ asmRegOkExact r3 x64Config = true := by
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, asmRegImmOkExact, x64Config,
    Bool.and_eq_true, Bool.or_eq_true, Bool.not_true, Bool.false_or] at h
  simp at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- `asm_ok` of an immediate `binop` splits into the two-register equality, the
register checks and the immediate-range check. -/
theorem binopRI_ok (op : BinOp) (r1 r2 : Nat) (i : BitVec 64)
    (h : asmOkExact (.inst (.arith (.binop op r1 r2 (.imm i)))) x64Config = true) :
    r1 = r2 ∧ asmRegOkExact r1 x64Config = true ∧
      asmRegOkExact r2 x64Config = true ∧
      (((Sum.inl op : Sum BinOp Cmp) == (Sum.inl BinOp.xor : Sum BinOp Cmp)) = true ∧
          i = -1 ∨
        (x64Min32.toInt ≤ i.toInt ∧ i.toInt ≤ x64Max32.toInt)) := by
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, asmRegImmOkExact, x64Config,
    Bool.and_eq_true, Bool.or_eq_true, Bool.not_true, Bool.false_or] at h
  simp at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- The value of a source `binop`. -/
def binopVal (op : BinOp) (a b : BitVec 64) : BitVec 64 :=
  match op with
  | .add => a + b | .sub => a - b | .and => a &&& b | .or => a ||| b | .xor => a ^^^ b

/-- The `binop` value computed by the closed model is the source semantics'
`binop_upd` value. -/
theorem binopValue_x64Bop (op : BinOp) (a b : BitVec 64) :
    binopValue (x64Bop op) a b = binopVal op a b := by
  cases op <;> rfl

/-- The `binop` value written by `binop_upd`. -/
theorem binopUpd_value (r : Nat) (op : BinOp) (a b : BitVec 64) (s : AsmState 64) :
    binopUpd r op a b s = updReg r (binopVal op a b) s := by
  cases op <;> rfl

/-- The source binops map into the eight arithmetic opcodes. -/
theorem x64Bop_hop (bop : BinOp) :
    x64Bop bop = .zadd ∨ x64Bop bop = .zor ∨ x64Bop bop = .zadc ∨
      x64Bop bop = .zsbb ∨ x64Bop bop = .zand ∨ x64Bop bop = .zsub ∨
      x64Bop bop = .zxor ∨ x64Bop bop = .zcmp := by
  cases bop <;> simp [x64Bop]

/-- The source binops never map to `test`. -/
theorem x64Bop_ne_test (bop : BinOp) : x64Bop bop ≠ .ztest := by
  cases bop <;> simp [x64Bop]

/-- The source binops never map to a shift opcode. -/
theorem x64Bop_code_div (bop : BinOp) : (x64Bop bop).code / 8 ≠ 1 := by
  cases bop <;> simp [x64Bop, ZBinopName.code]

/-- The immediate arithmetic encoding is nonempty under the range check. -/
theorem binopRI_z64_ne (bop : BinOp) (dst : Nat) (imm : BitVec 64) (hd : dst < 16)
    (hlo : -(2 ^ 31 : Int) ≤ imm.toInt) (hhi : imm.toInt < 2 ^ 31) :
    encodeInsn (.binopRI (x64Bop bop) .z64 dst imm) ≠ [] := by
  by_cases hs : -128 ≤ imm.toInt ∧ imm.toInt ≤ 127
  · rw [encodeInsn_binopRI_83 (x64Bop bop) dst hd imm (x64Bop_ne_test bop)
      (x64Bop_code_div bop) hs]
    simp [binopRI83Bytes]
  · by_cases hne : dst = 0
    · subst hne
      rw [encodeInsn_binopRI_rax (x64Bop bop) imm (x64Bop_hop bop) hs hlo hhi]
      simp [binopRIRaxBytes]
    · rw [encodeInsn_binopRI_81 (x64Bop bop) dst hd imm (x64Bop_hop bop) hs hne hlo hhi]
      simp [binopRI81Bytes]

/-- The zeroing `not` is nonempty. -/
theorem monop_not_ne (r : Nat) (hr : r < 16) :
    encodeInsn (.monop .znot .z64 r) ≠ [] := by
  intro h
  interval_cases r <;> simp [encodeInsn, eGenRmReg, eModRM] at h

/-- Comparing with `xor` through the `Sum` carrier. -/
theorem bop_xor_beq (bop : BinOp) :
    ((Sum.inl bop : Sum BinOp Cmp) == (Sum.inl BinOp.xor : Sum BinOp Cmp)) = true ↔
      bop = .xor := by
  cases bop <;> decide

/-- The `asm_ok` `xor -1` condition is the lowering's condition. -/
theorem bop_xor_cond (bop : BinOp) (i : BitVec 64) :
    (((Sum.inl bop : Sum BinOp Cmp) == (Sum.inl BinOp.xor : Sum BinOp Cmp)) = true ∧
        i = -1) ↔
      (decide (bop = .xor) && decide (i = -1)) = true := by
  rw [bop_xor_beq, Bool.and_eq_true]
  simp only [decide_eq_true_eq]

/-- The bounds of `x64Min32` and `x64Max32` as integers. -/
theorem x64Min32_toInt : x64Min32.toInt = -(2 ^ 31 : Int) := by decide

theorem x64Max32_toInt : x64Max32.toInt = 2 ^ 31 - 1 := by decide

/-- The immediate `binop` encoding is the lowering's instruction. -/
theorem x64Enc_binopRI (bop : BinOp) (r1 r2 : Nat) (i : BitVec 64)
    (h : asmOkExact (.inst (.arith (.binop bop r1 r2 (.imm i)))) x64Config = true) :
    x64Target.config.encode (.inst (.arith (.binop bop r1 r2 (.imm i)))) =
      encodeInsn (x64BinopRIImmInsn bop r1 i) := by
  obtain ⟨hr12, hr1ok, -, himm⟩ := binopRI_ok bop r1 r2 i h
  have hr1 : r1 < 16 := jumpReg_reg_lt r1 hr1ok
  have hdst : totalNum2Zreg r1 = r1 := totalNum2Zreg_eq r1 hr1
  have hflat : (x64Ast (.inst (.arith (.binop bop r1 r2 (.imm i))))).flatMap encodeInsn =
      encodeInsn (x64BinopRIImmInsn bop r1 i) := by
    simp only [x64Ast, x64Inst, x64BinopRIImmInsn, hdst]
    by_cases hc : bop = .xor && i = -1
    · simp only [if_pos hc]; simp
    · simp only [if_neg hc]; simp
  have hne : encodeInsn (x64BinopRIImmInsn bop r1 i) ≠ [] := by
    by_cases hc : bop = .xor && i = -1
    · rw [x64BinopRIImmInsn, if_pos hc]
      exact monop_not_ne r1 hr1
    · have hb : ¬(((Sum.inl bop : Sum BinOp Cmp) ==
          (Sum.inl BinOp.xor : Sum BinOp Cmp)) = true ∧ i = -1) := by
        intro hh
        exact hc ((bop_xor_cond bop i).mp hh)
      obtain ⟨hlo, hhi⟩ := himm.resolve_left hb
      rw [x64Min32_toInt] at hlo
      rw [x64Max32_toInt] at hhi
      rw [x64BinopRIImmInsn, if_neg hc]
      exact binopRI_z64_ne bop r1 i hr1 hlo (by omega)
  exact x64Enc_of_flatMap _ _ hflat hne

/-- A register-to-register 64-bit move is three bytes. -/
theorem encodeInsn_movRR_z64_length (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    (encodeInsn (.movRR .z64 dst src)).length = 3 := by
  interval_cases dst <;> interval_cases src <;> decide

/-- The register-to-register move is nonempty. -/
theorem movRR_z64_ne (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    encodeInsn (.movRR .z64 dst src) ≠ [] := by
  intro h
  have hlen := encodeInsn_movRR_z64_length dst src hd hs
  rw [h] at hlen
  simp at hlen

/-- The register-register arithmetic encoding is nonempty. -/
theorem binopRR_z64_ne (op : ZBinopName) (dst src : Nat) (hop : op.code < 8) :
    encodeInsn (.binopRR op .z64 dst src) ≠ [] := by
  intro h
  simp only [encodeInsn] at h
  split at h
  · simp [eGenRmReg, eModRM] at h
  · split at h
    · rename_i ho
      omega
    · simp [eGenRmReg, eModRM] at h

/-- The register-register `binop` encoding is the lowering's instruction. -/
theorem x64Enc_binopRR (op : BinOp) (r1 r2 r3 : Nat)
    (h : asmOkExact (.inst (.arith (.binop op r1 r2 (.reg r3)))) x64Config = true) :
    x64Target.config.encode (.inst (.arith (.binop op r1 r2 (.reg r3)))) =
      encodeInsn (x64BinopRRInsn op r1 r2 r3) := by
  obtain ⟨-, hr1, hr2, hr3⟩ := binopRR_ok op r1 r2 r3 h
  have h1 : r1 < 16 := jumpReg_reg_lt r1 hr1
  have h3 : r3 < 16 := jumpReg_reg_lt r3 hr3
  have hdst : totalNum2Zreg r1 = r1 := totalNum2Zreg_eq r1 h1
  have hsrc : totalNum2Zreg r3 = r3 := totalNum2Zreg_eq r3 h3
  have hflat : (x64Ast (.inst (.arith (.binop op r1 r2 (.reg r3))))).flatMap encodeInsn =
      encodeInsn (x64BinopRRInsn op r1 r2 r3) := by
    simp only [x64Ast, x64Inst, x64BinopRRInsn, hdst, hsrc]
    by_cases hc : op = .or && r2 = r3
    · simp only [if_pos hc]; simp
    · simp only [if_neg hc]; simp
  have hne : encodeInsn (x64BinopRRInsn op r1 r2 r3) ≠ [] := by
    by_cases hc : op = .or && r2 = r3
    · rw [x64BinopRRInsn, if_pos hc]
      exact movRR_z64_ne r1 r3 h1 h3
    · have hop : (x64Bop op).code < 8 := by
        cases op <;> simp [x64Bop, ZBinopName.code]
      rw [x64BinopRRInsn, if_neg hc]
      exact binopRR_z64_ne (x64Bop op) r1 r3 hop
  exact x64Enc_of_flatMap _ _ hflat hne

/-- The closed model executes an immediate arithmetic instruction by writing
the operation's value and setting the flags. -/
theorem execInsn_binopRI (bop : BinOp) (dst : Nat) (imm : BitVec 64) (len : Nat)
    (s : X64State) :
    execInsn (.binopRI (x64Bop bop) .z64 dst imm) len s =
      { (writeRegSized .z64 dst (binopValue (x64Bop bop) (readReg s dst) imm) s) with
        flags := binopFlags (x64Bop bop) (readReg s dst) imm s.flags } := by
  cases bop <;> rfl

/-- The closed model executes `not` by writing the complement. -/
theorem execInsn_monop_not (dst : Nat) (len : Nat) (s : X64State) :
    execInsn (.monop .znot .z64 dst) len s =
      writeRegSized .z64 dst (~~~(readReg s dst)) s := rfl

/-- One `x64Next` step over an immediate arithmetic instruction writes the
operation's value and sets the flags. -/
theorem x64Next_binopRI (ms : X64State) (bop : BinOp)
    (r : Nat) (i : BitVec 64) (len : Nat)
    (hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.binopRI (x64Bop bop) .z64 r i, len))
    (hlen : (encodeInsn (.binopRI (x64Bop bop) .z64 r i)).length = len)
    (hfailed : ms.failed = false) :
    x64Next ms = { (writeReg ms r (binopValue (x64Bop bop) (readReg ms r) i)) with
      flags := binopFlags (x64Bop bop) (readReg ms r) i ms.flags,
      pc := ms.pc + BitVec.ofNat 64
        (encodeInsn (.binopRI (x64Bop bop) .z64 r i)).length } := by
  rw [hlen]
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec]
  rw [execInsn_binopRI]
  simp only [writeRegSized, writeReg]

/-- One `x64Next` step over `not` writes the complement of the register. -/
theorem x64Next_monop_not (ms : X64State) (d : BitVec 64 → Prop) (r : Nat) (hr : r < 16)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.monop .znot .z64 r)) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms = { (writeReg ms r (~~~(readReg ms r))) with
      pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.monop .znot .z64 r)).length } := by
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.monop .znot .z64 r, (encodeInsn (.monop .znot .z64 r)).length) :=
    decode_bytesInMemory _ ms.pc ms.mem d _ _ hbm (decode_monop_z64 .znot r hr) (by omega)
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec]
  rw [execInsn_monop_not]
  simp only [writeRegSized, writeReg]

/-- One `x64Next` step over a register move copies the source register. -/
theorem x64Next_binopRR_mov (ms : X64State) (d : BitVec 64 → Prop) (r1 r3 : Nat)
    (hr1 : r1 < 16) (hr3 : r3 < 16)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.movRR .z64 r1 r3)) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms = { (writeReg ms r1 (readReg ms r3)) with
      pc := ms.pc + BitVec.ofNat 64 3 } := by
  have hlen := encodeInsn_movRR_z64_length r1 r3 hr1 hr3
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.movRR .z64 r1 r3, 3) :=
    decode_bytesInMemory _ ms.pc ms.mem d _ _ hbm (decode_movRR_z64 r1 r3 hr1 hr3)
      (by rw [hlen])
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec, execInsn, writeRegSized,
    writeReg]

/-- The closed model executes a register-register arithmetic instruction by
writing the operation's value and setting the flags. -/
theorem execInsn_binopRR (bop : BinOp) (dst src : Nat) (len : Nat) (s : X64State) :
    execInsn (.binopRR (x64Bop bop) .z64 dst src) len s =
      { (writeRegSized .z64 dst
          (binopValue (x64Bop bop) (readReg s dst) (readReg s src)) s) with
        flags := binopFlags (x64Bop bop) (readReg s dst) (readReg s src) s.flags } := by
  cases bop <;> rfl

/-- `targetStateRel`'s register hypothesis from `asm_ok`'s register check. -/
theorem regOk_of_asmRegOk (r : Nat) (h : asmRegOkExact r x64Config = true) :
    r < x64Target.config.regCount ∧ x64Target.config.avoidRegs.contains r = false := by
  refine ⟨?_, ?_⟩
  · simpa [x64Target_config, x64Config] using jumpReg_reg_lt r h
  · simpa [x64Target_config, x64Config] using jumpReg_reg_avoid r h

/-- Negation of a 64-bit word is its `xor` with all ones. -/
theorem neg_one_eq_allOnes : (-1 : BitVec 64) = BitVec.allOnes 64 := by decide

/-- `xor` with all ones complements the register. -/
theorem xor_allOnes_eq (a : BitVec 64) :
    a ^^^ (18446744073709551615#64) = ~~~a := by
  rw [show (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 from by decide,
    BitVec.xor_allOnes]

/-- The immediate `binop` constructor of `encoder_correct x64Target`: one
`x64Next` step writes the operation's value to the destination register. -/
theorem case_binopRI (bop : BinOp) (r1 r2 : Nat) (i : BitVec 64) (s1 s2 : AsmState 64)
    (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.arith (.binop bop r1 r2 (.imm i)))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.arith (.binop bop r1 r2 (.imm i)))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.arith (.binop bop r1 r2 (.imm i)))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  obtain ⟨hr12, hr1ok, -, himm⟩ := binopRI_ok bop r1 r2 i hok
  have hr1 : r1 < 16 := jumpReg_reg_lt r1 hr1ok
  have hreg1 := regOk_of_asmRegOk r1 hr1ok
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64
      (encodeInsn (x64BinopRIImmInsn bop r1 i)).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
    rw [x64Enc_binopRI bop r1 r2 i hok]
  have hs2regs : ∀ x, s2.regs x =
      if x = r1 then binopVal bop (s1.regs r1) i else s1.regs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, arithUpd, binopUpd_value, regImm, AsmSem.readReg,
      updReg, hr12]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, arithUpd, binopUpd_value, updReg]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, arithUpd, binopUpd_value, updReg]
  have hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, arithUpd, binopUpd_value, updReg]
  have hdom : s2.memDomain = s1.memDomain := hs2dom
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (x64BinopRIImmInsn bop r1 i)) ms.mem
      s1.memDomain := by
    rw [st.pc]
    have h' := st.bytesTarget
    rw [x64Enc_binopRI bop r1 r2 i hok] at h'
    exact h'
  have hcode : allPcs (x64Target.config.encode
      (.inst (.arith (.binop bop r1 r2 (.imm i))))).length s1.pc 0 ⊆ s1.memDomain :=
    bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
  have finish (hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms))
      (hsafe : StepSafe s1.memDomain ms) :
      CaseGoal (.inst (.arith (.binop bop r1 r2 (.imm i)))) s1 s2 ms := by
    exact encoderCaseStep _ s1 s2 ms 0 hdom hcode
      (by
        intro k hk
        have hk0 : k = 0 := by omega
        subst hk0
        simpa using hsafe)
      (by intro k hk1 hk2; omega) hq
  by_cases hc : bop = .xor && i = -1
  · -- `not r1`
    have hc_raw : (decide (bop = .xor) && decide (i = -1)) = true := hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have hbx : bop = .xor := hc.1
    have hi1 : i = -1 := hc.2
    have hinsn : x64BinopRIImmInsn bop r1 i = .monop .znot .z64 r1 := by
      rw [x64BinopRIImmInsn, if_pos hc_raw]
    have hs2pc' : s2.pc = s1.pc + BitVec.ofNat 64
        (encodeInsn (.monop .znot .z64 r1)).length := by
      rw [hs2pc, hinsn]
    have hbmM : bytesInMemoryHOL ms.pc (encodeInsn (.monop .znot .z64 r1))
        ms.mem s1.memDomain := by
      rw [← hinsn]; exact hbm
    have hval : binopVal bop (s1.regs r1) i = ~~~(s1.regs r1) := by
      rw [hbx, hi1]
      simp [binopVal, xor_allOnes_eq]
    have hnext := x64Next_monop_not ms s1.memDomain r1 hr1 hbmM st.failed
    have hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms) := by
      show targetStateRel x64Target s2 (x64Next ms)
      rw [hnext]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [x64Target_stateOk, x64StateOk, writeReg, st.failed, Bool.not_false]
      · show ms.pc + BitVec.ofNat 64 (encodeInsn (.monop .znot .z64 r1)).length = s2.pc
        rw [st.pc, hs2pc']
      · intro a ha
        show ms.mem a = s2.mem a
        rw [hs2mem a]
        rw [hs2dom] at ha
        exact st.mem a ha
      · intro x hx
        show readReg (writeReg ms r1 (~~~(readReg ms r1))) x = s2.regs x
        rw [readReg_writeReg ms r1 _ x hr1 hx.1, hs2regs x]
        by_cases hxr : x = r1
        · rw [if_pos hxr, if_pos hxr, hval, st.reg r1 hreg1]
        · rw [if_neg hxr, if_neg hxr]
          exact st.reg x hx
      · intro x hx
        show readXmm ms x = s2.fpRegs x
        rw [hs2fp x]
        exact st.fp x hx
    have hstepSafe : StepSafe s1.memDomain ms := by
      have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
          some (.monop .znot .z64 r1, (encodeInsn (.monop .znot .z64 r1)).length) :=
        decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbmM
          (decode_monop_z64 .znot r1 hr1) (by omega)
      have hdomN := bytesInMemoryHOL_domain _ _ _ _ hbmM
      refine ⟨.monop .znot .z64 r1, _, hdec, ?_, ?_⟩
      · intro j hj; exact hdomN j hj
      · intro a ha; simp [x64Touched] at ha
    exact finish hq hstepSafe
  · have hbx : ¬(bop = .xor ∧ i = -1) := by
      intro hh
      exact hc (by simp [hh])
    have hb : ¬(((Sum.inl bop : Sum BinOp Cmp) ==
        (Sum.inl BinOp.xor : Sum BinOp Cmp)) = true ∧ i = -1) := by
      intro hh
      exact hbx ⟨(bop_xor_beq bop).mp hh.1, hh.2⟩
    obtain ⟨hlo0, hhi0⟩ := himm.resolve_left hb
    have hlo : -(2 ^ 31 : Int) ≤ i.toInt := by rw [x64Min32_toInt] at hlo0; exact hlo0
    have hhi : i.toInt < 2 ^ 31 := by rw [x64Max32_toInt] at hhi0; omega
    have hinsn : x64BinopRIImmInsn bop r1 i = .binopRI (x64Bop bop) .z64 r1 i := by
      rw [x64BinopRIImmInsn, if_neg hc]
    have hval : binopVal bop (s1.regs r1) i =
        binopValue (x64Bop bop) (readReg ms r1) i := by
      rw [binopValue_x64Bop, st.reg r1 hreg1]
    have hs2pc' : s2.pc = s1.pc + BitVec.ofNat 64
        (encodeInsn (.binopRI (x64Bop bop) .z64 r1 i)).length := by
      rw [hs2pc, hinsn]
    have hbmM : bytesInMemoryHOL ms.pc (encodeInsn (.binopRI (x64Bop bop) .z64 r1 i))
        ms.mem s1.memDomain := by
      rw [← hinsn]; exact hbm
    have hdomN := bytesInMemoryHOL_domain _ _ _ _ hbmM
    have hq_of : ∀ (len : Nat), len = (encodeInsn (.binopRI (x64Bop bop) .z64 r1 i)).length →
        (decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
          some (.binopRI (x64Bop bop) .z64 r1 i, len)) →
        targetStateRel x64Target s2 (x64Next^[0 + 1] ms) := by
      intro len hlen hdec
      have hnext := x64Next_binopRI ms bop r1 i len hdec hlen.symm st.failed
      show targetStateRel x64Target s2 (x64Next ms)
      rw [hnext]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [x64Target_stateOk, x64StateOk, writeReg, st.failed, Bool.not_false]
      · show ms.pc + BitVec.ofNat 64
            (encodeInsn (.binopRI (x64Bop bop) .z64 r1 i)).length = s2.pc
        rw [st.pc, hs2pc']
      · intro a ha
        show ms.mem a = s2.mem a
        rw [hs2mem a]
        rw [hs2dom] at ha
        exact st.mem a ha
      · intro x hx
        show readReg (writeReg ms r1
            (binopValue (x64Bop bop) (readReg ms r1) i)) x = s2.regs x
        rw [readReg_writeReg ms r1 _ x hr1 hx.1, hs2regs x]
        by_cases hxr : x = r1
        · rw [if_pos hxr, if_pos hxr, ← hval]
        · rw [if_neg hxr, if_neg hxr]
          exact st.reg x hx
      · intro x hx
        show readXmm ms x = s2.fpRegs x
        rw [hs2fp x]
        exact st.fp x hx
    have hsafe_of : ∀ (len : Nat),
        (decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
          some (.binopRI (x64Bop bop) .z64 r1 i, len)) →
        len = (encodeInsn (.binopRI (x64Bop bop) .z64 r1 i)).length →
        StepSafe s1.memDomain ms := by
      intro len hdec hlen
      refine ⟨.binopRI (x64Bop bop) .z64 r1 i, len, hdec, ?_, ?_⟩
      · intro j hj
        exact hdomN j (by omega)
      · intro a ha; simp [x64Touched] at ha
    by_cases hs : -128 ≤ i.toInt ∧ i.toInt ≤ 127
    · -- `83` form
      have hlen : (encodeInsn (.binopRI (x64Bop bop) .z64 r1 i)).length = 4 := by
        rw [encodeInsn_binopRI_83 (x64Bop bop) r1 hr1 i (x64Bop_ne_test bop)
          (x64Bop_code_div bop) hs]
        simp [binopRI83Bytes]
      have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
          some (.binopRI (x64Bop bop) .z64 r1 i, 4) :=
        decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbmM
          (decode_binopRI_83 (x64Bop bop) r1 hr1 i (x64Bop_ne_test bop)
            (x64Bop_code_div bop) hs) (by rw [hlen])
      exact finish (hq_of 4 hlen.symm hdec) (hsafe_of 4 hdec hlen.symm)
    · by_cases hz : r1 = 0
      · -- accumulator form
        subst hz
        have hlen : (encodeInsn (.binopRI (x64Bop bop) .z64 0 i)).length = 6 := by
          rw [encodeInsn_binopRI_rax (x64Bop bop) i (x64Bop_hop bop) hs hlo hhi]
          simp [binopRIRaxBytes]
        have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
            some (.binopRI (x64Bop bop) .z64 0 i, 6) :=
          decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbmM
            (decode_binopRI_rax (x64Bop bop) i (x64Bop_hop bop) hs hlo hhi) (by rw [hlen])
        exact finish (hq_of 6 hlen.symm hdec) (hsafe_of 6 hdec hlen.symm)
      · -- `81` form
        have hlen : (encodeInsn (.binopRI (x64Bop bop) .z64 r1 i)).length = 7 := by
          rw [encodeInsn_binopRI_81 (x64Bop bop) r1 hr1 i (x64Bop_hop bop) hs hz hlo hhi]
          simp [binopRI81Bytes]
        have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
            some (.binopRI (x64Bop bop) .z64 r1 i, 7) :=
          decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbmM
            (decode_binopRI_81 (x64Bop bop) r1 hr1 i (x64Bop_hop bop) hs hz hlo hhi)
            (by rw [hlen])
        exact finish (hq_of 7 hlen.symm hdec) (hsafe_of 7 hdec hlen.symm)

theorem x64Next_binopRR (ms : X64State) (d : BitVec 64 → Prop) (bop : BinOp)
    (r1 r3 : Nat) (hr1 : r1 < 16) (hr3 : r3 < 16)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.binopRR (x64Bop bop) .z64 r1 r3)) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms = { (writeReg ms r1 (binopValue (x64Bop bop) (readReg ms r1) (readReg ms r3))) with
      flags := binopFlags (x64Bop bop) (readReg ms r1) (readReg ms r3) ms.flags,
      pc := ms.pc + BitVec.ofNat 64
        (encodeInsn (.binopRR (x64Bop bop) .z64 r1 r3)).length } := by
  have hop : (x64Bop bop).code < 8 := by cases bop <;> simp [x64Bop, ZBinopName.code]
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.binopRR (x64Bop bop) .z64 r1 r3,
        (encodeInsn (.binopRR (x64Bop bop) .z64 r1 r3)).length) :=
    decode_bytesInMemory _ ms.pc ms.mem d _ _ hbm
      (decode_binopRR_z64 (x64Bop bop) r1 r3 hr1 hr3 hop) (by omega)
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec]
  rw [execInsn_binopRR]
  simp only [writeRegSized, writeReg]

/-- The register-register `binop` constructor of `encoder_correct x64Target`:
one `x64Next` step writes the operation's value to the destination register. -/
theorem case_binopRR (bop : BinOp) (r1 r2 r3 : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.arith (.binop bop r1 r2 (.reg r3)))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.arith (.binop bop r1 r2 (.reg r3)))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.arith (.binop bop r1 r2 (.reg r3)))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  obtain ⟨hcond, hr1ok, hr2ok, hr3ok⟩ := binopRR_ok bop r1 r2 r3 hok
  have hr1 : r1 < 16 := jumpReg_reg_lt r1 hr1ok
  have hr2 : r2 < 16 := jumpReg_reg_lt r2 hr2ok
  have hr3 : r3 < 16 := jumpReg_reg_lt r3 hr3ok
  have hreg1 := regOk_of_asmRegOk r1 hr1ok
  have hreg2 := regOk_of_asmRegOk r2 hr2ok
  have hreg3 := regOk_of_asmRegOk r3 hr3ok
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 (encodeInsn (x64BinopRRInsn bop r1 r2 r3)).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
    rw [x64Enc_binopRR bop r1 r2 r3 hok]
  have hs2regs : ∀ x, s2.regs x =
      if x = r1 then binopVal bop (s1.regs r2) (s1.regs r3) else s1.regs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, arithUpd, binopUpd_value, regImm, AsmSem.readReg,
      updReg]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, arithUpd, binopUpd_value, updReg]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, arithUpd, binopUpd_value, updReg]
  have hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, arithUpd, binopUpd_value, updReg]
  have hdom : s2.memDomain = s1.memDomain := hs2dom
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (x64BinopRRInsn bop r1 r2 r3)) ms.mem
      s1.memDomain := by
    rw [st.pc]
    have h' := st.bytesTarget
    rw [x64Enc_binopRR bop r1 r2 r3 hok] at h'
    exact h'
  have hcode : allPcs (x64Target.config.encode
      (.inst (.arith (.binop bop r1 r2 (.reg r3))))).length s1.pc 0 ⊆ s1.memDomain :=
    bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
  have finish (hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms))
      (hsafe : StepSafe s1.memDomain ms) :
      CaseGoal (.inst (.arith (.binop bop r1 r2 (.reg r3)))) s1 s2 ms := by
    exact encoderCaseStep _ s1 s2 ms 0 hdom hcode
      (by
        intro k hk
        have hk0 : k = 0 := by omega
        subst hk0
        simpa using hsafe)
      (by intro k hk1 hk2; omega) hq
  by_cases hc : bop = .or && r2 = r3
  · -- `mov r1, r3`
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have hbor : bop = .or := hc.1
    have hr23 : r2 = r3 := hc.2
    have hinsn : x64BinopRRInsn bop r1 r2 r3 = .movRR .z64 r1 r3 := by
      simp [x64BinopRRInsn, hbor, hr23]
    have hval : binopVal bop (s1.regs r2) (s1.regs r3) = s1.regs r3 := by
      rw [hbor, hr23]
      simp [binopVal]
    have hs2pc' : s2.pc = s1.pc + BitVec.ofNat 64 3 := by
      rw [hs2pc, hinsn, encodeInsn_movRR_z64_length r1 r3 hr1 hr3]
    have hbmM : bytesInMemoryHOL ms.pc (encodeInsn (.movRR .z64 r1 r3)) ms.mem
        s1.memDomain := by
      rw [← hinsn]; exact hbm
    have hdomN := bytesInMemoryHOL_domain _ _ _ _ hbmM
    have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
        some (.movRR .z64 r1 r3, 3) :=
      decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbmM
        (decode_movRR_z64 r1 r3 hr1 hr3) (by rw [encodeInsn_movRR_z64_length r1 r3 hr1 hr3])
    have hstepSafe : StepSafe s1.memDomain ms := by
      refine ⟨.movRR .z64 r1 r3, _, hdec, ?_, ?_⟩
      · intro j hj
        exact hdomN j (by rw [encodeInsn_movRR_z64_length r1 r3 hr1 hr3]; exact hj)
      · intro a ha; simp [x64Touched] at ha
    have hnext := x64Next_binopRR_mov ms s1.memDomain r1 r3 hr1 hr3 hbmM st.failed
    have hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms) := by
      show targetStateRel x64Target s2 (x64Next ms)
      rw [hnext]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [x64Target_stateOk, x64StateOk, writeReg, st.failed, Bool.not_false]
      · show ms.pc + BitVec.ofNat 64 3 = s2.pc
        rw [st.pc, hs2pc']
      · intro a ha
        show ms.mem a = s2.mem a
        rw [hs2mem a]
        rw [hs2dom] at ha
        exact st.mem a ha
      · intro x hx
        show readReg (writeReg ms r1 (readReg ms r3)) x = s2.regs x
        rw [readReg_writeReg ms r1 _ x hr1 hx.1, hs2regs x]
        by_cases hxr : x = r1
        · rw [if_pos hxr, if_pos hxr, hval]
          exact st.reg r3 hreg3
        · simp only [hxr, if_false]
          exact st.reg x hx
      · intro x hx
        show readXmm ms x = s2.fpRegs x
        rw [hs2fp x]
        exact st.fp x hx
    exact finish hq hstepSafe
  · -- `binopRR r1, r3`
    have hc' : ¬(bop = .or ∧ r2 = r3) := by
      intro hh
      exact hc (by simpa using hh)
    have hr12 : r1 = r2 := by
      rcases hcond with h | h
      · exact h
      · exact absurd h (by intro hh; exact hc' ⟨hh.1, hh.2.symm⟩)
    have hinsn : x64BinopRRInsn bop r1 r2 r3 = .binopRR (x64Bop bop) .z64 r1 r3 := by
      simp [x64BinopRRInsn, hc]
    have hs2pc' : s2.pc = s1.pc + BitVec.ofNat 64
        (encodeInsn (.binopRR (x64Bop bop) .z64 r1 r3)).length := by
      rw [hs2pc, hinsn]
    have hbmM : bytesInMemoryHOL ms.pc (encodeInsn (.binopRR (x64Bop bop) .z64 r1 r3))
        ms.mem s1.memDomain := by
      rw [← hinsn]; exact hbm
    have hop : (x64Bop bop).code < 8 := by cases bop <;> simp [x64Bop, ZBinopName.code]
    have hdomN := bytesInMemoryHOL_domain _ _ _ _ hbmM
    have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
        some (.binopRR (x64Bop bop) .z64 r1 r3,
          (encodeInsn (.binopRR (x64Bop bop) .z64 r1 r3)).length) :=
      decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbmM
        (decode_binopRR_z64 (x64Bop bop) r1 r3 hr1 hr3 hop) (by omega)
    have hstepSafe : StepSafe s1.memDomain ms := by
      refine ⟨.binopRR (x64Bop bop) .z64 r1 r3, _, hdec, ?_, ?_⟩
      · intro j hj; exact hdomN j hj
      · intro a ha; simp [x64Touched] at ha
    have hnext := x64Next_binopRR ms s1.memDomain bop r1 r3 hr1 hr3 hbmM st.failed
    have hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms) := by
      show targetStateRel x64Target s2 (x64Next ms)
      rw [hnext]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [x64Target_stateOk, x64StateOk, writeReg, st.failed, Bool.not_false]
      · show ms.pc + BitVec.ofNat 64
            (encodeInsn (.binopRR (x64Bop bop) .z64 r1 r3)).length = s2.pc
        rw [st.pc, hs2pc']
      · intro a ha
        show ms.mem a = s2.mem a
        rw [hs2mem a]
        rw [hs2dom] at ha
        exact st.mem a ha
      · intro x hx
        show readReg (writeReg ms r1
            (binopValue (x64Bop bop) (readReg ms r1) (readReg ms r3))) x = s2.regs x
        rw [readReg_writeReg ms r1 _ x hr1 hx.1, hs2regs x]
        by_cases hxr : x = r1
        · rw [if_pos hxr, if_pos hxr, binopValue_x64Bop]
          have h1 : readReg ms r1 = s1.regs r2 := by
            rw [hr12]; exact st.reg r2 hreg2
          rw [h1, st.reg r3 hreg3]
        · simp only [hxr, if_false]
          exact st.reg x hx
      · intro x hx
        show readXmm ms x = s2.fpRegs x
        rw [hs2fp x]
        exact st.fp x hx
    exact finish hq hstepSafe


end Flapjack.Compiler.Encoders.X64
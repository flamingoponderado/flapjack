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

/-- `asm_ok` of an immediate `binop` splits into its register check and the
immediate-range check. -/
theorem binopRI_ok (op : BinOp) (r : Nat) (i : BitVec 64)
    (h : asmOkExact (.inst (.arith (.binop op r r (.imm i)))) x64Config = true) :
    asmRegOkExact r x64Config = true ∧
      ((((Sum.inl op : Sum BinOp Cmp) == (Sum.inl BinOp.xor : Sum BinOp Cmp)) = true ∧ i = -1) ∨
        (x64Min32.toInt ≤ i.toInt ∧ i.toInt ≤ x64Max32.toInt)) := by
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, asmRegImmOkExact, x64Config,
    Bool.and_eq_true, Bool.or_eq_true, Bool.not_true, Bool.false_or] at h
  simp at h
  exact h

/-- The `binop` value computed by the closed model is the source semantics'
`binop_upd` value. -/
theorem binopValue_x64Bop (op : BinOp) (a b : BitVec 64) :
    binopValue (x64Bop op) a b =
      (match op with
       | .add => a + b | .sub => a - b | .and => a &&& b | .or => a ||| b
       | .xor => a ^^^ b) := by
  cases op <;> rfl

/-- The `binop` value written by `binop_upd`. -/
theorem binopUpd_value (r : Nat) (op : BinOp) (a b : BitVec 64) (s : AsmState 64) :
    binopUpd r op a b s =
      updReg r (match op with
        | .add => a + b | .sub => a - b | .and => a &&& b | .or => a ||| b
        | .xor => a ^^^ b) s := by
  cases op <;> rfl

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

/-- One `x64Next` step over a register-register arithmetic instruction writes
the operation's value and sets the flags. -/
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

end Flapjack.Compiler.Encoders.X64

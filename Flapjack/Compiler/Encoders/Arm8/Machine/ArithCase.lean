/-
Copyright (c) 2025 Flapjack contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Flapjack.Compiler.Encoders.Arm8.Machine.ConstCase

/-!
# The ARM8 arithmetic encoder-correctness cases

This file proves the `arith` cases of `encoder_correct arm8Target`, the ARM8
analogue of `case_binop_reg`, `case_binop_imm`, `case_shift_imm` and `case_div`
in `Flapjack/Mips32/TargetProof/Arith.lean`.

Every `arith` form in the restricted `arm8Ast` (`Machine/Target.lean`) lowers to
exactly one instruction (or to `noOp` for an unavailable operation), so each case
is a one-step `arm8Next` run (`n = 0`) through `encoderCaseStep`.  Each proof
reads the encoder's side conditions off `arm8Start.asmOk`, identifies the emitted
instruction from `arm8Start.bytes`, executes it with the matching `arm8Next_*`
decoder lemma, and compares the destination register with the value `arithUpd`
writes.

The statement-level shape follows the MIPS file, but the ARM8 form is wrapped:
`HolAsm.inst (.arith ...)`, and the machine step is the closed `arm8Next` of
`Machine/Execute.lean` rather than the L3 `arm8_step`.

## The `Shift ... (Reg r)` case

`arm8Ast` lowers `Shift sop destination source (Reg right)` to the single
instruction `Shift (arm8Shv sop) right source destination`, whose operand order
is `(shift, right, source, destination)`.  In the ARMv8 encoding the second
operand is the register in the `Rm` field (the shift *amount*) and the third is
in the `Rn` field (the shifted *value*).  The closed `execInsn` of
`Machine/Execute.lean`, however, computes
`shiftValue (readReg s rm) shift (readReg s rn).toNat`: it reads the shifted
value from `rm` and the amount from `rn`, i.e. the two registers are swapped
relative to the encoder and the L3 model
(`dfn'Shift`: value `X[n]`, amount `X[m]`).  The encoded instruction therefore
computes `right <<< source` where `arithUpd` specifies `source <<< right`, so the
`Shift ... (Reg r)` case is false against this model and is not stated here.  It
cannot be repaired without changing `Machine/Execute.lean`, which is outside this
file.

As in the other `Machine/*Case.lean` files, this is a case split of the single
HOL theorem `arm8_encoder_correct`
(`cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml`), whose
`Inst`/`Arith` branch has no per-case declaration of its own; the module is
Flapjack infrastructure and carries no `@[hol]` tags.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-! ## Word arithmetic used by the instruction models -/

/-- `ofNat` of the sum of the `toNat`s is the word sum. -/
theorem arith_ofNat64_add_toNat (x y : BitVec 64) :
    BitVec.ofNat 64 (x.toNat + y.toNat) = x + y := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_add]

/-- The result half of `addWithCarry` without carry. -/
theorem arith_addWithCarry_false (x y : BitVec 64) :
    (addWithCarry x y false).1 = x + y := by
  unfold addWithCarry
  simp only [Bool.false_eq_true, if_false, Nat.add_zero]
  exact arith_ofNat64_add_toNat x y

/-- `ofNat` of a sum with one extra low bit is the word sum with one. -/
theorem arith_ofNat64_add_one (x y : BitVec 64) :
    BitVec.ofNat 64 (x.toNat + y.toNat + 1) = x + y + 1 := by
  rw [show x.toNat + y.toNat + 1 = (x.toNat + y.toNat) + 1 by omega]
  rw [BitVec.ofNat_add, arith_ofNat64_add_toNat]
  rfl

/-- The result half of `addWithCarry` with carry in. -/
theorem arith_addWithCarry_true (x y : BitVec 64) :
    (addWithCarry x y true).1 = x + y + 1 := by
  unfold addWithCarry
  simp only [if_true]
  exact arith_ofNat64_add_one x y

/-- The value `x + ~~~y + 1` is the difference `x - y`. -/
theorem arith_add_not_add_one (x y : BitVec 64) : x + ~~~y + 1 = x - y := by
  rw [BitVec.add_assoc]
  have h1 : (1 : BitVec 64) = 1#64 := rfl
  rw [h1, ← BitVec.neg_eq_not_add, BitVec.sub_eq_add_neg]

/-- The all-ones word is the word `-1`. -/
theorem arith_allOnes : (BitVec.allOnes 64 : BitVec 64) = -1 := by decide

/-! ## Executing the lowered instructions -/

/-- Executing the subtracting, flag-preserving `addSubShiftedRegister`: the
result is the difference of the two register values. -/
theorem execInsn_addSubShiftedRegister_sub_lsl0 (s : Arm8State) (rm rn rd : Nat) :
    execInsn s (.addSubShiftedRegister true false .lsl rm 0 rn rd) =
      writeReg s rd (readReg s rn - readReg s rm) := by
  simp only [execInsn, shiftValue, Nat.zero_mod, BitVec.shiftLeft_zero,
    Bool.false_eq_true, if_false, if_true]
  rw [arith_addWithCarry_true, arith_add_not_add_one]

/-- Executing the flag-preserving `logicalShiftedRegister` with no shift and no
inversion. -/
theorem execInsn_logicalShiftedRegister_lsl0 (s : Arm8State) (op : LogicalOp)
    (rm rn rd : Nat) :
    execInsn s (.logicalShiftedRegister op false false .lsl 0 rm rn rd) =
      writeReg s rd (match op with
        | .and => readReg s rn &&& readReg s rm
        | .orr => readReg s rn ||| readReg s rm
        | .eor => readReg s rn ^^^ readReg s rm) := by
  simp only [execInsn, shiftValue, Nat.zero_mod, BitVec.shiftLeft_zero,
    Bool.false_eq_true, ↓reduceIte]
  cases op <;> rfl

/-- Executing the `Xor -1` lowering: an inverting `ORR` against the zero
register. -/
theorem execInsn_logicalShiftedRegister_invert_zero (s : Arm8State) (rm rd : Nat) :
    execInsn s (.logicalShiftedRegister .orr true false .lsl 0 rm 31 rd) =
      writeReg s rd (~~~(readReg s rm)) := by
  have h31 : readReg s 31 = 0 := rfl
  simp only [execInsn, shiftValue, Nat.zero_mod, BitVec.shiftLeft_zero,
    Bool.false_eq_true, ↓reduceIte, h31]
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  rw [h0, BitVec.zero_or]

/-- Executing a flag-preserving `logicalImmediate`. -/
theorem execInsn_logicalImmediate (s : Arm8State) (op : LogicalOp) (w : BitVec 64)
    (rn rd : Nat) :
    execInsn s (.logicalImmediate op false w rn rd) =
      writeReg s rd (match op with
        | .and => readReg s rn &&& w
        | .orr => readReg s rn ||| w
        | .eor => readReg s rn ^^^ w) := by
  simp only [execInsn, Bool.false_eq_true, ↓reduceIte]
  cases op <;> rfl

/-- Executing an unshifted, flag-preserving `addSubImmediate` addition. -/
theorem execInsn_addSubImmediate_add (s : Arm8State) (w : BitVec 64) (rn rd : Nat) :
    execInsn s (.addSubImmediate false false w rn rd) =
      writeReg s rd (readReg s rn + w) := by
  simp only [execInsn, Bool.false_eq_true, ↓reduceIte]
  rw [arith_addWithCarry_false]

/-- Executing an unshifted, flag-preserving `addSubImmediate` subtraction. -/
theorem execInsn_addSubImmediate_sub (s : Arm8State) (w : BitVec 64) (rn rd : Nat) :
    execInsn s (.addSubImmediate true false w rn rd) =
      writeReg s rd (readReg s rn - w) := by
  simp only [execInsn, Bool.false_eq_true, ↓reduceIte]
  rw [arith_addWithCarry_true, arith_add_not_add_one]

/-- Executing a division writes the signed quotient of the two register
values. -/
theorem execInsn_division_signed (s : Arm8State) (rm rn rd : Nat) :
    execInsn s (.division false rm rn rd) =
      writeReg s rd ((readReg s rn).sdiv (readReg s rm)) := by
  simp only [execInsn, Bool.false_eq_true, ↓reduceIte]

/-- The fields `execInsn` leaves when it is a `writeReg` of the destination. -/
theorem execWriteFields {ms t : Arm8State} {r : Nat} {v : BitVec 64} (hne31 : r ≠ 31)
    (h : t = writeReg { ms with pc := ms.pc + 4 } r v) :
    t.pc = ms.pc + 4 ∧ (∀ x, t.mem x = ms.mem x) ∧
      (∀ j, j ≠ r → t.regs j = ms.regs j) ∧ t.failed = ms.failed ∧ t.regs r = v := by
  subst h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [writeReg, if_neg hne31]
  · intro x; simp only [writeReg, if_neg hne31]
  · intro j hj; simp only [writeReg, if_neg hne31, if_neg hj]
  · simp only [writeReg, if_neg hne31]
  · simp only [writeReg, if_neg hne31]
    exact if_pos trivial

/-! ## Reading registers out of the start relation -/

/-- A register of the initial target state agrees with the source state. -/
theorem msReadReg (st : Arm8Start i s1 s2 ms) {r : Nat}
    (hlt : r < arm8Config.regCount) (hav : arm8Config.avoidRegs.contains r = false)
    (hne : r ≠ 31) : readReg ms r = s1.regs r := by
  simp only [readReg, hne, if_false]
  exact st.reg r (by rw [arm8Target_config]; exact ⟨hlt, hav⟩)

/-- The same, in the PC-advanced state `execInsn` runs on. -/
theorem msReadReg_pc (st : Arm8Start i s1 s2 ms) {r : Nat}
    (hlt : r < arm8Config.regCount) (hav : arm8Config.avoidRegs.contains r = false)
    (hne : r ≠ 31) : readReg { ms with pc := ms.pc + 4 } r = s1.regs r := by
  simpa only [readReg, hne, if_false] using msReadReg st hlt hav hne

/-! ## The side conditions of an `arith` instruction -/

/-- The three register side conditions of a `div`. -/
theorem arithRegOkDiv (r t u : Nat) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.div r t u))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    (asmRegOkExact r arm8Config = true ∧ asmRegOkExact t arm8Config = true) ∧
      asmRegOkExact u arm8Config = true := by
  have st := arm8Start _ s1 s2 ms h
  have hb := st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, arm8Config] at hb
  simp only [Bool.and_eq_true] at hb
  exact hb.1

/-- The three register side conditions of a register-operand `binop`. -/
theorem arithRegOkBinopReg (bop : BinOp) (r t u : Nat) (s1 s2 : AsmState 64)
    (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.binop bop r t (.reg u)))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    (asmRegOkExact r arm8Config = true ∧ asmRegOkExact t arm8Config = true) ∧
      asmRegOkExact u arm8Config = true := by
  have st := arm8Start _ s1 s2 ms h
  have hb := st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, arm8Config,
    asmRegImmOkExact, Bool.not_false, Bool.true_or, Bool.true_and,
    Bool.and_eq_true] at hb
  exact hb

/-- The register and immediate side conditions of an immediate `binop`. -/
theorem arithRegOkBinopImm (bop : BinOp) (r t : Nat) (w : BitVec 64)
    (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.binop bop r t (.imm w)))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    (asmRegOkExact r arm8Config = true ∧ asmRegOkExact t arm8Config = true) ∧
      asmRegImmOkExact (.inl bop) (.imm w) arm8Config = true := by
  have st := arm8Start _ s1 s2 ms h
  have hb := st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, arm8Config,
    Bool.not_false, Bool.true_or, Bool.true_and, Bool.and_eq_true] at hb
  exact hb

/-- The immediate side condition of an addition or subtraction says that the
immediate is a twelve-bit constant, possibly shifted left by twelve. -/
theorem validImmediate_addSub {bop : BinOp} (hbop : bop = .add ∨ bop = .sub)
    {w : BitVec 64} (h : asmRegImmOkExact (.inl bop) (.imm w) arm8Config = true) :
    w &&& ~~~(0xFFF : BitVec 64) = 0 ∨ w &&& ~~~(0xFFF000 : BitVec 64) = 0 := by
  rcases hbop with rfl | rfl
  · have hxor : ((Sum.inl .add == (Sum.inl .xor : Sum BinOp Cmp)) && (w == -1)) = false :=
      rfl
    simp only [asmRegImmOkExact, arm8Config, hxor, Bool.false_or, validImmediate,
      Bool.or_eq_true, decide_eq_true_eq] at h
    exact h
  · have hxor : ((Sum.inl .sub == (Sum.inl .xor : Sum BinOp Cmp)) && (w == -1)) = false :=
      rfl
    simp only [asmRegImmOkExact, arm8Config, hxor, Bool.false_or, validImmediate,
      Bool.or_eq_true, decide_eq_true_eq] at h
    exact h

/-- The immediate side condition of a bitmask `and`/`or` says that the immediate
has a bitmask encoding. -/
theorem isSome_of_asmRegImm {bop : BinOp} (hbop : bop = .and ∨ bop = .or)
    {w : BitVec 64} (h : asmRegImmOkExact (.inl bop) (.imm w) arm8Config = true) :
    (encodeBitMask w).isSome = true := by
  rcases hbop with rfl | rfl
  · have hxor : ((Sum.inl .and == (Sum.inl .xor : Sum BinOp Cmp)) && (w == -1)) = false :=
      rfl
    simp only [asmRegImmOkExact, arm8Config, hxor, Bool.false_or, validImmediate] at h
    exact h
  · have hxor : ((Sum.inl .or == (Sum.inl .xor : Sum BinOp Cmp)) && (w == -1)) = false :=
      rfl
    simp only [asmRegImmOkExact, arm8Config, hxor, Bool.false_or, validImmediate] at h
    exact h

/-! ## The registers `arithUpd` writes -/

/-- The register update of a register-operand `binop`. -/
theorem arithUpd_binop_reg_regs (s : AsmState 64) (bop : BinOp) (r t u : Nat) :
    ∀ j, (arithUpd (.binop bop r t (.reg u)) s).regs j =
      (if j = r then (match bop with
        | .add => s.regs t + s.regs u
        | .sub => s.regs t - s.regs u
        | .and => s.regs t &&& s.regs u
        | .or => s.regs t ||| s.regs u
        | .xor => s.regs t ^^^ s.regs u) else s.regs j) := by
  intro j
  cases bop <;> rfl

/-- The register update of an immediate `binop`. -/
theorem arithUpd_binop_imm_regs (s : AsmState 64) (bop : BinOp) (r t : Nat)
    (w : BitVec 64) :
    ∀ j, (arithUpd (.binop bop r t (.imm w)) s).regs j =
      (if j = r then (match bop with
        | .add => s.regs t + w
        | .sub => s.regs t - w
        | .and => s.regs t &&& w
        | .or => s.regs t ||| w
        | .xor => s.regs t ^^^ w) else s.regs j) := by
  intro j
  cases bop <;> rfl

/-- The register update of a `div`.

`assertState` only touches the failure flag, and the ARM8 source semantics reads
the divisor without the `31`-is-zero convention, so no register case is needed. -/
theorem arithUpd_div_regs (s : AsmState 64) (r t u : Nat) :
    ∀ j, (arithUpd (.div r t u) s).regs j =
      (if j = r then (s.regs t).sdiv (s.regs u) else s.regs j) := by
  intro j
  simp only [arithUpd, assertState, updReg]
  rfl

/-- `arithUpd` never changes the program counter. -/
theorem arithUpd_pc (op : HolArith 64) (s : AsmState 64) : (arithUpd op s).pc = s.pc := by
  cases op <;> rfl

/-- `arithUpd` never changes memory. -/
theorem arithUpd_mem (op : HolArith 64) (s : AsmState 64) :
    ∀ x, (arithUpd op s).mem x = s.mem x := by
  intro x
  cases op <;> rfl

/-- `arithUpd` never changes the memory domain. -/
theorem arithUpd_dom (op : HolArith 64) (s : AsmState 64) :
    (arithUpd op s).memDomain = s.memDomain := by
  cases op <;> rfl

/-- An `arith` instruction only advances the program counter. -/
theorem asmUpd_arith_pc (op : HolArith 64) (pc : BitVec 64) (s : AsmState 64) :
    (asmUpd (.inst (.arith op)) pc s).pc = pc := rfl

/-- An `arith` instruction leaves memory alone. -/
theorem asmUpd_arith_mem (op : HolArith 64) (pc : BitVec 64) (s : AsmState 64) :
    ∀ x, (asmUpd (.inst (.arith op)) pc s).mem x = s.mem x := by
  intro x
  exact arithUpd_mem op s x

/-- An `arith` instruction leaves the memory domain alone. -/
theorem asmUpd_arith_dom (op : HolArith 64) (pc : BitVec 64) (s : AsmState 64) :
    (asmUpd (.inst (.arith op)) pc s).memDomain = s.memDomain :=
  arithUpd_dom op s

/-- A one-instruction lowering advances the source by four bytes. -/
theorem arithUpd_of_start (i : HolAsm 64) {insn : Insn} (s1 s2 : AsmState 64)
    (ms : Arm8State)
    (h : asmStep arm8Config s1 i s2 ∧ targetStateRel arm8Target s1 ms)
    (hast : arm8Ast i = [insn]) :
    asmUpd i (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
  have st := arm8Start i s1 s2 ms h
  have hlen : (arm8Enc i).length = 4 := by
    rw [arm8Enc, hast, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      encodeBytes_length]
  rw [← st.upd, hlen]

/-- The four state facts of an `arith` step, from its `asmUpd` and the register
the update writes. -/
theorem arithUpdFacts (op : HolArith 64) (s1 s2 : AsmState 64) (r : Nat)
    (v : BitVec 64)
    (hupd : asmUpd (.inst (.arith op)) (s1.pc + BitVec.ofNat 64 4) s1 = s2)
    (hregs : ∀ j, (arithUpd op s1).regs j = (if j = r then v else s1.regs j)) :
    s2.pc = s1.pc + 4 ∧ (∀ x, s2.mem x = s1.mem x) ∧
      s2.memDomain = s1.memDomain ∧
      ∀ j, s2.regs j = (if j = r then v else s1.regs j) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hupd]
    exact asmUpd_arith_pc op _ s1
  · intro x
    rw [← hupd]
    exact asmUpd_arith_mem op _ s1 x
  · rw [← hupd]
    exact asmUpd_arith_dom op _ s1
  · intro j
    rw [← hupd]
    exact hregs j

/-! ## A generic single-instruction `arith` run -/

/-- One `arith` case whose lowering is a single instruction writing the
destination register: assemble the `encoderCaseStep` run from the instruction's
decoder, the state it produces, and the register value both sides agree on. -/
theorem arithOneCase (i : HolAsm 64) (r : Nat) (v : BitVec 64) (t : Arm8State)
    (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 i s2 ∧ targetStateRel arm8Target s1 ms)
    (hnext : arm8Next ms = t)
    (hfields : t.pc = ms.pc + 4 ∧ (∀ x, t.mem x = ms.mem x) ∧
      (∀ j, j ≠ r → t.regs j = ms.regs j) ∧ t.failed = ms.failed ∧ t.regs r = v)
    (hs2pc : s2.pc = s1.pc + 4)
    (hs2mem : ∀ x, s2.mem x = s1.mem x)
    (hs2dom : s2.memDomain = s1.memDomain)
    (hs2regs : ∀ j, s2.regs j = (if j = r then v else s1.regs j))
    (hsafe0 : StepSafe s1.memDomain ms) :
    CaseGoal i s1 s2 ms := by
  obtain ⟨htpc, htmem, htreg, htfailed, htval⟩ := hfields
  have st := arm8Start i s1 s2 ms h
  have hcode : allPcs (arm8Target.config.encode i).length s1.pc 0 ⊆
      s1.memDomain := by
    rw [arm8Target_config, arm8Config_encode, ← st.pc]
    exact bytesInMemory_allPcs _ _ _ _ 0 st.bytes
  have hq1 : arm8Target.stateOk t = true :=
    arm8StateOk_set t (by
      rw [htpc, (alignedAddSub 2 ms.pc 4 holAligned_four).1, st.aligned])
      (htfailed.trans st.msFailed)
  have hq2 : t.pc = s2.pc := by
    rw [htpc, st.pc, hs2pc]
  have hq3 : ∀ x, s2.memDomain x → t.mem x = s2.mem x := by
    intro x hx
    rw [htmem x, hs2mem x]
    exact st.mem x (hs2dom ▸ hx)
  have hq4 : ∀ j, j < arm8Target.config.regCount ∧
      arm8Target.config.avoidRegs.contains j = false → t.regs j = s2.regs j := by
    intro j hj
    by_cases hjr : j = r
    · rw [hjr, htval, hs2regs r, if_pos rfl]
    · rw [htreg j hjr, hs2regs j, if_neg hjr]
      exact st.reg j hj
  have hq5 : ∀ j, j < arm8Target.config.fpRegCount →
      arm8Target.getFpReg t j = s2.fpRegs j := by
    intro j hj
    simp only [arm8Target_config, arm8Config] at hj
    omega
  have hq : targetStateRel arm8Target s2 (arm8Next^[0 + 1] ms) := by
    rw [show arm8Next^[0 + 1] ms = t by
      rw [Nat.zero_add, Function.iterate_one, hnext]]
    exact ⟨hq1, hq2, hq3, hq4, hq5⟩
  refine encoderCaseStep i s1 s2 ms 0 hs2dom hcode ?_ ?_ hq
  · intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simpa using hsafe0
  · intro k h1 h2
    omega

/-- The scaffolding of a register-operand `binop` case: the lowering is one
instruction writing the destination register with a known value, and `arithUpd`
writes the same value. -/
theorem arithBinopRegCase (bop : BinOp) (r t u : Nat) (v : BitVec 64)
    (t' : Arm8State) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.binop bop r t (.reg u)))) s2 ∧
      targetStateRel arm8Target s1 ms)
    (hnext : arm8Next ms = t')
    (hwrite : t' = writeReg { ms with pc := ms.pc + 4 } r v)
    (hne31 : r ≠ 31)
    (hs2pc : s2.pc = s1.pc + 4)
    (hs2mem : ∀ x, s2.mem x = s1.mem x)
    (hs2dom : s2.memDomain = s1.memDomain)
    (hs2regs : ∀ j, s2.regs j = (if j = r then v else s1.regs j))
    (hsafe0 : StepSafe s1.memDomain ms) :
    CaseGoal (.inst (.arith (.binop bop r t (.reg u)))) s1 s2 ms := by
  have hfields := execWriteFields hne31 hwrite
  exact arithOneCase _ r v t' s1 s2 ms h hnext hfields hs2pc hs2mem hs2dom hs2regs hsafe0

/-- The scaffolding of an immediate `binop` case. -/
theorem arithBinopImmCase (bop : BinOp) (r t : Nat) (w : BitVec 64)
    (v : BitVec 64) (t' : Arm8State) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.binop bop r t (.imm w)))) s2 ∧
      targetStateRel arm8Target s1 ms)
    (hnext : arm8Next ms = t')
    (hwrite : t' = writeReg { ms with pc := ms.pc + 4 } r v)
    (hne31 : r ≠ 31)
    (hs2pc : s2.pc = s1.pc + 4)
    (hs2mem : ∀ x, s2.mem x = s1.mem x)
    (hs2dom : s2.memDomain = s1.memDomain)
    (hs2regs : ∀ j, s2.regs j = (if j = r then v else s1.regs j))
    (hsafe0 : StepSafe s1.memDomain ms) :
    CaseGoal (.inst (.arith (.binop bop r t (.imm w)))) s1 s2 ms := by
  have hfields := execWriteFields hne31 hwrite
  exact arithOneCase _ r v t' s1 s2 ms h hnext hfields hs2pc hs2mem hs2dom hs2regs hsafe0

/-! ## `binop` with a register operand -/

/-- The register-operand `binop` cases: addition and subtraction become one
`addSubShiftedRegister` with a zero shift, `and`/`or`/`xor` one
`logicalShiftedRegister`. -/
theorem case_binop_reg (bop : BinOp) (r t u : Nat) (s1 s2 : AsmState 64)
    (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.binop bop r t (.reg u)))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.arith (.binop bop r t (.reg u)))) s1 s2 ms := by
  cases bop
  case add =>
    have hok := arithRegOkBinopReg .add r t u s1 s2 ms h
    obtain ⟨⟨hokr, hokt⟩, hoku⟩ := hok
    obtain ⟨hltr, havr, hne31⟩ := regOk_of_asm hokr
    obtain ⟨hltt, havt, hnet31⟩ := regOk_of_asm hokt
    obtain ⟨hltu, havu, hneu31⟩ := regOk_of_asm hoku
    have hltr32 : r < 32 := by simpa [arm8Config] using hltr
    have hltt32 : t < 32 := by simpa [arm8Config] using hltt
    have hltu32 : u < 32 := by simpa [arm8Config] using hltu
    have st := arm8Start _ s1 s2 ms h
    have hast : arm8Ast (.inst (.arith (.binop .add r t (.reg u)))) =
        [.addSubShiftedRegister false false .lsl u 0 t r] := rfl
    have hb : bytesInMemoryHOL ms.pc
        (encodeBytes (.addSubShiftedRegister false false .lsl u 0 t r)) ms.mem
        s1.memDomain := by
      have hb' := st.bytes
      rw [arm8Enc, hast] at hb'
      simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
    have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
        (.addSubShiftedRegister false false .lsl u 0 t r) :=
      arm8Next_addSubShiftedRegister ms s1.memDomain false false .lsl u 0 t r hltu32
        (by decide) hltt32 hltr32 hb
    have hsrc := msReadReg_pc st hltt havt hnet31
    have harg := msReadReg_pc st hltu havu hneu31
    have hwrite : execInsn { ms with pc := ms.pc + 4 }
        (.addSubShiftedRegister false false .lsl u 0 t r) =
        writeReg { ms with pc := ms.pc + 4 } r (s1.regs t + s1.regs u) := by
      simp only [execInsn_addSubShiftedRegister_lsl0, hsrc, harg]
    have hsafe0 : StepSafe s1.memDomain ms :=
      stepSafe_of_encode ms s1.memDomain
        (.addSubShiftedRegister false false .lsl u 0 t r) _ hb
        (encodeInsn_addSubShiftedRegister false false .lsl u 0 t r)
        (decode_encode_addSubShiftedRegisterInsn false false .lsl u 0 t r hltu32
          (by decide) hltt32 hltr32) (by rfl)
    have hupd := arithUpd_of_start (.inst (.arith (.binop .add r t (.reg u)))) s1 s2 ms h hast
    have hregs := arithUpd_binop_reg_regs s1 .add r t u
    obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
      arithUpdFacts _ s1 s2 r (s1.regs t + s1.regs u) hupd hregs
    exact arithBinopRegCase .add r t u (s1.regs t + s1.regs u) _ s1 s2 ms h hnext hwrite hne31
      hs2pc hs2mem hs2dom hs2regs hsafe0
  case sub =>
    have hok := arithRegOkBinopReg .sub r t u s1 s2 ms h
    obtain ⟨⟨hokr, hokt⟩, hoku⟩ := hok
    obtain ⟨hltr, havr, hne31⟩ := regOk_of_asm hokr
    obtain ⟨hltt, havt, hnet31⟩ := regOk_of_asm hokt
    obtain ⟨hltu, havu, hneu31⟩ := regOk_of_asm hoku
    have hltr32 : r < 32 := by simpa [arm8Config] using hltr
    have hltt32 : t < 32 := by simpa [arm8Config] using hltt
    have hltu32 : u < 32 := by simpa [arm8Config] using hltu
    have st := arm8Start _ s1 s2 ms h
    have hast : arm8Ast (.inst (.arith (.binop .sub r t (.reg u)))) =
        [.addSubShiftedRegister true false .lsl u 0 t r] := rfl
    have hb : bytesInMemoryHOL ms.pc
        (encodeBytes (.addSubShiftedRegister true false .lsl u 0 t r)) ms.mem
        s1.memDomain := by
      have hb' := st.bytes
      rw [arm8Enc, hast] at hb'
      simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
    have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
        (.addSubShiftedRegister true false .lsl u 0 t r) :=
      arm8Next_addSubShiftedRegister ms s1.memDomain true false .lsl u 0 t r hltu32
        (by decide) hltt32 hltr32 hb
    have hsrc := msReadReg_pc st hltt havt hnet31
    have harg := msReadReg_pc st hltu havu hneu31
    have hwrite : execInsn { ms with pc := ms.pc + 4 }
        (.addSubShiftedRegister true false .lsl u 0 t r) =
        writeReg { ms with pc := ms.pc + 4 } r (s1.regs t - s1.regs u) := by
      simp only [execInsn_addSubShiftedRegister_sub_lsl0, hsrc, harg]
    have hsafe0 : StepSafe s1.memDomain ms :=
      stepSafe_of_encode ms s1.memDomain
        (.addSubShiftedRegister true false .lsl u 0 t r) _ hb
        (encodeInsn_addSubShiftedRegister true false .lsl u 0 t r)
        (decode_encode_addSubShiftedRegisterInsn true false .lsl u 0 t r hltu32
          (by decide) hltt32 hltr32) (by rfl)
    have hupd := arithUpd_of_start (.inst (.arith (.binop .sub r t (.reg u)))) s1 s2 ms h hast
    have hregs := arithUpd_binop_reg_regs s1 .sub r t u
    obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
      arithUpdFacts _ s1 s2 r (s1.regs t - s1.regs u) hupd hregs
    exact arithBinopRegCase .sub r t u (s1.regs t - s1.regs u) _ s1 s2 ms h hnext hwrite hne31
      hs2pc hs2mem hs2dom hs2regs hsafe0
  case and =>
    have hok := arithRegOkBinopReg .and r t u s1 s2 ms h
    obtain ⟨⟨hokr, hokt⟩, hoku⟩ := hok
    obtain ⟨hltr, havr, hne31⟩ := regOk_of_asm hokr
    obtain ⟨hltt, havt, hnet31⟩ := regOk_of_asm hokt
    obtain ⟨hltu, havu, hneu31⟩ := regOk_of_asm hoku
    have hltr32 : r < 32 := by simpa [arm8Config] using hltr
    have hltt32 : t < 32 := by simpa [arm8Config] using hltt
    have hltu32 : u < 32 := by simpa [arm8Config] using hltu
    have st := arm8Start _ s1 s2 ms h
    have hast : arm8Ast (.inst (.arith (.binop .and r t (.reg u)))) =
        [.logicalShiftedRegister .and false false .lsl 0 u t r] := rfl
    have hb : bytesInMemoryHOL ms.pc
        (encodeBytes (.logicalShiftedRegister .and false false .lsl 0 u t r)) ms.mem
        s1.memDomain := by
      have hb' := st.bytes
      rw [arm8Enc, hast] at hb'
      simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
    have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
        (.logicalShiftedRegister .and false false .lsl 0 u t r) :=
      arm8Next_logicalShiftedRegister ms s1.memDomain .and false false .lsl 0 u t r 0
        (by decide) (by decide) hltu32 hltt32 hltr32 hb
    have hsrc := msReadReg_pc st hltt havt hnet31
    have harg := msReadReg_pc st hltu havu hneu31
    have hwrite : execInsn { ms with pc := ms.pc + 4 }
        (.logicalShiftedRegister .and false false .lsl 0 u t r) =
        writeReg { ms with pc := ms.pc + 4 } r (s1.regs t &&& s1.regs u) := by
      simp only [execInsn_logicalShiftedRegister_lsl0, hsrc, harg]
    have hsafe0 : StepSafe s1.memDomain ms :=
      stepSafe_of_encode ms s1.memDomain
        (.logicalShiftedRegister .and false false .lsl 0 u t r) _ hb
        (encodeInsn_logicalShiftedRegister .and false false .lsl 0 u t r 0 (by decide) (by decide))
        (decode_encode_logicalShiftedRegister .and false false .lsl 0 u t r 0
          (by decide) (by decide) hltu32 hltt32 hltr32) (by rfl)
    have hupd := arithUpd_of_start (.inst (.arith (.binop .and r t (.reg u)))) s1 s2 ms h hast
    have hregs := arithUpd_binop_reg_regs s1 .and r t u
    obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
      arithUpdFacts _ s1 s2 r (s1.regs t &&& s1.regs u) hupd hregs
    exact arithBinopRegCase .and r t u (s1.regs t &&& s1.regs u) _ s1 s2 ms h hnext hwrite hne31
      hs2pc hs2mem hs2dom hs2regs hsafe0
  case or =>
    have hok := arithRegOkBinopReg .or r t u s1 s2 ms h
    obtain ⟨⟨hokr, hokt⟩, hoku⟩ := hok
    obtain ⟨hltr, havr, hne31⟩ := regOk_of_asm hokr
    obtain ⟨hltt, havt, hnet31⟩ := regOk_of_asm hokt
    obtain ⟨hltu, havu, hneu31⟩ := regOk_of_asm hoku
    have hltr32 : r < 32 := by simpa [arm8Config] using hltr
    have hltt32 : t < 32 := by simpa [arm8Config] using hltt
    have hltu32 : u < 32 := by simpa [arm8Config] using hltu
    have st := arm8Start _ s1 s2 ms h
    have hast : arm8Ast (.inst (.arith (.binop .or r t (.reg u)))) =
        [.logicalShiftedRegister .orr false false .lsl 0 u t r] := rfl
    have hb : bytesInMemoryHOL ms.pc
        (encodeBytes (.logicalShiftedRegister .orr false false .lsl 0 u t r)) ms.mem
        s1.memDomain := by
      have hb' := st.bytes
      rw [arm8Enc, hast] at hb'
      simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
    have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
        (.logicalShiftedRegister .orr false false .lsl 0 u t r) :=
      arm8Next_logicalShiftedRegister ms s1.memDomain .orr false false .lsl 0 u t r 1
        (by decide) (by decide) hltu32 hltt32 hltr32 hb
    have hsrc := msReadReg_pc st hltt havt hnet31
    have harg := msReadReg_pc st hltu havu hneu31
    have hwrite : execInsn { ms with pc := ms.pc + 4 }
        (.logicalShiftedRegister .orr false false .lsl 0 u t r) =
        writeReg { ms with pc := ms.pc + 4 } r (s1.regs t ||| s1.regs u) := by
      simp only [execInsn_logicalShiftedRegister_lsl0, hsrc, harg]
    have hsafe0 : StepSafe s1.memDomain ms :=
      stepSafe_of_encode ms s1.memDomain
        (.logicalShiftedRegister .orr false false .lsl 0 u t r) _ hb
        (encodeInsn_logicalShiftedRegister .orr false false .lsl 0 u t r 1 (by decide) (by decide))
        (decode_encode_logicalShiftedRegister .orr false false .lsl 0 u t r 1
          (by decide) (by decide) hltu32 hltt32 hltr32) (by rfl)
    have hupd := arithUpd_of_start (.inst (.arith (.binop .or r t (.reg u)))) s1 s2 ms h hast
    have hregs := arithUpd_binop_reg_regs s1 .or r t u
    obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
      arithUpdFacts _ s1 s2 r (s1.regs t ||| s1.regs u) hupd hregs
    exact arithBinopRegCase .or r t u (s1.regs t ||| s1.regs u) _ s1 s2 ms h hnext hwrite hne31
      hs2pc hs2mem hs2dom hs2regs hsafe0
  case xor =>
    have hok := arithRegOkBinopReg .xor r t u s1 s2 ms h
    obtain ⟨⟨hokr, hokt⟩, hoku⟩ := hok
    obtain ⟨hltr, havr, hne31⟩ := regOk_of_asm hokr
    obtain ⟨hltt, havt, hnet31⟩ := regOk_of_asm hokt
    obtain ⟨hltu, havu, hneu31⟩ := regOk_of_asm hoku
    have hltr32 : r < 32 := by simpa [arm8Config] using hltr
    have hltt32 : t < 32 := by simpa [arm8Config] using hltt
    have hltu32 : u < 32 := by simpa [arm8Config] using hltu
    have st := arm8Start _ s1 s2 ms h
    have hast : arm8Ast (.inst (.arith (.binop .xor r t (.reg u)))) =
        [.logicalShiftedRegister .eor false false .lsl 0 u t r] := rfl
    have hb : bytesInMemoryHOL ms.pc
        (encodeBytes (.logicalShiftedRegister .eor false false .lsl 0 u t r)) ms.mem
        s1.memDomain := by
      have hb' := st.bytes
      rw [arm8Enc, hast] at hb'
      simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
    have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
        (.logicalShiftedRegister .eor false false .lsl 0 u t r) :=
      arm8Next_logicalShiftedRegister ms s1.memDomain .eor false false .lsl 0 u t r 2
        (by decide) (by decide) hltu32 hltt32 hltr32 hb
    have hsrc := msReadReg_pc st hltt havt hnet31
    have harg := msReadReg_pc st hltu havu hneu31
    have hwrite : execInsn { ms with pc := ms.pc + 4 }
        (.logicalShiftedRegister .eor false false .lsl 0 u t r) =
        writeReg { ms with pc := ms.pc + 4 } r (s1.regs t ^^^ s1.regs u) := by
      simp only [execInsn_logicalShiftedRegister_lsl0, hsrc, harg]
    have hsafe0 : StepSafe s1.memDomain ms :=
      stepSafe_of_encode ms s1.memDomain
        (.logicalShiftedRegister .eor false false .lsl 0 u t r) _ hb
        (encodeInsn_logicalShiftedRegister .eor false false .lsl 0 u t r 2 (by decide) (by decide))
        (decode_encode_logicalShiftedRegister .eor false false .lsl 0 u t r 2
          (by decide) (by decide) hltu32 hltt32 hltr32) (by rfl)
    have hupd := arithUpd_of_start (.inst (.arith (.binop .xor r t (.reg u)))) s1 s2 ms h hast
    have hregs := arithUpd_binop_reg_regs s1 .xor r t u
    obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
      arithUpdFacts _ s1 s2 r (s1.regs t ^^^ s1.regs u) hupd hregs
    exact arithBinopRegCase .xor r t u (s1.regs t ^^^ s1.regs u) _ s1 s2 ms h hnext hwrite hne31
      hs2pc hs2mem hs2dom hs2regs hsafe0

/-! ## `binop` with an immediate operand -/

/-- The immediate `binop` cases: addition and subtraction become one
`addSubImmediate`, `and`/`or` and a non-`-1` `xor` one `logicalImmediate`, and
`xor -1` one inverting `logicalShiftedRegister`. -/
theorem case_binop_imm (bop : BinOp) (r t : Nat) (w : BitVec 64) (s1 s2 : AsmState 64)
    (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.binop bop r t (.imm w)))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.arith (.binop bop r t (.imm w)))) s1 s2 ms := by
  cases bop
  case add =>
    have hok := arithRegOkBinopImm .add r t w s1 s2 ms h
    obtain ⟨⟨hokr, hokt⟩, himm⟩ := hok
    obtain ⟨hltr, havr, hne31⟩ := regOk_of_asm hokr
    obtain ⟨hltt, havt, hnet31⟩ := regOk_of_asm hokt
    have hltr32 : r < 32 := by simpa [arm8Config] using hltr
    have hltt32 : t < 32 := by simpa [arm8Config] using hltt
    have st := arm8Start _ s1 s2 ms h
    have hast : arm8Ast (.inst (.arith (.binop .add r t (.imm w)))) =
        [.addSubImmediate false false w t r] := rfl
    have hb : bytesInMemoryHOL ms.pc (encodeBytes (.addSubImmediate false false w t r))
        ms.mem s1.memDomain := by
      have hb' := st.bytes
      rw [arm8Enc, hast] at hb'
      simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
    have hdisj := validImmediate_addSub (Or.inl rfl) himm
    have hsrc := msReadReg_pc st hltt havt hnet31
    by_cases hlow : w &&& ~~~(0xFFF : BitVec 64) = 0
    · have hwlt : w.toNat < 4096 := and_not_fff_eq_zero_toNat_lt hlow
      have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
          (.addSubImmediate false false w t r) :=
        arm8Next_addSubImmediate ms s1.memDomain false false w t r hwlt hltt32 hltr32 hb
      have hwrite : execInsn { ms with pc := ms.pc + 4 }
          (.addSubImmediate false false w t r) =
          writeReg { ms with pc := ms.pc + 4 } r (s1.regs t + w) := by
        simp only [execInsn_addSubImmediate_add, hsrc]
      have hsafe0 : StepSafe s1.memDomain ms :=
        stepSafe_of_encode ms s1.memDomain (.addSubImmediate false false w t r) _ hb
          (encodeInsn_addSubImmediate false false w t r hwlt)
          (decode_encode_addSubImmediate false false w t r hwlt hltt32 hltr32) (by rfl)
      have hupd := arithUpd_of_start (.inst (.arith (.binop .add r t (.imm w)))) s1 s2 ms h hast
      have hregs := arithUpd_binop_imm_regs s1 .add r t w
      obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
        arithUpdFacts _ s1 s2 r (s1.regs t + w) hupd hregs
      exact
        arithBinopImmCase .add r t w (s1.regs t + w) _ s1 s2 ms h hnext hwrite hne31
          hs2pc hs2mem hs2dom hs2regs hsafe0
    · have hhigh : w &&& ~~~(0xFFF000 : BitVec 64) = 0 := by
        rcases hdisj with hh | hh
        · exact absurd hh hlow
        · exact hh
      have hmod : w.toNat % 4096 = 0 := and_not_fff000_eq_zero_toNat_mod hhigh
      have hlt24 : w.toNat < 2 ^ 24 := and_not_fff000_eq_zero_toNat_lt hhigh
      have hweq : BitVec.ofNat 64 (((w >>> 12).toNat % 4096) <<< 12) = w :=
        jumpCmp_ofNat_shifted w hmod hlt24
      have hm : ((w >>> 12).toNat % 4096) < 4096 := Nat.mod_lt _ (by decide)
      have hm0 : ((w >>> 12).toNat % 4096) ≠ 0 := by
        intro h0
        apply hlow
        rw [← hweq, h0]
        simp
      have hb' : bytesInMemoryHOL ms.pc
          (encodeBytes (.addSubImmediate false false
            (BitVec.ofNat 64 (((w >>> 12).toNat % 4096) <<< 12)) t r))
          ms.mem s1.memDomain := by
        rw [hweq]
        exact hb
      have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
          (.addSubImmediate false false w t r) := by
        have h' := arm8Next_addSubImmediateShifted ms s1.memDomain false false
          ((w >>> 12).toNat % 4096) t r hm hm0 hltt32 hltr32 hb'
        rw [hweq] at h'
        exact h'
      have hwrite : execInsn { ms with pc := ms.pc + 4 }
          (.addSubImmediate false false w t r) =
          writeReg { ms with pc := ms.pc + 4 } r (s1.regs t + w) := by
        simp only [execInsn_addSubImmediate_add, hsrc]
      have hsafe0 : StepSafe s1.memDomain ms :=
        stepSafe_of_encode ms s1.memDomain
          (.addSubImmediate false false (BitVec.ofNat 64 (((w >>> 12).toNat % 4096) <<< 12))
            t r) _ hb'
          (encodeInsn_addSubImmediateShifted false false _ t r hm hm0)
          (decode_encode_addSubImmediateShifted false false _ t r hm hltt32 hltr32)
          (by rfl)
      have hupd := arithUpd_of_start (.inst (.arith (.binop .add r t (.imm w)))) s1 s2 ms h hast
      have hregs := arithUpd_binop_imm_regs s1 .add r t w
      obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
        arithUpdFacts _ s1 s2 r (s1.regs t + w) hupd hregs
      exact
        arithBinopImmCase .add r t w (s1.regs t + w) _ s1 s2 ms h hnext hwrite hne31
          hs2pc hs2mem hs2dom hs2regs hsafe0
  case sub =>
    have hok := arithRegOkBinopImm .sub r t w s1 s2 ms h
    obtain ⟨⟨hokr, hokt⟩, himm⟩ := hok
    obtain ⟨hltr, havr, hne31⟩ := regOk_of_asm hokr
    obtain ⟨hltt, havt, hnet31⟩ := regOk_of_asm hokt
    have hltr32 : r < 32 := by simpa [arm8Config] using hltr
    have hltt32 : t < 32 := by simpa [arm8Config] using hltt
    have st := arm8Start _ s1 s2 ms h
    have hast : arm8Ast (.inst (.arith (.binop .sub r t (.imm w)))) =
        [.addSubImmediate true false w t r] := rfl
    have hb : bytesInMemoryHOL ms.pc (encodeBytes (.addSubImmediate true false w t r))
        ms.mem s1.memDomain := by
      have hb' := st.bytes
      rw [arm8Enc, hast] at hb'
      simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
    have hdisj := validImmediate_addSub (Or.inr rfl) himm
    have hsrc := msReadReg_pc st hltt havt hnet31
    by_cases hlow : w &&& ~~~(0xFFF : BitVec 64) = 0
    · have hwlt : w.toNat < 4096 := and_not_fff_eq_zero_toNat_lt hlow
      have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
          (.addSubImmediate true false w t r) :=
        arm8Next_addSubImmediate ms s1.memDomain true false w t r hwlt hltt32 hltr32 hb
      have hwrite : execInsn { ms with pc := ms.pc + 4 }
          (.addSubImmediate true false w t r) =
          writeReg { ms with pc := ms.pc + 4 } r (s1.regs t - w) := by
        simp only [execInsn_addSubImmediate_sub, hsrc]
      have hsafe0 : StepSafe s1.memDomain ms :=
        stepSafe_of_encode ms s1.memDomain (.addSubImmediate true false w t r) _ hb
          (encodeInsn_addSubImmediate true false w t r hwlt)
          (decode_encode_addSubImmediate true false w t r hwlt hltt32 hltr32) (by rfl)
      have hupd := arithUpd_of_start (.inst (.arith (.binop .sub r t (.imm w)))) s1 s2 ms h hast
      have hregs := arithUpd_binop_imm_regs s1 .sub r t w
      obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
        arithUpdFacts _ s1 s2 r (s1.regs t - w) hupd hregs
      exact
        arithBinopImmCase .sub r t w (s1.regs t - w) _ s1 s2 ms h hnext hwrite hne31
          hs2pc hs2mem hs2dom hs2regs hsafe0
    · have hhigh : w &&& ~~~(0xFFF000 : BitVec 64) = 0 := by
        rcases hdisj with hh | hh
        · exact absurd hh hlow
        · exact hh
      have hmod : w.toNat % 4096 = 0 := and_not_fff000_eq_zero_toNat_mod hhigh
      have hlt24 : w.toNat < 2 ^ 24 := and_not_fff000_eq_zero_toNat_lt hhigh
      have hweq : BitVec.ofNat 64 (((w >>> 12).toNat % 4096) <<< 12) = w :=
        jumpCmp_ofNat_shifted w hmod hlt24
      have hm : ((w >>> 12).toNat % 4096) < 4096 := Nat.mod_lt _ (by decide)
      have hm0 : ((w >>> 12).toNat % 4096) ≠ 0 := by
        intro h0
        apply hlow
        rw [← hweq, h0]
        simp
      have hb' : bytesInMemoryHOL ms.pc
          (encodeBytes (.addSubImmediate true false
            (BitVec.ofNat 64 (((w >>> 12).toNat % 4096) <<< 12)) t r))
          ms.mem s1.memDomain := by
        rw [hweq]
        exact hb
      have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
          (.addSubImmediate true false w t r) := by
        have h' := arm8Next_addSubImmediateShifted ms s1.memDomain true false
          ((w >>> 12).toNat % 4096) t r hm hm0 hltt32 hltr32 hb'
        rw [hweq] at h'
        exact h'
      have hwrite : execInsn { ms with pc := ms.pc + 4 }
          (.addSubImmediate true false w t r) =
          writeReg { ms with pc := ms.pc + 4 } r (s1.regs t - w) := by
        simp only [execInsn_addSubImmediate_sub, hsrc]
      have hsafe0 : StepSafe s1.memDomain ms :=
        stepSafe_of_encode ms s1.memDomain
          (.addSubImmediate true false (BitVec.ofNat 64 (((w >>> 12).toNat % 4096) <<< 12))
            t r) _ hb'
          (encodeInsn_addSubImmediateShifted true false _ t r hm hm0)
          (decode_encode_addSubImmediateShifted true false _ t r hm hltt32 hltr32)
          (by rfl)
      have hupd := arithUpd_of_start (.inst (.arith (.binop .sub r t (.imm w)))) s1 s2 ms h hast
      have hregs := arithUpd_binop_imm_regs s1 .sub r t w
      obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
        arithUpdFacts _ s1 s2 r (s1.regs t - w) hupd hregs
      exact
        arithBinopImmCase .sub r t w (s1.regs t - w) _ s1 s2 ms h hnext hwrite hne31
          hs2pc hs2mem hs2dom hs2regs hsafe0
  case and =>
    have hok := arithRegOkBinopImm .and r t w s1 s2 ms h
    obtain ⟨⟨hokr, hokt⟩, himm⟩ := hok
    obtain ⟨hltr, havr, hne31⟩ := regOk_of_asm hokr
    obtain ⟨hltt, havt, hnet31⟩ := regOk_of_asm hokt
    have hltr32 : r < 32 := by simpa [arm8Config] using hltr
    have hltt32 : t < 32 := by simpa [arm8Config] using hltt
    have hisSome := isSome_of_asmRegImm (Or.inl rfl) himm
    obtain ⟨⟨n, imms, immr⟩, hbm⟩ := Option.isSome_iff_exists.mp hisSome
    have st := arm8Start _ s1 s2 ms h
    have hast : arm8Ast (.inst (.arith (.binop .and r t (.imm w)))) =
        [.logicalImmediate .and false w t r] := rfl
    have hb : bytesInMemoryHOL ms.pc
        (encodeBytes (.logicalImmediate .and false w t r)) ms.mem s1.memDomain := by
      have hb' := st.bytes
      rw [arm8Enc, hast] at hb'
      simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
    have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
        (.logicalImmediate .and false w t r) :=
      arm8Next_logicalImmediate ms s1.memDomain .and false w t r 0 n imms immr
        (by decide) hbm hltt32 hltr32 hb
    have hsrc := msReadReg_pc st hltt havt hnet31
    have hwrite : execInsn { ms with pc := ms.pc + 4 }
        (.logicalImmediate .and false w t r) =
        writeReg { ms with pc := ms.pc + 4 } r (s1.regs t &&& w) := by
      simp only [execInsn_logicalImmediate, hsrc]
    have hsafe0 : StepSafe s1.memDomain ms :=
      stepSafe_of_encode ms s1.memDomain (.logicalImmediate .and false w t r) _ hb
        (encodeInsn_logicalImmediate .and false w t r 0 n imms immr (by decide) hbm)
        (decode_encode_logicalImmediate .and false w t r 0 n imms immr (by decide) hbm
          hltt32 hltr32) (by rfl)
    have hupd := arithUpd_of_start (.inst (.arith (.binop .and r t (.imm w)))) s1 s2 ms h hast
    have hregs := arithUpd_binop_imm_regs s1 .and r t w
    obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
      arithUpdFacts _ s1 s2 r (s1.regs t &&& w) hupd hregs
    exact
      arithBinopImmCase .and r t w (s1.regs t &&& w) _ s1 s2 ms h hnext hwrite hne31
        hs2pc hs2mem hs2dom hs2regs hsafe0
  case or =>
    have hok := arithRegOkBinopImm .or r t w s1 s2 ms h
    obtain ⟨⟨hokr, hokt⟩, himm⟩ := hok
    obtain ⟨hltr, havr, hne31⟩ := regOk_of_asm hokr
    obtain ⟨hltt, havt, hnet31⟩ := regOk_of_asm hokt
    have hltr32 : r < 32 := by simpa [arm8Config] using hltr
    have hltt32 : t < 32 := by simpa [arm8Config] using hltt
    have hisSome := isSome_of_asmRegImm (Or.inr rfl) himm
    obtain ⟨⟨n, imms, immr⟩, hbm⟩ := Option.isSome_iff_exists.mp hisSome
    have st := arm8Start _ s1 s2 ms h
    have hast : arm8Ast (.inst (.arith (.binop .or r t (.imm w)))) =
        [.logicalImmediate .orr false w t r] := rfl
    have hb : bytesInMemoryHOL ms.pc
        (encodeBytes (.logicalImmediate .orr false w t r)) ms.mem s1.memDomain := by
      have hb' := st.bytes
      rw [arm8Enc, hast] at hb'
      simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
    have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
        (.logicalImmediate .orr false w t r) :=
      arm8Next_logicalImmediate ms s1.memDomain .orr false w t r 1 n imms immr
        (by decide) hbm hltt32 hltr32 hb
    have hsrc := msReadReg_pc st hltt havt hnet31
    have hwrite : execInsn { ms with pc := ms.pc + 4 }
        (.logicalImmediate .orr false w t r) =
        writeReg { ms with pc := ms.pc + 4 } r (s1.regs t ||| w) := by
      simp only [execInsn_logicalImmediate, hsrc]
    have hsafe0 : StepSafe s1.memDomain ms :=
      stepSafe_of_encode ms s1.memDomain (.logicalImmediate .orr false w t r) _ hb
        (encodeInsn_logicalImmediate .orr false w t r 1 n imms immr (by decide) hbm)
        (decode_encode_logicalImmediate .orr false w t r 1 n imms immr (by decide) hbm
          hltt32 hltr32) (by rfl)
    have hupd := arithUpd_of_start (.inst (.arith (.binop .or r t (.imm w)))) s1 s2 ms h hast
    have hregs := arithUpd_binop_imm_regs s1 .or r t w
    obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
      arithUpdFacts _ s1 s2 r (s1.regs t ||| w) hupd hregs
    exact
      arithBinopImmCase .or r t w (s1.regs t ||| w) _ s1 s2 ms h hnext hwrite hne31
        hs2pc hs2mem hs2dom hs2regs hsafe0
  case xor =>
    have hok := arithRegOkBinopImm .xor r t w s1 s2 ms h
    obtain ⟨⟨hokr, hokt⟩, himm⟩ := hok
    obtain ⟨hltr, havr, hne31⟩ := regOk_of_asm hokr
    obtain ⟨hltt, havt, hnet31⟩ := regOk_of_asm hokt
    have hltr32 : r < 32 := by simpa [arm8Config] using hltr
    have hltt32 : t < 32 := by simpa [arm8Config] using hltt
    have st := arm8Start _ s1 s2 ms h
    have hsrc := msReadReg_pc st hltt havt hnet31
    by_cases hneg : w = -1
    · have hast : arm8Ast (.inst (.arith (.binop .xor r t (.imm w)))) =
          [.logicalShiftedRegister .orr true false .lsl 0 t 31 r] := by
        simp only [arm8Ast, arm8Inst, if_pos hneg]
      have hb : bytesInMemoryHOL ms.pc
          (encodeBytes (.logicalShiftedRegister .orr true false .lsl 0 t 31 r)) ms.mem
          s1.memDomain := by
        have hb' := st.bytes
        rw [arm8Enc, hast] at hb'
        simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
      have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
          (.logicalShiftedRegister .orr true false .lsl 0 t 31 r) :=
        arm8Next_logicalShiftedRegister ms s1.memDomain .orr true false .lsl 0 t 31 r 1
          (by decide) (by decide) hltt32 (by decide) hltr32 hb
      have hwrite : execInsn { ms with pc := ms.pc + 4 }
          (.logicalShiftedRegister .orr true false .lsl 0 t 31 r) =
          writeReg { ms with pc := ms.pc + 4 } r (s1.regs t ^^^ w) := by
        simp only [execInsn_logicalShiftedRegister_invert_zero, hsrc]
        rw [hneg, BitVec.not_def, BitVec.xor_comm, ← arith_allOnes]
      have hsafe0 : StepSafe s1.memDomain ms :=
        stepSafe_of_encode ms s1.memDomain
          (.logicalShiftedRegister .orr true false .lsl 0 t 31 r) _ hb
          (encodeInsn_logicalShiftedRegister .orr true false .lsl 0 t 31 r 1 (by decide) (by decide))
          (decode_encode_logicalShiftedRegister .orr true false .lsl 0 t 31 r 1
            (by decide) (by decide) hltt32 (by decide) hltr32) (by rfl)
      have hupd := arithUpd_of_start (.inst (.arith (.binop .xor r t (.imm w)))) s1 s2 ms h hast
      have hregs := arithUpd_binop_imm_regs s1 .xor r t w
      obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
        arithUpdFacts _ s1 s2 r (s1.regs t ^^^ w) hupd hregs
      exact
        arithBinopImmCase .xor r t w (s1.regs t ^^^ w) _ s1 s2 ms h hnext hwrite hne31
          hs2pc hs2mem hs2dom hs2regs hsafe0
    · have hisSome : (encodeBitMask w).isSome = true := by
        have h' := himm
        have hne : (w == -1) = false := by
          rw [beq_eq_false_iff_ne]
          exact hneg
        simp only [asmRegImmOkExact, arm8Config, hne, validImmediate] at h'
        exact h'
      obtain ⟨⟨n, imms, immr⟩, hbm⟩ := Option.isSome_iff_exists.mp hisSome
      have hast : arm8Ast (.inst (.arith (.binop .xor r t (.imm w)))) =
          [.logicalImmediate .eor false w t r] := by
        simp only [arm8Ast, arm8Inst, if_neg hneg]
      have hb : bytesInMemoryHOL ms.pc
          (encodeBytes (.logicalImmediate .eor false w t r)) ms.mem s1.memDomain := by
        have hb' := st.bytes
        rw [arm8Enc, hast] at hb'
        simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
      have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
          (.logicalImmediate .eor false w t r) :=
        arm8Next_logicalImmediate ms s1.memDomain .eor false w t r 2 n imms immr
          (by decide) hbm hltt32 hltr32 hb
      have hwrite : execInsn { ms with pc := ms.pc + 4 }
          (.logicalImmediate .eor false w t r) =
          writeReg { ms with pc := ms.pc + 4 } r (s1.regs t ^^^ w) := by
        simp only [execInsn_logicalImmediate, hsrc]
      have hsafe0 : StepSafe s1.memDomain ms :=
        stepSafe_of_encode ms s1.memDomain (.logicalImmediate .eor false w t r) _ hb
          (encodeInsn_logicalImmediate .eor false w t r 2 n imms immr (by decide) hbm)
          (decode_encode_logicalImmediate .eor false w t r 2 n imms immr (by decide) hbm
            hltt32 hltr32) (by rfl)
      have hupd := arithUpd_of_start (.inst (.arith (.binop .xor r t (.imm w)))) s1 s2 ms h hast
      have hregs := arithUpd_binop_imm_regs s1 .xor r t w
      obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
        arithUpdFacts _ s1 s2 r (s1.regs t ^^^ w) hupd hregs
      exact
        arithBinopImmCase .xor r t w (s1.regs t ^^^ w) _ s1 s2 ms h hnext hwrite hne31
          hs2pc hs2mem hs2dom hs2regs hsafe0

/-! ## `div` -/

/-- `Div` lowers to a single signed `division`. -/
theorem arm8Ast_div (r t u : Nat) :
    arm8Ast (.inst (.arith (.div r t u))) = [.division false u t r] := rfl

/-- The `div` case: the one signed `division` writes the signed quotient, which
is exactly what `arithUpd` records (`assertState` only touches the failure
flag). -/
theorem case_div (r t u : Nat) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.div r t u))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.arith (.div r t u))) s1 s2 ms := by
  have hok := arithRegOkDiv r t u s1 s2 ms h
  obtain ⟨⟨hokr, hokt⟩, hoku⟩ := hok
  obtain ⟨hltr, havr, hne31⟩ := regOk_of_asm hokr
  obtain ⟨hltt, havt, hnet31⟩ := regOk_of_asm hokt
  obtain ⟨hltu, havu, hneu31⟩ := regOk_of_asm hoku
  have hltr32 : r < 32 := by simpa [arm8Config] using hltr
  have hltt32 : t < 32 := by simpa [arm8Config] using hltt
  have hltu32 : u < 32 := by simpa [arm8Config] using hltu
  have st := arm8Start (.inst (.arith (.div r t u))) s1 s2 ms h
  have hast := arm8Ast_div r t u
  have hb : bytesInMemoryHOL ms.pc (encodeBytes (.division false u t r)) ms.mem
      s1.memDomain := by
    have hb' := st.bytes
    rw [arm8Enc, hast] at hb'
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
  have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
      (.division false u t r) :=
    arm8Next_division ms s1.memDomain false u t r hltu32 hltt32 hltr32 hb
  have hsrc := msReadReg_pc st hltt havt hnet31
  have harg := msReadReg_pc st hltu havu hneu31
  have hwrite : execInsn { ms with pc := ms.pc + 4 } (.division false u t r) =
      writeReg { ms with pc := ms.pc + 4 } r ((s1.regs t).sdiv (s1.regs u)) := by
    simp only [execInsn_division_signed, hsrc, harg]
  have hlen : (arm8Enc (.inst (.arith (.div r t u)))).length = 4 := by
    rw [arm8Enc, hast, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      encodeBytes_length]
  have hupd : asmUpd (.inst (.arith (.div r t u))) (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    rw [← st.upd, hlen]
  have hs2pc : s2.pc = s1.pc + 4 := by
    rw [← hupd]; rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd]; intro x; rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; rfl
  have hs2regs : ∀ j, s2.regs j =
      (if j = r then (s1.regs t).sdiv (s1.regs u) else s1.regs j) := by
    intro j
    rw [← hupd]
    simp only [asmUpd, instUpd, updPc, arithUpd_div_regs s1 r t u j]
  have hsafe0 : StepSafe s1.memDomain ms :=
    stepSafe_of_encode ms s1.memDomain (.division false u t r) _ hb (encodeInsn_division false u t r)
      (decode_encode_division false u t r hltu32 hltt32 hltr32) (by rfl)
  have hfields := execWriteFields hne31 hwrite
  exact arithOneCase _ r _ _ s1 s2 ms h hnext hfields hs2pc hs2mem hs2dom hs2regs hsafe0

end Flapjack.Compiler.Encoders.Arm8

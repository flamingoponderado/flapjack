/-
Copyright (c) 2025 Flapjack contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Flapjack.Compiler.Encoders.Arm8.Machine.ArithCase

/-!
# The ARM8 `shift` encoder-correctness cases

This file proves the `arith (.shift ...)` cases of `encoder_correct arm8Target`,
the ARM8 analogue of `case_shift_reg` and `case_shift_imm` in
`Flapjack/Mips32/TargetProof/Arith.lean`.

## The register-shift case

`arm8Ast` lowers `Shift sop destination source (Reg right)` to the single
instruction `Shift (arm8Shv sop) right source destination`, i.e. `Rm = right`
(the shift *amount*) and `Rn = source` (the shifted *value*).  The corrected
`execInsn` of `Machine/Execute.lean` reads the value from `Rn` and the amount
from `Rm`, so the encoded instruction computes
`wordShift sop (readReg source) (readReg right).toNat`, which is exactly the
value `arithUpd` writes.  The one remaining ingredient is the ARM8 shift-range
assertion: `arithUpd` sets `failed` when `(readReg right).toNat ≥ 64`, and
`asmStep` says the source state did not fail, so the amount is below the
register width (where `shiftValue`'s `% 64` and `wordShift` agree).

## The immediate-shift case

`arm8Ast` lowers `Shift sop destination source (Imm value)`, with
`n = value.toNat % 64`, to

* `BitfieldMove (inzero := true) (extend := false) immr imms` with
  `immr = (64 - n) % 64`, `imms = 63 - n` for `.lsl`,
* `BitfieldMove true (sop == .asr) n 63` for `.lsr`/`.asr`, and
* `ExtractRegister n source source destination` for `.ror`.

Two independent defects in the imported infrastructure prevent the case from
being stated for all four shifts, and this file records both as kernel-checked
lemmas rather than weakening the case:

1. `decodeBitMasks` (`Flapjack/Compiler/Encoders/Arm8/Encode.lean`) computes the
   `ones` count of `tmask` as `((S - R) % 2 ^ len) + 1` in `Nat`, i.e. with a
   *truncating* subtraction.  HOL's `DecodeBitMasks` (`arm8Script.sml`,
   `EX (S - R) (len-1) 0`) subtracts the two six-bit words, so the difference is
   taken modulo `64`.  The two agree whenever `S ≥ R` (which is the case for the
   `.lsr`/`.asr` lowering, where `S = 63 ≥ R = n`), but for `.lsl` we have
   `S = 63 - n < R = 64 - n`, and the Lean definition yields `tmask = 1` instead
   of `tmask = 2 ^ 64 - 1`.  Consequently the lowered `BitfieldMove` writes `0`
   instead of `value <<< n` (`bitfieldMove_lsl_writes_zero`), so the `.lsl`
   branch of the case is *false* against the current `Execute.lean`.
2. `BitfieldMove` encodings whose `immr` field is `≥ 32` do not decode at all:
   the ARM8 `bitfieldMove` decoder mask (`decode_bitfieldMove_word` in
   `DecodeProofConditional.lean`) pins the top bit of `immr` to zero, and
   `arm8Next_bitfieldMove` therefore needs `immr < 32`.  The `.lsl` lowering has
   `immr = (64 - n) % 64` (so `immr ≥ 33` for `1 ≤ n < 32`), and the
   `.lsr`/`.asr` lowering has `immr = n` (so `immr ≥ 32` for `n ≥ 32`); in both
   ranges `arm8Next` fails instead of executing the shift
   (`decode_encode_bitfieldMove_high_none`).

The subcases that are unaffected are proved in full below: `case_shift_imm_ror`
(all amounts), and `case_shift_imm_lsr`/`case_shift_imm_asr` under the decoder
bound `value.toNat < 32` that `arm8Next_bitfieldMove` requires.  With defect 1
repaired and `immr` widened to six bits, the same proof structure yields the
missing `.lsl` branch (`bitfieldMove_lsl_eq` isolates the semantic half: the
closed form of the mask HOL's `DecodeBitMasks` would return makes the lowered
instruction compute `value <<< n`).

As in the other `Machine/*Case.lean` files, this is a case split of the single
HOL theorem `arm8_encoder_correct`
(`cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml`), whose
`Inst`/`Arith` branch has no per-case declaration of its own; the module is
Flapjack infrastructure and carries no `@[hol]` tags.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-! ## The two shift models agree on in-range amounts -/

/-- `shiftValue` of the closed executor agrees with `wordShift` of the source
semantics whenever the amount is below the register width. -/
theorem shiftValue_eq_wordShift (v : BitVec 64) (sop : Shift) (a : Nat) (h : a < 64) :
    shiftValue v (arm8Shv sop) a = wordShift sop v a := by
  cases sop <;> simp only [shiftValue, arm8Shv, wordShift, Nat.mod_eq_of_lt h]

/-- `ror64` of the closed executor is `wordShift`'s rotation. -/
theorem ror64_eq_wordShift (v : BitVec 64) (a : Nat) :
    ror64 v a = wordShift .ror v a := by
  simp only [ror64, wordShift, BitVec.rotateRight_def, Nat.mod_mod]

/-! ## Side conditions of an `arith` shift -/

/-- The register side conditions of a register-operand `shift`. -/
theorem arithRegOkShiftReg (sop : Shift) (r t u : Nat) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.shift sop r t (.reg u)))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    (asmRegOkExact r arm8Config = true ∧ asmRegOkExact t arm8Config = true) ∧
      asmRegOkExact u arm8Config = true := by
  have st := arm8Start _ s1 s2 ms h
  have hb := st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, arm8Config,
    Bool.not_false, Bool.true_or, Bool.true_and, Bool.and_eq_true] at hb
  exact ⟨hb.1, hb.2.1⟩

/-- The register side conditions of an immediate-operand `shift`. -/
theorem arithRegOkShiftImm (sop : Shift) (r t : Nat) (w : BitVec 64) (s1 s2 : AsmState 64)
    (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.shift sop r t (.imm w)))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    (asmRegOkExact r arm8Config = true ∧ asmRegOkExact t arm8Config = true) ∧
      w.toNat < 64 := by
  have st := arm8Start _ s1 s2 ms h
  have hb := st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, arm8Config,
    Bool.not_false, Bool.true_or, Bool.true_and, Bool.and_eq_true,
    decide_eq_true_eq] at hb
  exact ⟨hb.1, hb.2.2⟩

/-! ## The register shift amount -/

/-- The lowered `shift` instruction of a register-operand shift. -/
theorem arm8Ast_shift_reg (sop : Shift) (r t u : Nat) :
    arm8Ast (.inst (.arith (.shift sop r t (.reg u)))) = [.shift (arm8Shv sop) u t r] := rfl

/-- The one-instruction `shift` lowering encodes to four bytes. -/
theorem arm8Enc_shift_reg_length (sop : Shift) (r t u : Nat) :
    (arm8Enc (.inst (.arith (.shift sop r t (.reg u))))).length = 4 := by
  rw [arm8Enc, arm8Ast_shift_reg, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    encodeBytes_length]

/-- The ARM8 shift-range assertion fails the step exactly when the register shift
amount is at least 64; `asmStep` therefore bounds the amount by the register
width. -/
theorem shiftReg_amount_lt (sop : Shift) (r t u : Nat) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.shift sop r t (.reg u)))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    (s1.regs u).toNat < 64 := by
  have st := arm8Start _ s1 s2 ms h
  have hupd : asmUpd (.inst (.arith (.shift sop r t (.reg u))))
      (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    have h' := st.upd
    rwa [arm8Enc_shift_reg_length] at h'
  have hf := st.ok
  rw [← hupd] at hf
  simp only [asmUpd, instUpd, arithUpd, regImm, assertState, updPc, updReg] at hf
  by_contra hge
  exact hf (by simp [AsmSem.readReg, hge])

/-! ## The register-shift update -/

/-- The register update of a register-operand `shift`: only the destination
changes, and the failure flag carries the ARM8 shift-range assertion. -/
theorem arithUpd_shift_reg_regs (s : AsmState 64) (sop : Shift) (r t u : Nat) :
    ∀ j, (arithUpd (.shift sop r t (.reg u)) s).regs j =
      (if j = r then wordShift sop (s.regs t) (s.regs u).toNat else s.regs j) := by
  intro j
  simp only [arithUpd, assertState, updReg, regImm]
  rfl

/-! ## The register-shift case -/

/-- Executing the lowered `shift` instruction writes the shifted source value. -/
theorem execInsn_shift (s : Arm8State) (sop : Shift) (r t u : Nat) (v w : BitVec 64)
    (ht : readReg s t = v) (hu : readReg s u = w) (hw : w.toNat < 64) :
    execInsn s (.shift (arm8Shv sop) u t r) = writeReg s r (wordShift sop v w.toNat) := by
  simp only [execInsn, ht, hu, shiftValue_eq_wordShift _ sop _ hw]

/-- `arm8_ast` lowers a register-operand `Shift` to one `shift` instruction, which
the corrected executor runs as `wordShift` of the source register by the amount
in the shift register.  This is exactly the value `arithUpd` writes, so the case
is a straight one-step `encoderCaseStep` run. -/
theorem case_shift_reg (sop : Shift) (r t u : Nat) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.shift sop r t (.reg u)))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.arith (.shift sop r t (.reg u)))) s1 s2 ms := by
  have hok := arithRegOkShiftReg sop r t u s1 s2 ms h
  obtain ⟨⟨hokr, hokt⟩, hoku⟩ := hok
  obtain ⟨hltr, havr, hne31⟩ := regOk_of_asm hokr
  obtain ⟨hltt, havt, hnet31⟩ := regOk_of_asm hokt
  obtain ⟨hltu, havu, hneu31⟩ := regOk_of_asm hoku
  have hltr32 : r < 32 := by simpa [arm8Config] using hltr
  have hltt32 : t < 32 := by simpa [arm8Config] using hltt
  have hltu32 : u < 32 := by simpa [arm8Config] using hltu
  have htu := shiftReg_amount_lt sop r t u s1 s2 ms h
  have st := arm8Start _ s1 s2 ms h
  have hb : bytesInMemoryHOL ms.pc (encodeBytes (.shift (arm8Shv sop) u t r)) ms.mem
      s1.memDomain := by
    have hb' := st.bytes
    rw [arm8Enc, arm8Ast_shift_reg] at hb'
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
  have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
      (.shift (arm8Shv sop) u t r) :=
    arm8Next_shift ms s1.memDomain (arm8Shv sop) u t r hltu32 hltt32 hltr32 hb
  have hsrc := msReadReg_pc st hltt havt hnet31
  have harg := msReadReg_pc st hltu havu hneu31
  have hwrite : execInsn { ms with pc := ms.pc + 4 } (.shift (arm8Shv sop) u t r) =
      writeReg { ms with pc := ms.pc + 4 } r (wordShift sop (s1.regs t) (s1.regs u).toNat) := by
    rw [execInsn_shift _ sop r t u (s1.regs t) (s1.regs u) hsrc harg htu]
  have hsafe0 : StepSafe s1.memDomain ms :=
    stepSafe_of_encode ms s1.memDomain (.shift (arm8Shv sop) u t r) _ hb
      (encodeInsn_shift (arm8Shv sop) u t r)
      (decode_encode_shiftInsn (arm8Shv sop) u t r hltu32 hltt32 hltr32) (by rfl)
  have hupd := arithUpd_of_start (.inst (.arith (.shift sop r t (.reg u)))) s1 s2 ms h
    (arm8Ast_shift_reg sop r t u)
  have hregs := arithUpd_shift_reg_regs s1 sop r t u
  obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
    arithUpdFacts _ s1 s2 r (wordShift sop (s1.regs t) (s1.regs u).toNat) hupd hregs
  have hfields := execWriteFields hne31 hwrite
  exact arithOneCase _ r _ _ s1 s2 ms h hnext hfields hs2pc hs2mem hs2dom hs2regs hsafe0

end Flapjack.Compiler.Encoders.Arm8

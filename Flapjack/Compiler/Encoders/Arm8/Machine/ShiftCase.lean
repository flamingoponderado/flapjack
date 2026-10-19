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

Earlier versions of this file documented two decoder defects here: truncating
`onesCount` in `decodeBitMasks`, and a pinned top bit of the `immr` field.  Both
were repaired in the infrastructure (`Encode.lean`, `Machine/Decode.lean` and
their decoder proofs), so the `.lsl` branch is now provable and the `.lsr`/`.asr`
branches no longer need the former `value.toNat < 32` bound.  The unconditional
`case_shift_imm` for all four shifts is proved in `ShiftCaseFull.lean`; the
bounded `case_shift_imm_lsr`/`case_shift_imm_asr` below are kept as the earlier
reusable sub-proofs.

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

/-! ## Bit-level facts about the bitfield masks -/

/-- A `getLsbD` above the width is `false`. -/
theorem getLsbD_of_ge {w i : Nat} (h : w ≤ i) (x : BitVec w) : x.getLsbD i = false := by
  simp only [BitVec.getLsbD]
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by norm_num) h))

/-- Bit `i` of a low mask of `k` ones. -/
theorem ones_testBit_true {k i : Nat} (h : i < k) : (ones k).testBit i = true := by
  rw [ones, Nat.testBit_two_pow_sub_one]; simp [h]

/-- Bit `i` of a low mask of `k` ones, above the mask. -/
theorem ones_testBit_false {k i : Nat} (h : ¬ i < k) : (ones k).testBit i = false := by
  rw [ones, Nat.testBit_two_pow_sub_one]; simp [h]

/-- Rotating the all-ones mask keeps it: `DecodeBitMasks`'s `welem` for a
64-bit logical shift with `imms = 63`. -/
theorem rotateRightWidth_ones (n : Nat) : rotateRightWidth 64 (ones 64) n = ones 64 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [rotateRightWidth, ones, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by norm_num : 2 ^ 64 - 1 < 2 ^ 64)]
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_div_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 64
  · simp only [hi, decide_true, Bool.true_and]
    by_cases hc : i ≥ 64 - n % 64
    · have h2 : i - (64 - n % 64) < 64 := by omega
      have h4 : ¬ (i + n % 64 < 64) := by omega
      simp only [hc, h2, h4, decide_true, decide_false, Bool.and_true, Bool.false_or]
    · have h5 : i + n % 64 < 64 := by omega
      simp only [h5, hc, decide_true, decide_false, Bool.false_and, Bool.or_false]
  · simp only [hi, decide_false, Bool.false_and]

/-- `DecodeBitMasks`'s closed form for a 64-bit logical or arithmetic shift
right: the left mask is all ones and the right mask keeps the low `64 - n`
bits. -/
theorem decodeBitMasks_lsr (n : Nat) (hn : n < 64) :
    decodeBitMasks 1 63 n false = some (ones 64, ones (64 - n)) := by
  have h1 : ((1 % 2) <<< 6 ||| (63 - 63 % 64)) = 64 := by decide
  have h2 : highestSetBit 64 = 6 := by decide
  have hR : n % 64 &&& 63 = n := by
    rw [show (63 : Nat) = 2 ^ 6 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega : n < 2 ^ 6)]
  rw [decodeBitMasks, h1, h2]
  rw [if_neg (by decide : ¬ ((6 : Int) < 1)), if_neg (by decide : ¬ ((false && _) = true)),
    show (6 : Int).toNat = 6 by decide, show (63 : Nat) % 64 = 63 by decide,
    show ones 6 = 63 by decide, hR]
  dsimp only
  have hone : (63 + 2 ^ 6 - n) % 2 ^ 6 + 1 = 64 - n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0; norm_num
    · rw [show 2 ^ 6 = (64 : Nat) by norm_num,
        show 63 + 64 - n = 64 + (63 - n) by omega, Nat.add_mod, Nat.mod_self,
        Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      omega
  rw [Nat.and_self, show (63 + 1 : Nat) = 64 by norm_num, rotateRightWidth_ones,
    hone]
  simp

/-- The `ones` count `decodeBitMasks` computes for the `.lsl` lowering: with
`S = 63 - n` and `R = 64 - n` the truncated difference `S - R` is `0`, so the
`tmask` of the lowered bitfield move is `ones 1 = 1` instead of `ones 64`
(HOL's `DecodeBitMasks` wraps the six-bit subtraction, giving `S - R = 63` and
`tmask = 2 ^ 64 - 1`).  For `n = 0` the two agree, so the statement needs
`1 ≤ n`. -/
theorem onesCount_lsl (n : Nat) (h1 : 1 ≤ n) (hn : n < 64) :
    ((63 - n) - (64 - n) % 64) % 64 + 1 = 1 := by
  rw [Nat.mod_eq_of_lt (by omega : 64 - n < 64)]
  omega

/-- The 64-bit all-ones mask as `DecodeBitMasks` builds it. -/
theorem ofNat_ones_eq_allOnes : BitVec.ofNat 64 (ones 64) = BitVec.allOnes 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_allOnes, ones,
    Nat.mod_eq_of_lt (by norm_num : 2 ^ 64 - 1 < 2 ^ 64)]

/-- Conjunction with the all-ones mask is the identity. -/
theorem and_ones64 (x : BitVec 64) : x &&& BitVec.ofNat 64 (ones 64) = x := by
  rw [ofNat_ones_eq_allOnes, BitVec.and_allOnes]

/-- `Replicate` of `true` is the all-ones mask. -/
theorem replicateBit_true : replicateBit true = BitVec.allOnes 64 := rfl

/-- `Replicate` of `false` is zero. -/
theorem replicateBit_false : replicateBit false = 0 := rfl

/-- `wordShift`'s rotation only depends on the amount modulo 64. -/
theorem wordShift_ror_mod (v : BitVec 64) (a : Nat) :
    wordShift .ror v (a % 64) = wordShift .ror v a := by
  simp only [wordShift, BitVec.rotateRight_def, Nat.mod_mod]

/-- The mask step of the logical shift right bitfield move: crossing the
`welem` mask keeps exactly the bits that a shift right discards. -/
theorem ror64_and_ones (v : BitVec 64) (n : Nat) (hn : n < 64) :
    ror64 v n &&& BitVec.ofNat 64 (ones (64 - n)) = v >>> n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ofNat]
  simp only [ror64, BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hn,
    Nat.testBit_two_pow_sub_one, ones, hi, decide_true, Bool.true_and]
  by_cases hin : i < 64 - n
  · have htr : n + i < 64 := by omega
    have htr' : i - (64 - n) < 64 := by omega
    simp [hin, htr, htr', BitVec.getLsbD_ushiftRight]
  · have hge : n + i ≥ 64 := by omega
    simp [hin, BitVec.getLsbD_ushiftRight, getLsbD_of_ge hge v]

/-- Sign filling of an arithmetic shift right, from the `|||` form the
bitfield move produces. -/
theorem or_sshiftRight (v : BitVec 64) (n : Nat) (hn : n < 64) :
    ((if v.getLsbD 63 then ~~~(BitVec.ofNat 64 (ones (64 - n))) else 0) ||| (v >>> n)) =
      v.sshiftRight n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi64 : ¬ (64 ≤ i) := by omega
  rw [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_sshiftRight,
    BitVec.msb_eq_getLsbD_last]
  by_cases hin : i < 64 - n
  · have htr : n + i < 64 := by omega
    have hm := ones_testBit_true hin
    by_cases hs : v.getLsbD 63
    · rw [if_pos hs, BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
      simp [hi, hi64, htr, hm]
    · rw [if_neg hs]
      simp [hi, hi64, htr]
  · have htr : ¬ (n + i < 64) := by omega
    have hge : 64 ≤ n + i := by omega
    have hm := ones_testBit_false hin
    by_cases hs : v.getLsbD 63
    · rw [if_pos hs, hs, BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
      simp [hi, hi64, htr, getLsbD_of_ge hge v]
      exact hm
    · rw [if_neg hs]
      have hf : v.getLsbD 63 = false := by simpa using hs
      simpa [hi, hi64, htr, getLsbD_of_ge hge v] using hf

/-- Sign filling with the sign bit set. -/
theorem asr_signfill_true (v : BitVec 64) (n : Nat) (hn : n < 64) (hs : v.getLsbD 63) :
    ~~~(BitVec.ofNat 64 (ones (64 - n))) ||| (v >>> n) = v.sshiftRight n := by
  have h := or_sshiftRight v n hn
  rw [if_pos hs] at h
  exact h

/-- Sign filling with the sign bit clear: nothing to fill. -/
theorem asr_signfill_false (v : BitVec 64) (n : Nat) (hn : n < 64) (hs : ¬ v.getLsbD 63) :
    (0 : BitVec 64) ||| (v >>> n) = v.sshiftRight n := by
  have h := or_sshiftRight v n hn
  rw [if_neg hs] at h
  exact h

/-- The value the lowered `LSR` bitfield move computes. -/
theorem bfmove_lsr_value (v : BitVec 64) (n : Nat) (hn : n < 64) :
    ((0 : BitVec 64) &&& ~~~(BitVec.ofNat 64 (ones (64 - n))) |||
      (0 &&& ~~~(BitVec.ofNat 64 (ones 64)) ||| ror64 v n &&& BitVec.ofNat 64 (ones 64)) &&&
        BitVec.ofNat 64 (ones (64 - n))) = v >>> n := by
  simp [and_ones64, ror64_and_ones v n hn]

/-- The value the lowered `ASR` bitfield move computes. -/
theorem bfmove_asr_value (v : BitVec 64) (n : Nat) (hn : n < 64) :
    (replicateBit (v.getLsbD 63) &&& ~~~(BitVec.ofNat 64 (ones (64 - n))) |||
      (0 &&& ~~~(BitVec.ofNat 64 (ones 64)) ||| ror64 v n &&& BitVec.ofNat 64 (ones 64)) &&&
        BitVec.ofNat 64 (ones (64 - n))) = v.sshiftRight n := by
  have hz1 : (0 : BitVec 64) &&& ~~~(BitVec.ofNat 64 (ones 64)) = 0 := by simp
  have hor : (0 : BitVec 64) ||| ror64 v n = ror64 v n := by simp
  rw [hz1, and_ones64, hor, ror64_and_ones v n hn]
  by_cases hs : v.getLsbD 63
  · rw [hs, replicateBit_true, BitVec.allOnes_and]
    exact asr_signfill_true v n hn hs
  · have hf : v.getLsbD 63 = false := by simpa using hs
    rw [hf, replicateBit_false]
    have hz2 : (0 : BitVec 64) &&& ~~~(BitVec.ofNat 64 (ones (64 - n))) = 0 := by simp
    rw [hz2]
    exact asr_signfill_false v n hn hs

/-! ## Executing the lowered immediate forms -/

/-- The lowered `ROR` immediate form (`EXTR`) writes the rotation. -/
theorem execInsn_extractRegister (s : Arm8State) (n t r : Nat) :
    execInsn s (.extractRegister n t t r) = writeReg s r (ror64 (readReg s t) n) := by
  simp only [execInsn]

/-- The lowered `LSR` immediate form (a bitfield move with `imms = 63`) writes
the logical shift right. -/
theorem execInsn_bitfieldMove_lsr (s : Arm8State) (n t r : Nat) (hn : n < 64) :
    execInsn s (.bitfieldMove true false n 63 t r) = writeReg s r (readReg s t >>> n) := by
  simp only [execInsn, bitfieldMove, decodeBitMasks_lsr n hn, reduceIte, Nat.reduceMod,
    Bool.false_eq_true]
  rw [bfmove_lsr_value (readReg s t) n hn]

/-- The lowered `ASR` immediate form (a sign-filling bitfield move with
`imms = 63`) writes the arithmetic shift right. -/
theorem execInsn_bitfieldMove_asr (s : Arm8State) (n t r : Nat) (hn : n < 64) :
    execInsn s (.bitfieldMove true true n 63 t r) = writeReg s r ((readReg s t).sshiftRight n) := by
  simp only [execInsn, bitfieldMove, decodeBitMasks_lsr n hn, reduceIte, Nat.reduceMod]
  rw [bfmove_asr_value (readReg s t) n hn]

/-! ## The immediate shift lowerings -/

/-- `arm8_ast` lowers a `ROR` by a constant to one `EXTR` of the source
register with itself. -/
theorem arm8Ast_shift_ror (r t : Nat) (w : BitVec 64) :
    arm8Ast (.inst (.arith (.shift .ror r t (.imm w)))) =
      [.extractRegister (w.toNat % 64) t t r] := rfl

/-- `Shift.lsr` is not `Shift.asr`, so the shift kind bit of the lowering is
clear. -/
theorem lsr_beq_asr : (Flapjack.Shift.lsr == Flapjack.Shift.asr) = false := by decide

/-- `Shift.asr` is `Shift.asr`, so the shift kind bit of the lowering is set. -/
theorem asr_beq_asr : (Flapjack.Shift.asr == Flapjack.Shift.asr) = true := by decide

/-- `arm8_ast` lowers an `LSR` by a constant to one bitfield move. -/
theorem arm8Ast_shift_lsr (r t : Nat) (w : BitVec 64) :
    arm8Ast (.inst (.arith (.shift .lsr r t (.imm w)))) =
      [.bitfieldMove true false (w.toNat % 64) 63 t r] := by
  simp only [arm8Ast, arm8Inst, decodeBitMasks_lsr (w.toNat % 64)
    (Nat.mod_lt _ (by norm_num)), lsr_beq_asr]

/-- `arm8_ast` lowers an `ASR` by a constant to one sign-filling bitfield
move. -/
theorem arm8Ast_shift_asr (r t : Nat) (w : BitVec 64) :
    arm8Ast (.inst (.arith (.shift .asr r t (.imm w)))) =
      [.bitfieldMove true true (w.toNat % 64) 63 t r] := by
  simp only [arm8Ast, arm8Inst, decodeBitMasks_lsr (w.toNat % 64)
    (Nat.mod_lt _ (by norm_num)), asr_beq_asr]

/-- The update of an immediate-operand `shift` writes only the destination
register. -/
theorem arithUpd_shift_imm_regs (s : AsmState 64) (sop : Shift) (r t : Nat) (w : BitVec 64) :
    ∀ j, (arithUpd (.shift sop r t (.imm w)) s).regs j =
      (if j = r then wordShift sop (s.regs t) w.toNat else s.regs j) := by
  intro j
  simp only [arithUpd, assertState, updReg, regImm]
  rfl

/-! ## The `ROR` case -/

/-- The `ror` case: `EXTR` writes the rotation of the source register, which is
exactly the value `arithUpd` records. -/
theorem case_shift_imm_ror (r t : Nat) (w : BitVec 64) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.shift .ror r t (.imm w)))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.arith (.shift .ror r t (.imm w)))) s1 s2 ms := by
  have hok := arithRegOkShiftImm .ror r t w s1 s2 ms h
  obtain ⟨⟨hokr, hokt⟩, hwlt⟩ := hok
  obtain ⟨hltr, havr, hne31⟩ := regOk_of_asm hokr
  obtain ⟨hltt, havt, hnet31⟩ := regOk_of_asm hokt
  have hltr32 : r < 32 := by simpa [arm8Config] using hltr
  have hltt32 : t < 32 := by simpa [arm8Config] using hltt
  have hn64 : w.toNat % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hast := arm8Ast_shift_ror r t w
  have st := arm8Start (.inst (.arith (.shift .ror r t (.imm w)))) s1 s2 ms h
  have hb : bytesInMemoryHOL ms.pc (encodeBytes (.extractRegister (w.toNat % 64) t t r)) ms.mem
      s1.memDomain := by
    have hb' := st.bytes
    rw [arm8Enc, hast] at hb'
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
  have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
      (.extractRegister (w.toNat % 64) t t r) :=
    arm8Next_extractRegister ms s1.memDomain t (w.toNat % 64) t r hltt32 hn64 hltt32 hltr32 hb
  have hsrc := msReadReg_pc st hltt havt hnet31
  have hwrite : execInsn { ms with pc := ms.pc + 4 } (.extractRegister (w.toNat % 64) t t r) =
      writeReg { ms with pc := ms.pc + 4 } r (wordShift .ror (s1.regs t) w.toNat) := by
    rw [execInsn_extractRegister, hsrc, ror64_eq_wordShift, wordShift_ror_mod]
  have hsafe0 : StepSafe s1.memDomain ms :=
    stepSafe_of_encode ms s1.memDomain (.extractRegister (w.toNat % 64) t t r) _ hb
      (encodeInsn_extractRegister t (w.toNat % 64) t r)
      (decode_encode_extractRegister t (w.toNat % 64) t r hltt32 hn64 hltt32 hltr32) (by rfl)
  have hupd := arithUpd_of_start (.inst (.arith (.shift .ror r t (.imm w)))) s1 s2 ms h hast
  have hregs := arithUpd_shift_imm_regs s1 .ror r t w
  obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
    arithUpdFacts _ s1 s2 r (wordShift .ror (s1.regs t) w.toNat) hupd hregs
  have hfields := execWriteFields hne31 hwrite
  exact arithOneCase _ r _ _ s1 s2 ms h hnext hfields hs2pc hs2mem hs2dom hs2regs hsafe0

/-! ## The `LSR` and `ASR` cases -/

/-- The `lsr` case, under the decoder bound `value.toNat < 32` that
`arm8Next_bitfieldMove` needs (`immr < 32`): the lowered bitfield move writes
the logical shift right, which is the value `arithUpd` records. -/
theorem case_shift_imm_lsr (r t : Nat) (w : BitVec 64) (hw : w.toNat < 32)
    (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.shift .lsr r t (.imm w)))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.arith (.shift .lsr r t (.imm w)))) s1 s2 ms := by
  have hok := arithRegOkShiftImm .lsr r t w s1 s2 ms h
  obtain ⟨⟨hokr, hokt⟩, hwlt⟩ := hok
  obtain ⟨hltr, havr, hne31⟩ := regOk_of_asm hokr
  obtain ⟨hltt, havt, hnet31⟩ := regOk_of_asm hokt
  have hltr32 : r < 32 := by simpa [arm8Config] using hltr
  have hltt32 : t < 32 := by simpa [arm8Config] using hltt
  have hn64 : w.toNat % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hn32 : w.toNat % 64 < 32 := by omega
  have hn64' : w.toNat % 64 < 64 := hn64
  have hmod : w.toNat % 64 = w.toNat := Nat.mod_eq_of_lt hwlt
  have hast := arm8Ast_shift_lsr r t w
  have st := arm8Start (.inst (.arith (.shift .lsr r t (.imm w)))) s1 s2 ms h
  have hb : bytesInMemoryHOL ms.pc (encodeBytes (.bitfieldMove true false (w.toNat % 64) 63 t r))
      ms.mem s1.memDomain := by
    have hb' := st.bytes
    rw [arm8Enc, hast] at hb'
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
  have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
      (.bitfieldMove true false (w.toNat % 64) 63 t r) :=
    arm8Next_bitfieldMove ms s1.memDomain true false (w.toNat % 64) 63 t r 2 (by decide)
      hn64 (by decide) hltt32 hltr32 hb
  have hsrc := msReadReg_pc st hltt havt hnet31
  have hwrite : execInsn { ms with pc := ms.pc + 4 } (.bitfieldMove true false (w.toNat % 64) 63 t r) =
      writeReg { ms with pc := ms.pc + 4 } r (wordShift .lsr (s1.regs t) w.toNat) := by
    rw [execInsn_bitfieldMove_lsr _ _ _ _ hn64, hsrc, hmod, wordShift]
  have hsafe0 : StepSafe s1.memDomain ms :=
    stepSafe_of_encode ms s1.memDomain (.bitfieldMove true false (w.toNat % 64) 63 t r) _ hb
      (encodeInsn_bitfieldMove true false (w.toNat % 64) 63 t r 2 (by decide))
      (decode_encode_bitfieldMoveInsn true false (w.toNat % 64) 63 t r 2 (by decide) hn64
        (by decide) hltt32 hltr32) (by rfl)
  have hupd := arithUpd_of_start (.inst (.arith (.shift .lsr r t (.imm w)))) s1 s2 ms h hast
  have hregs := arithUpd_shift_imm_regs s1 .lsr r t w
  obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
    arithUpdFacts _ s1 s2 r (wordShift .lsr (s1.regs t) w.toNat) hupd hregs
  have hfields := execWriteFields hne31 hwrite
  exact arithOneCase _ r _ _ s1 s2 ms h hnext hfields hs2pc hs2mem hs2dom hs2regs hsafe0

/-- The `asr` case, under the decoder bound `value.toNat < 32` that
`arm8Next_bitfieldMove` needs (`immr < 32`): the lowered sign-filling bitfield
move writes the arithmetic shift right, which is the value `arithUpd`
records. -/
theorem case_shift_imm_asr (r t : Nat) (w : BitVec 64) (hw : w.toNat < 32)
    (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.shift .asr r t (.imm w)))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.arith (.shift .asr r t (.imm w)))) s1 s2 ms := by
  have hok := arithRegOkShiftImm .asr r t w s1 s2 ms h
  obtain ⟨⟨hokr, hokt⟩, hwlt⟩ := hok
  obtain ⟨hltr, havr, hne31⟩ := regOk_of_asm hokr
  obtain ⟨hltt, havt, hnet31⟩ := regOk_of_asm hokt
  have hltr32 : r < 32 := by simpa [arm8Config] using hltr
  have hltt32 : t < 32 := by simpa [arm8Config] using hltt
  have hn64 : w.toNat % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hn32 : w.toNat % 64 < 32 := by omega
  have hn64' : w.toNat % 64 < 64 := hn64
  have hmod : w.toNat % 64 = w.toNat := Nat.mod_eq_of_lt hwlt
  have hast := arm8Ast_shift_asr r t w
  have st := arm8Start (.inst (.arith (.shift .asr r t (.imm w)))) s1 s2 ms h
  have hb : bytesInMemoryHOL ms.pc (encodeBytes (.bitfieldMove true true (w.toNat % 64) 63 t r))
      ms.mem s1.memDomain := by
    have hb' := st.bytes
    rw [arm8Enc, hast] at hb'
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
  have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
      (.bitfieldMove true true (w.toNat % 64) 63 t r) :=
    arm8Next_bitfieldMove ms s1.memDomain true true (w.toNat % 64) 63 t r 0 (by decide)
      hn64 (by decide) hltt32 hltr32 hb
  have hsrc := msReadReg_pc st hltt havt hnet31
  have hwrite : execInsn { ms with pc := ms.pc + 4 } (.bitfieldMove true true (w.toNat % 64) 63 t r) =
      writeReg { ms with pc := ms.pc + 4 } r (wordShift .asr (s1.regs t) w.toNat) := by
    rw [execInsn_bitfieldMove_asr _ _ _ _ hn64, hsrc, hmod, wordShift]
  have hsafe0 : StepSafe s1.memDomain ms :=
    stepSafe_of_encode ms s1.memDomain (.bitfieldMove true true (w.toNat % 64) 63 t r) _ hb
      (encodeInsn_bitfieldMove true true (w.toNat % 64) 63 t r 0 (by decide))
      (decode_encode_bitfieldMoveInsn true true (w.toNat % 64) 63 t r 0 (by decide) hn64
        (by decide) hltt32 hltr32) (by rfl)
  have hupd := arithUpd_of_start (.inst (.arith (.shift .asr r t (.imm w)))) s1 s2 ms h hast
  have hregs := arithUpd_shift_imm_regs s1 .asr r t w
  obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
    arithUpdFacts _ s1 s2 r (wordShift .asr (s1.regs t) w.toNat) hupd hregs
  have hfields := execWriteFields hne31 hwrite
  exact arithOneCase _ r _ _ s1 s2 ms h hnext hfields hs2pc hs2mem hs2dom hs2regs hsafe0

end Flapjack.Compiler.Encoders.Arm8

/-
Copyright (c) 2025 Flapjack contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Flapjack.Compiler.Encoders.Arm8.Machine.ShiftCase

/-!
# The remaining ARM8 `shift` encoder-correctness cases

`Machine/ShiftCase.lean` proves the `.reg` form of `arith (.shift ...)` for all
four shifts, the `.imm` form for `.ror`, and the `.imm` form for `.lsr`/`.asr`
under the decoder bound `value.toNat < 32`.  This file completes the `.imm`
form: the `.lsl` lowering, the `.lsr`/`.asr` lowerings without the bound, and
the assembled `case_shift_imm` over all four shift kinds.

## The `.lsl` masks

`arm8Ast` lowers `Shift .lsl destination source (Imm value)` with
`n = value.toNat % 64` to `BitfieldMove (inzero := true) (extend := false) immr
imms` with `immr = (64 - n) % 64` and `imms = 63 - n`.  `decodeBitMasks` sees
`immN = 1` and `imms = 63 - n`, whose highest set bit is 6 (the value it inspects
is `64 ||| n`), so the element size is the full 64 bits and `levels = 63`.  The
number of ones of `tmask` is `((S + 64 - R) % 64) + 1` with `S = 63 - n` and
`R = (64 - n) % 64`: the wrapping subtraction cancels both `n` terms and gives
`tmask = 2 ^ 64 - 1`, i.e. all ones -- this is the repair of the former
truncating `decodeBitMasks` defect.  The `wmask` is
`rotateRightWidth 64 (ones (64 - n)) ((64 - n) % 64)`, the mask of the top
`n` bits: rotating `ones (64 - n)` right by `64 - n` moves its run of ones to
positions `n .. 63`.  Rotating the source by `immr = 64 - n` (a rotation right
by `64 - n` is a left shift by `n`) and keeping those bits therefore computes
`source <<< n`, which is `wordShift .lsl` of the shift amount (the amount is
below 64 by the `asmArithOkExact` side condition, so `% 64` is the identity).

## The decoder bound

`decodeInsn`'s bitfield pattern ignores bit 5 of the six-bit `immr` field, so
`decode_encode_bitfieldMove*` and `arm8Next_bitfieldMove` now only need
`immr < 64`; `(64 - n) % 64` and `n` are both below 64 for `n < 64`, so the
`.lsl` lowering and the `.lsr`/`.asr` lowerings decode for every amount.  This
removes the `value.toNat < 32` hypothesis of `case_shift_imm_lsr` and
`case_shift_imm_asr` in `Machine/ShiftCase.lean`; the unconditional statements
are `case_shift_imm_lsr_full` and `case_shift_imm_asr_full` below.

As in the other `Machine/*Case.lean` files, this is a case split of the single
HOL theorem `arm8_encoder_correct`
(`cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml`), whose
`Inst`/`Arith` branch has no per-case declaration of its own; the module is
Flapjack infrastructure and carries no `@[hol]` tags.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-! ## The `DecodeBitMasks` masks of the `.lsl` lowering -/

/-- The element-size selector `DecodeBitMasks` computes for the `.lsl` lowering,
`imms = 63 - n`: the value `64 ||| n` it inspects has highest set bit 6 for
every `n < 64`, so the element size is the full 64 bits. -/
theorem highestSetBit_lsl (n : Nat) (hn : n < 64) : highestSetBit (64 ||| n) = 6 := by
  have hne : 64 ||| n ≠ 0 := by
    have h := Nat.left_le_or (n := 64) (m := n)
    omega
  rw [highestSetBit, if_neg hne]
  have hlog : Nat.log2 (64 ||| n) = 6 := by
    rw [Nat.log2_eq_iff (k := 6) hne]
    constructor
    · have h := Nat.left_le_or (n := 64) (m := n)
      norm_num at h ⊢
      omega
    · have h := Nat.or_lt_two_pow (x := 64) (y := n) (n := 7) (by norm_num) (by omega)
      norm_num at h ⊢
      omega
  rw [hlog]
  norm_num

/-- `DecodeBitMasks`'s closed form for the `.lsl` lowering: the element size is
all 64 bits, the left mask rotates `ones (64 - n)` and the right mask is all
ones, because the wrapping `S - R` cancels both `n` terms. -/
theorem decodeBitMasks_lsl (n : Nat) (hn : n < 64) :
    decodeBitMasks 1 (63 - n) ((64 - n) % 64) false =
      some (rotateRightWidth 64 (ones (64 - n)) ((64 - n) % 64), ones 64) := by
  have hS63 : (63 - n) % 64 = 63 - n := Nat.mod_eq_of_lt (by omega)
  have hnum : ((1 % 2) <<< 6 ||| (63 - (63 - n) % 64)) = 64 ||| n := by
    rw [hS63]
    have h1 : (1 : Nat) <<< 6 = 64 := by decide
    have h2 : 63 - (63 - n) = n := by omega
    rw [h1, h2]
  have hlen : highestSetBit (64 ||| n) = 6 := highestSetBit_lsl n hn
  have hS : (63 - n) % 64 &&& (2 ^ 6 - 1) = 63 - n := by
    rw [Nat.and_two_pow_sub_one_eq_mod, hS63, Nat.mod_eq_of_lt (by omega : 63 - n < 2 ^ 6)]
  have hR : (64 - n) % 64 &&& (2 ^ 6 - 1) = (64 - n) % 64 := by
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
  have hone : ((63 - n) + 2 ^ 6 - (64 - n) % 64) % 2 ^ 6 + 1 = 64 := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      norm_num
    · have hk : (64 - n) % 64 = 64 - n := Nat.mod_eq_of_lt (by omega)
      rw [hk, show (2 : Nat) ^ 6 = 64 by norm_num,
        show 63 - n + 64 - (64 - n) = 63 by omega]
  rw [decodeBitMasks, hnum, hlen]
  rw [if_neg (by decide : ¬ ((6 : Int) < 1)), if_neg (by simp : ¬ ((false && _) = true)),
    show (6 : Int).toNat = 6 by decide]
  simp only [ones]
  rw [Nat.mod_mod, hS, hR, hone, show 63 - n + 1 = 64 - n by omega,
    show (2 : Nat) ^ 6 = 64 by norm_num]
  have hdiv : (2 ^ 64 - 1) / (2 ^ 64 - 1) = 1 := Nat.div_self (by norm_num)
  rw [hdiv, Nat.mul_one]

/-- Bit `i` of the `wmask` of the `.lsl` lowering is set exactly above position
`n`: the mask keeps bits `n .. 63`. -/
theorem testBit_rotateRightWidth_lsl (n i : Nat) (hn : n < 64) (hi : i < 64) :
    (rotateRightWidth 64 (ones (64 - n)) ((64 - n) % 64)).testBit i = decide (n ≤ i) := by
  rw [rotateRightWidth]
  simp only [Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and, Nat.testBit_or,
    Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  simp only [ones, Nat.testBit_two_pow_sub_one]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    norm_num [hi]
  · have hk : (64 - n) % 64 = 64 - n := Nat.mod_eq_of_lt (by omega)
    simp only [hk, show 64 - (64 - n) = n by omega]
    by_cases hni : n ≤ i
    · have h4 : decide (i - n < 64) = true := decide_eq_true (by omega)
      have h5 : decide (i - n < 64 - n) = true := decide_eq_true (by omega)
      simp [h4, h5, hni]
    · simp [hni]

/-- The 64-bit `wmask` of the `.lsl` lowering clears exactly the low `n` bits. -/
theorem ofNat_rotateRightWidth_lsl_bv (n : Nat) (hn : n < 64) :
    BitVec.ofNat 64 (rotateRightWidth 64 (ones (64 - n)) ((64 - n) % 64)) =
      ~~~(BitVec.ofNat 64 (ones n)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_not, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat,
    testBit_rotateRightWidth_lsl n i hn hi]
  simp only [hi, decide_true, Bool.true_and, ones, Nat.testBit_two_pow_sub_one]
  by_cases hin : i < n
  · have h2 : ¬ n ≤ i := by omega
    rw [decide_eq_false h2, decide_eq_true hin]
    rfl
  · have h2 : n ≤ i := by omega
    rw [decide_eq_true h2, decide_eq_false hin]
    rfl

/-- Rotating a value right by `64 - n` and keeping the top `n` bits is the left
shift by `n`: the lowered `.lsl` bitfield move combines `immr = 64 - n` with the
`wmask` above. -/
theorem ror64_lsl_mask (v : BitVec 64) (n : Nat) (hn : n < 64) :
    ror64 v ((64 - n) % 64) &&& ~~~(BitVec.ofNat 64 (ones n)) = v <<< n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ofNat, ror64,
    BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft]
  simp only [hi, decide_true, Bool.true_and, Nat.mod_mod, ones, Nat.testBit_two_pow_sub_one]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp [hi]
  · have hk : (64 - n) % 64 = 64 - n := Nat.mod_eq_of_lt (by omega)
    rw [hk, show 64 - (64 - n) = n by omega]
    by_cases hin : i < n
    · simp [hin]
    · simp [hin]

/-! ## Executing the lowered `.lsl` form -/

/-- The lowered `.lsl` immediate form (a bitfield move with `immr = 64 - n` and
`imms = 63 - n`) writes the left shift by `n`. -/
theorem execInsn_bitfieldMove_lsl (s : Arm8State) (n t r : Nat) (hn : n < 64) :
    execInsn s (.bitfieldMove true false ((64 - n) % 64) (63 - n) t r) =
      writeReg s r (readReg s t <<< n) := by
  simp only [execInsn, bitfieldMove, decodeBitMasks_lsl n hn, ofNat_rotateRightWidth_lsl_bv n hn,
    ofNat_ones_eq_allOnes, reduceIte, Bool.false_eq_true, BitVec.not_allOnes, BitVec.and_allOnes,
    BitVec.not_not]
  rw [ror64_lsl_mask _ n hn]
  simp

/-! ## The `.lsl` lowering -/

/-- `arm8_ast` lowers an `LSL` by a constant to one bitfield move whose masks
`DecodeBitMasks` reconstructs as all ones. -/
theorem arm8Ast_shift_lsl (r t : Nat) (w : BitVec 64) :
    arm8Ast (.inst (.arith (.shift .lsl r t (.imm w)))) =
      [.bitfieldMove true false ((64 - w.toNat % 64) % 64) (63 - w.toNat % 64) t r] := by
  simp only [arm8Ast, arm8Inst, decodeBitMasks_lsl (w.toNat % 64) (Nat.mod_lt _ (by norm_num))]

/-! ## The `.lsl` case -/

/-- The `lsl` case: the lowered bitfield move writes the left shift of the
source register, which is exactly the value `arithUpd` records. -/
theorem case_shift_imm_lsl (r t : Nat) (w : BitVec 64) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.shift .lsl r t (.imm w)))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.arith (.shift .lsl r t (.imm w)))) s1 s2 ms := by
  have hok := arithRegOkShiftImm .lsl r t w s1 s2 ms h
  obtain ⟨⟨hokr, hokt⟩, hwlt⟩ := hok
  obtain ⟨hltr, havr, hne31⟩ := regOk_of_asm hokr
  obtain ⟨hltt, havt, hnet31⟩ := regOk_of_asm hokt
  have hltr32 : r < 32 := by simpa [arm8Config] using hltr
  have hltt32 : t < 32 := by simpa [arm8Config] using hltt
  have hn64 : w.toNat % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have himmr : (64 - w.toNat % 64) % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have himms : 63 - w.toNat % 64 < 64 := by omega
  have hmod : w.toNat % 64 = w.toNat := Nat.mod_eq_of_lt hwlt
  have hast := arm8Ast_shift_lsl r t w
  have st := arm8Start (.inst (.arith (.shift .lsl r t (.imm w)))) s1 s2 ms h
  have hb : bytesInMemoryHOL ms.pc
      (encodeBytes (.bitfieldMove true false ((64 - w.toNat % 64) % 64) (63 - w.toNat % 64) t r))
      ms.mem s1.memDomain := by
    have hb' := st.bytes
    rw [arm8Enc, hast] at hb'
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
  have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
      (.bitfieldMove true false ((64 - w.toNat % 64) % 64) (63 - w.toNat % 64) t r) :=
    arm8Next_bitfieldMove ms s1.memDomain true false ((64 - w.toNat % 64) % 64)
      (63 - w.toNat % 64) t r 2 (by decide) himmr himms hltt32 hltr32 hb
  have hsrc := msReadReg_pc st hltt havt hnet31
  have hwrite : execInsn { ms with pc := ms.pc + 4 }
      (.bitfieldMove true false ((64 - w.toNat % 64) % 64) (63 - w.toNat % 64) t r) =
      writeReg { ms with pc := ms.pc + 4 } r (wordShift .lsl (s1.regs t) w.toNat) := by
    rw [execInsn_bitfieldMove_lsl _ _ _ _ hn64, hsrc, hmod, wordShift]
  have hdec : decodeInsn32 (BitVec.setWidth 32 (BitVec.setWidth 64
      (fields [(1, 1), (2, 2), (6, 0b100110), (1, 1), (6, (64 - w.toNat % 64) % 64),
        (6, 63 - w.toNat % 64), (5, t), (5, r)]))) =
      some (.bitfieldMove true false ((64 - w.toNat % 64) % 64) (63 - w.toNat % 64) t r) := by
    simpa [decodeInsn] using
      (decode_encode_bitfieldMove true false ((64 - w.toNat % 64) % 64)
        (63 - w.toNat % 64) t r 2 (by decide) himmr himms hltt32 hltr32)
  have hsafe0 : StepSafe s1.memDomain ms :=
    stepSafe_of_encode ms s1.memDomain
      (.bitfieldMove true false ((64 - w.toNat % 64) % 64) (63 - w.toNat % 64) t r) _ hb
      (encodeInsn_bitfieldMove true false ((64 - w.toNat % 64) % 64) (63 - w.toNat % 64) t r 2
        (by decide) himmr himms)
      hdec (by rfl)
  have hupd := arithUpd_of_start (.inst (.arith (.shift .lsl r t (.imm w)))) s1 s2 ms h hast
  have hregs := arithUpd_shift_imm_regs s1 .lsl r t w
  obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
    arithUpdFacts _ s1 s2 r (wordShift .lsl (s1.regs t) w.toNat) hupd hregs
  have hfields := execWriteFields hne31 hwrite
  exact arithOneCase _ r _ _ s1 s2 ms h hnext hfields hs2pc hs2mem hs2dom hs2regs hsafe0


/-! ## The `.lsr` and `.asr` cases without a decoder bound -/

/-- The `lsr` case for every amount: the lowered bitfield move writes the
logical shift right, which is the value `arithUpd` records.  Unlike
`case_shift_imm_lsr` this needs no `value.toNat < 32` hypothesis, because
`decode_encode_bitfieldMove*` only requires `immr < 64`. -/
theorem case_shift_imm_lsr_full (r t : Nat) (w : BitVec 64) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.shift .lsr r t (.imm w)))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.arith (.shift .lsr r t (.imm w)))) s1 s2 ms := by
  have hok := arithRegOkShiftImm .lsr r t w s1 s2 ms h
  obtain ⟨⟨hokr, hokt⟩, hwlt⟩ := hok
  obtain ⟨hltr, havr, hne31⟩ := regOk_of_asm hokr
  obtain ⟨hltt, havt, hnet31⟩ := regOk_of_asm hokt
  have hltr32 : r < 32 := by simpa [arm8Config] using hltr
  have hltt32 : t < 32 := by simpa [arm8Config] using hltt
  have hn64 : w.toNat < 64 := hwlt
  have hast := arm8Ast_shift_lsr r t w
  have st := arm8Start (.inst (.arith (.shift .lsr r t (.imm w)))) s1 s2 ms h
  have hb : bytesInMemoryHOL ms.pc (encodeBytes (.bitfieldMove true false w.toNat 63 t r))
      ms.mem s1.memDomain := by
    have hb' := st.bytes
    rw [arm8Enc, hast] at hb'
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
  have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
      (.bitfieldMove true false w.toNat 63 t r) :=
    arm8Next_bitfieldMove ms s1.memDomain true false w.toNat 63 t r 2 (by decide)
      hn64 (by decide) hltt32 hltr32 hb
  have hsrc := msReadReg_pc st hltt havt hnet31
  have hwrite : execInsn { ms with pc := ms.pc + 4 } (.bitfieldMove true false w.toNat 63 t r) =
      writeReg { ms with pc := ms.pc + 4 } r (wordShift .lsr (s1.regs t) w.toNat) := by
    rw [execInsn_bitfieldMove_lsr _ _ _ _ hn64, hsrc, wordShift]
  have hdec : decodeInsn32 (BitVec.setWidth 32 (BitVec.setWidth 64
      (fields [(1, 1), (2, 2), (6, 0b100110), (1, 1), (6, w.toNat), (6, 63),
        (5, t), (5, r)]))) = some (.bitfieldMove true false w.toNat 63 t r) := by
    simpa [decodeInsn] using
      (decode_encode_bitfieldMove true false w.toNat 63 t r 2 (by decide) hn64
        (by decide) hltt32 hltr32)
  have hsafe0 : StepSafe s1.memDomain ms :=
    stepSafe_of_encode ms s1.memDomain (.bitfieldMove true false w.toNat 63 t r) _ hb
      (encodeInsn_bitfieldMove true false w.toNat 63 t r 2 (by decide) hn64 (by decide))
      hdec (by rfl)
  have hupd := arithUpd_of_start (.inst (.arith (.shift .lsr r t (.imm w)))) s1 s2 ms h hast
  have hregs := arithUpd_shift_imm_regs s1 .lsr r t w
  obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
    arithUpdFacts _ s1 s2 r (wordShift .lsr (s1.regs t) w.toNat) hupd hregs
  have hfields := execWriteFields hne31 hwrite
  exact arithOneCase _ r _ _ s1 s2 ms h hnext hfields hs2pc hs2mem hs2dom hs2regs hsafe0

/-- The `asr` case for every amount: the lowered sign-filling bitfield move
writes the arithmetic shift right, which is the value `arithUpd` records.
Unlike `case_shift_imm_asr` this needs no `value.toNat < 32` hypothesis. -/
theorem case_shift_imm_asr_full (r t : Nat) (w : BitVec 64) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.shift .asr r t (.imm w)))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.arith (.shift .asr r t (.imm w)))) s1 s2 ms := by
  have hok := arithRegOkShiftImm .asr r t w s1 s2 ms h
  obtain ⟨⟨hokr, hokt⟩, hwlt⟩ := hok
  obtain ⟨hltr, havr, hne31⟩ := regOk_of_asm hokr
  obtain ⟨hltt, havt, hnet31⟩ := regOk_of_asm hokt
  have hltr32 : r < 32 := by simpa [arm8Config] using hltr
  have hltt32 : t < 32 := by simpa [arm8Config] using hltt
  have hn64 : w.toNat < 64 := hwlt
  have hast := arm8Ast_shift_asr r t w
  have st := arm8Start (.inst (.arith (.shift .asr r t (.imm w)))) s1 s2 ms h
  have hb : bytesInMemoryHOL ms.pc (encodeBytes (.bitfieldMove true true w.toNat 63 t r))
      ms.mem s1.memDomain := by
    have hb' := st.bytes
    rw [arm8Enc, hast] at hb'
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hb'
  have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 }
      (.bitfieldMove true true w.toNat 63 t r) :=
    arm8Next_bitfieldMove ms s1.memDomain true true w.toNat 63 t r 0 (by decide)
      hn64 (by decide) hltt32 hltr32 hb
  have hsrc := msReadReg_pc st hltt havt hnet31
  have hwrite : execInsn { ms with pc := ms.pc + 4 } (.bitfieldMove true true w.toNat 63 t r) =
      writeReg { ms with pc := ms.pc + 4 } r (wordShift .asr (s1.regs t) w.toNat) := by
    rw [execInsn_bitfieldMove_asr _ _ _ _ hn64, hsrc, wordShift]
  have hdec : decodeInsn32 (BitVec.setWidth 32 (BitVec.setWidth 64
      (fields [(1, 1), (2, 0), (6, 0b100110), (1, 1), (6, w.toNat), (6, 63),
        (5, t), (5, r)]))) = some (.bitfieldMove true true w.toNat 63 t r) := by
    simpa [decodeInsn] using
      (decode_encode_bitfieldMove true true w.toNat 63 t r 0 (by decide) hn64
        (by decide) hltt32 hltr32)
  have hsafe0 : StepSafe s1.memDomain ms :=
    stepSafe_of_encode ms s1.memDomain (.bitfieldMove true true w.toNat 63 t r) _ hb
      (encodeInsn_bitfieldMove true true w.toNat 63 t r 0 (by decide) hn64 (by decide))
      hdec (by rfl)
  have hupd := arithUpd_of_start (.inst (.arith (.shift .asr r t (.imm w)))) s1 s2 ms h hast
  have hregs := arithUpd_shift_imm_regs s1 .asr r t w
  obtain ⟨hs2pc, hs2mem, hs2dom, hs2regs⟩ :=
    arithUpdFacts _ s1 s2 r (wordShift .asr (s1.regs t) w.toNat) hupd hregs
  have hfields := execWriteFields hne31 hwrite
  exact arithOneCase _ r _ _ s1 s2 ms h hnext hfields hs2pc hs2mem hs2dom hs2regs hsafe0

/-! ## The immediate-shift case for all four shift kinds -/

/-- The whole `Shift sop destination source (Imm value)` case: split on the
shift kind and dispatch to the four unconditional per-kind cases. -/
theorem case_shift_imm (sop : Shift) (r t : Nat) (w : BitVec 64) (s1 s2 : AsmState 64)
    (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.arith (.shift sop r t (.imm w)))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.arith (.shift sop r t (.imm w)))) s1 s2 ms := by
  cases sop
  · exact case_shift_imm_lsl r t w s1 s2 ms h
  · exact case_shift_imm_lsr_full r t w s1 s2 ms h
  · exact case_shift_imm_asr_full r t w s1 s2 ms h
  · exact case_shift_imm_ror r t w s1 s2 ms h

end Flapjack.Compiler.Encoders.Arm8

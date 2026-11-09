module

public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.ShiftBitfieldMasks
public import Flapjack.HolRef

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# `BitfieldMove@64` case theorems for the `shift` immediate forms

The `.lsl`/`.lsr`/`.asr` immediate constructors of
`encoder_correct arm8TargetL3`, assembled from the `BitfieldMove` encode/
decode/run layer (`ShiftBitfield.lean`) and the mask identities
(`ShiftBitfieldMasks.lean`).
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The `.lsr` immediate constructor of `encoder_correct arm8TargetL3`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_shift_lsr_imm (destination source : Nat) (value : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.shift .lsr destination source (.imm value)))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.shift .lsr destination source (.imm value)))) s1 s2 ms := by
  have hs := h.1
  have hregok : (asmRegOkExact destination arm8ConfigL3 = true ∧
      asmRegOkExact source arm8ConfigL3 = true) ∧
      ((!(value == 0) || Flapjack.Shift.lsr == Flapjack.Shift.lsl) = true ∧
        value.toNat < 64) := by
    have hk := hs.2.2.2.2.2.2
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact, arm8ConfigL3,
      Bool.and_eq_true] using hk
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hregok.1.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hregok.1.2
  have hlt : value.toNat < 64 := hregok.2.2
  have hmasks := decodeBitMasks_lsr value.toNat hlt
  have hsw : BitVec.setWidth 6 value = BitVec.ofNat 6 value.toNat := by
    rw [BitVec.setWidth, dif_neg (by omega : ¬ 64 ≤ 6)]
  have hast : arm8Ast (.inst (.arith (.shift .lsr destination source (.imm value)))) =
      [.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))] := by
    have h63 : (63 : BitVec 6) = BitVec.ofNat 6 63 := by decide
    have hne : (Flapjack.Shift.lsr == Flapjack.Shift.asr) = false := by decide
    simp only [arm8Ast, h63, hne, hmasks]
    rfl
  have henc : arm8Enc (.inst (.arith (.shift .lsr destination source (.imm value)))) =
      arm8Encode (.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) := by
    rw [arm8Enc, hast]
    simp
  let w : BitVec 32 := arm8BitfieldWord 1 (BitVec.ofNat 2 2) (BitVec.ofNat 6 value.toNat)
    (BitVec.ofNat 6 63) (BitVec.ofNat 5 source) (BitVec.ofNat 5 destination)
  have hencw : Encode (.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) =
      MachineCode.ARM8 w :=
    arm8Encode_bitfieldMove true false (BitVec.ofNat 2 2) _ _ value.toNat 63 _ _
      (by decide) hlt (by norm_num) hmasks
  have hdec : Decode w = instruction.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination)) :=
    arm8Decode_bitfieldMove_2 _ _ value.toNat 63 _ _ hlt (by norm_num) hmasks
  let v : BitVec 64 := wordShift .lsr (s1.regs source) value.toNat
  refine arm8RegCaseOne _ destination v s1 s2 ms h (by omega) _ _ _ henc hencw hdec ?_ ?_
  · intro hreg
    have hX : X (TN := 64) (BitVec.ofNat 5 source) { ms with branch_hint := none } =
        s1.regs source := by
      rw [arm8X_of_valid _ hs31 hslt]
      exact hreg source ⟨hslt, hsav⟩
    rw [arm8Run_bitfieldMove, arm8WriteX_of_valid _ _ hd31 hdlt]
    simp [hX, v, holUpdate, wordShift, lsr_mask (s1.regs source) value.toNat hlt]
  · intro hreg p
    refine ⟨?_, fun x => ?_, ?_, fun k => ?_⟩
    · simp [asmUpd, instUpd, arithUpd, updPc]
    · simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
    · simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
    · simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc, v, wordShift,
        Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm]

/-- The `.asr` immediate constructor of `encoder_correct arm8TargetL3`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_shift_asr_imm (destination source : Nat) (value : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.shift .asr destination source (.imm value)))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.shift .asr destination source (.imm value)))) s1 s2 ms := by
  have hs := h.1
  have hregok : (asmRegOkExact destination arm8ConfigL3 = true ∧
      asmRegOkExact source arm8ConfigL3 = true) ∧
      ((!(value == 0) || Flapjack.Shift.asr == Flapjack.Shift.lsl) = true ∧
        value.toNat < 64) := by
    have hk := hs.2.2.2.2.2.2
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact, arm8ConfigL3,
      Bool.and_eq_true] using hk
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hregok.1.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hregok.1.2
  have hlt : value.toNat < 64 := hregok.2.2
  have hmasks := decodeBitMasks_lsr value.toNat hlt
  have hsw : BitVec.setWidth 6 value = BitVec.ofNat 6 value.toNat := by
    rw [BitVec.setWidth, dif_neg (by omega : ¬ 64 ≤ 6)]
  have hast : arm8Ast (.inst (.arith (.shift .asr destination source (.imm value)))) =
      [.Data (.«BitfieldMove@64» (1, true, true,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))] := by
    have h63 : (63 : BitVec 6) = BitVec.ofNat 6 63 := by decide
    have hne : (Flapjack.Shift.asr == Flapjack.Shift.asr) = true := by decide
    simp only [arm8Ast, h63, hne, hmasks]
    rfl
  have henc : arm8Enc (.inst (.arith (.shift .asr destination source (.imm value)))) =
      arm8Encode (.Data (.«BitfieldMove@64» (1, true, true,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) := by
    rw [arm8Enc, hast]
    simp
  let w : BitVec 32 := arm8BitfieldWord 1 (BitVec.ofNat 2 0) (BitVec.ofNat 6 value.toNat)
    (BitVec.ofNat 6 63) (BitVec.ofNat 5 source) (BitVec.ofNat 5 destination)
  have hencw : Encode (.Data (.«BitfieldMove@64» (1, true, true,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) =
      MachineCode.ARM8 w :=
    arm8Encode_bitfieldMove true true (BitVec.ofNat 2 0) _ _ value.toNat 63 _ _
      (by decide) hlt (by norm_num) hmasks
  have hdec : Decode w = instruction.Data (.«BitfieldMove@64» (1, true, true,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination)) :=
    arm8Decode_bitfieldMove_0 _ _ value.toNat 63 _ _ hlt (by norm_num) hmasks
  let v : BitVec 64 := wordShift .asr (s1.regs source) value.toNat
  refine arm8RegCaseOne _ destination v s1 s2 ms h (by omega) _ _ _ henc hencw hdec ?_ ?_
  · intro hreg
    have hX : X (TN := 64) (BitVec.ofNat 5 source) { ms with branch_hint := none } =
        s1.regs source := by
      rw [arm8X_of_valid _ hs31 hslt]
      exact hreg source ⟨hslt, hsav⟩
    rw [arm8Run_bitfieldMove, arm8WriteX_of_valid _ _ hd31 hdlt]
    simp [hX, v, holUpdate, wordShift]
    congr 1
    exact asr_mask (s1.regs source) value.toNat hlt
  · intro hreg p
    refine ⟨?_, fun x => ?_, ?_, fun k => ?_⟩
    · simp [asmUpd, instUpd, arithUpd, updPc]
    · simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
    · simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
    · simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc, v, wordShift,
        Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm]

/-- The `.lsl` immediate constructor of `encoder_correct arm8TargetL3`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_shift_lsl_imm (destination source : Nat) (value : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.shift .lsl destination source (.imm value)))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.shift .lsl destination source (.imm value)))) s1 s2 ms := by
  have hs := h.1
  have hregok : (asmRegOkExact destination arm8ConfigL3 = true ∧
      asmRegOkExact source arm8ConfigL3 = true) ∧
      ((!(value == 0) || Flapjack.Shift.lsl == Flapjack.Shift.lsl) = true ∧
        value.toNat < 64) := by
    have hk := hs.2.2.2.2.2.2
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact, arm8ConfigL3,
      Bool.and_eq_true] using hk
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hregok.1.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hregok.1.2
  have hlt : value.toNat < 64 := hregok.2.2
  have hs6 : (63 : BitVec 6) - BitVec.ofNat 6 value.toNat =
      BitVec.ofNat 6 ((63 - value.toNat) % 64) := by
    interval_cases value.toNat <;> decide
  have hr6 : -(BitVec.ofNat 6 value.toNat) =
      BitVec.ofNat 6 ((64 - value.toNat) % 64) := by
    interval_cases value.toNat <;> decide
  have hmasks := decodeBitMasks_lsl value.toNat hlt
  have hne : (Flapjack.Shift.lsl == Flapjack.Shift.asr) = false := by decide
  have hast : arm8Ast (.inst (.arith (.shift .lsl destination source (.imm value)))) =
      [.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64)
          (holRotate (holPadLeft false 64 (Ones ((63 - value.toNat) % 64 + 1))) ((64 - value.toNat) % 64)),
        BitVec.allOnes 64,
        (64 - value.toNat) % 64, (63 - value.toNat) % 64,
        BitVec.ofNat 5 source, BitVec.ofNat 5 destination))] := by
    simp only [arm8Ast, hs6, hr6, hmasks, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_mod]
    rfl
  have henc : arm8Enc (.inst (.arith (.shift .lsl destination source (.imm value)))) =
      arm8Encode (.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64)
          (holRotate (holPadLeft false 64 (Ones ((63 - value.toNat) % 64 + 1))) ((64 - value.toNat) % 64)),
        BitVec.allOnes 64, (64 - value.toNat) % 64, (63 - value.toNat) % 64,
        BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) := by
    rw [arm8Enc, hast]
    simp
  let w : BitVec 32 := arm8BitfieldWord 1 (BitVec.ofNat 2 2)
    (BitVec.ofNat 6 ((64 - value.toNat) % 64)) (BitVec.ofNat 6 ((63 - value.toNat) % 64))
    (BitVec.ofNat 5 source) (BitVec.ofNat 5 destination)
  have hencw : Encode (.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64)
          (holRotate (holPadLeft false 64 (Ones ((63 - value.toNat) % 64 + 1))) ((64 - value.toNat) % 64)),
        BitVec.allOnes 64, (64 - value.toNat) % 64, (63 - value.toNat) % 64,
        BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) = MachineCode.ARM8 w :=
    arm8Encode_bitfieldMove true false (BitVec.ofNat 2 2) _ _ ((64 - value.toNat) % 64)
      ((63 - value.toNat) % 64) _ _ (by decide) (by omega) (by omega) hmasks
  have hdec : Decode w = instruction.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64)
          (holRotate (holPadLeft false 64 (Ones ((63 - value.toNat) % 64 + 1))) ((64 - value.toNat) % 64)),
        BitVec.allOnes 64, (64 - value.toNat) % 64, (63 - value.toNat) % 64,
        BitVec.ofNat 5 source, BitVec.ofNat 5 destination)) :=
    arm8Decode_bitfieldMove_2 _ _ ((64 - value.toNat) % 64) ((63 - value.toNat) % 64) _ _
      (by omega) (by omega) hmasks
  let v : BitVec 64 := wordShift .lsl (s1.regs source) value.toNat
  refine arm8RegCaseOne _ destination v s1 s2 ms h (by omega) _ _ _ henc hencw hdec ?_ ?_
  · intro hreg
    have hX : X (TN := 64) (BitVec.ofNat 5 source) { ms with branch_hint := none } =
        s1.regs source := by
      rw [arm8X_of_valid _ hs31 hslt]
      exact hreg source ⟨hslt, hsav⟩
    rw [arm8Run_bitfieldMove, arm8WriteX_of_valid _ _ hd31 hdlt]
    simp [hX, v, holUpdate, wordShift]
    congr 1
    have hall : (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 := by decide
    rw [hall, BitVec.and_allOnes]
    have hm := lsl_mask (s1.regs source) value.toNat hlt
    rw [BitVec.allOnes_and] at hm
    rw [BitVec.and_comm ((s1.regs source).rotateRight (64 - value.toNat))]
    have hrot : (s1.regs source).rotateRight (64 - value.toNat) =
        (s1.regs source).rotateRight ((64 - value.toNat) % 64) := by
      simp [BitVec.rotateRight]
    rw [hrot]
    exact hm
  · intro hreg p
    refine ⟨?_, fun x => ?_, ?_, fun k => ?_⟩
    · simp [asmUpd, instUpd, arithUpd, updPc]
    · simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
    · simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
    · simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc, v, wordShift,
        Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm]

end Flapjack.Compiler.Encoders.Arm8.L3

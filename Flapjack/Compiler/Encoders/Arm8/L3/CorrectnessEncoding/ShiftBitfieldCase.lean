import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.ShiftBitfieldMasks

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
theorem arm8_encoder_correct_shift_lsr_imm (destination source : Nat) (value : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.shift .lsr destination source (.imm value)))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.shift .lsr destination source (.imm value)))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
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
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hmasks := decodeBitMasks_lsr value.toNat hlt
  have hbms : bytesInMemoryHOL ms.PC
      (arm8Enc (.inst (.arith (.shift .lsr destination source (.imm value))))) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
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
  have hlen : (arm8Enc (.inst (.arith (.shift .lsr destination source (.imm value))))).length = 4 := by
    rw [henc]; exact arm8Encode_length _
  let w : BitVec 32 := arm8BitfieldWord 1 (BitVec.ofNat 2 2) (BitVec.ofNat 6 value.toNat)
    (BitVec.ofNat 6 63) (BitVec.ofNat 5 source) (BitVec.ofNat 5 destination)
  have hencw : Encode (.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) =
      MachineCode.ARM8 w :=
    arm8Encode_bitfieldMove true false (BitVec.ofNat 2 2) _ _ value.toNat 63 _ _
      (by decide) hlt (by norm_num) hmasks
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have hdec : Decode w = instruction.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination)) :=
    arm8Decode_bitfieldMove_2 _ _ value.toNat 63 _ _ hlt (by norm_num) hmasks
  let v : BitVec 64 := wordShift .lsr (s1.regs source) value.toNat
  have hbr : (Run (instruction.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))
      { ms with branch_hint := none }).branch_hint = none := by
    rw [arm8Run_bitfieldMove, arm8WriteX_of_valid _ _ hd31 hdlt]
  have hexc : (Run (instruction.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))
      { ms with branch_hint := none }).exception = exception.NoException := by
    rw [arm8Run_bitfieldMove, arm8WriteX_of_valid _ _ hd31 hdlt]
    simpa using hexc0
  have hn := arm8Next_word ms w (instruction.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))
    hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hX : X (TN := 64) (BitVec.ofNat 5 source) { ms with branch_hint := none } =
      s1.regs source := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg source ⟨hslt, hsav⟩
  have hrun : Run (instruction.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))
      { ms with branch_hint := none } =
      { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 destination) v ms.REG } := by
    rw [arm8Run_bitfieldMove, arm8WriteX_of_valid _ _ hd31 hdlt]
    simp [hX, v, holUpdate, wordShift, lsr_mask (s1.regs source) value.toNat hlt]
  have hnext : arm8Next ms =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 destination) v ms.REG,
        PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  rw [hlen] at hupd
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd]; simp [asmUpd, instUpd, arithUpd, updPc]
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    intro x; rw [← hupd]; simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
  have hs2regs : ∀ k, s2.regs k = if k = destination then v else s1.regs k := by
    intro k
    rw [← hupd]
    simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc, v, wordShift,
      Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm]
  refine asmCaseOne (.arith (.shift .lsr destination source (.imm value))) destination v
    _ s1 s2 ms ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext ?_ ?_ ?_ ?_ ?_ hs2pc hs2mem hs2dom hs2regs
  · rfl
  · intro x; rfl
  · intro k hk hkne
    show (if (BitVec.ofNat 5 destination) = (BitVec.ofNat 5 k) then v
      else ms.REG (BitVec.ofNat 5 k)) = ms.REG (BitVec.ofNat 5 k)
    rw [if_neg]
    intro hh
    apply hkne
    have := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have hd32 : destination % 2 ^ 5 = destination := Nat.mod_eq_of_lt (by omega)
    have hk32 : k % 2 ^ 5 = k := Nat.mod_eq_of_lt (by omega)
    omega
  · show (if (BitVec.ofNat 5 destination) = (BitVec.ofNat 5 destination) then v
      else ms.REG (BitVec.ofNat 5 destination)) = v
    rw [if_pos rfl]
  · rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    have h4 : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
    have hal4 : holAligned 2 (ms.PC + 4) = true := by
      rw [(alignedAddSub 2 ms.PC 4 h4).1, halign]
    change holAligned 2 (ms.PC + 4) = true
    exact hal4


/-- The `.asr` immediate constructor of `encoder_correct arm8TargetL3`. -/
theorem arm8_encoder_correct_shift_asr_imm (destination source : Nat) (value : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.shift .asr destination source (.imm value)))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.shift .asr destination source (.imm value)))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
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
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hmasks := decodeBitMasks_lsr value.toNat hlt
  have hbms : bytesInMemoryHOL ms.PC
      (arm8Enc (.inst (.arith (.shift .asr destination source (.imm value))))) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
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
  have hlen : (arm8Enc (.inst (.arith (.shift .asr destination source (.imm value))))).length = 4 := by
    rw [henc]; exact arm8Encode_length _
  let w : BitVec 32 := arm8BitfieldWord 1 (BitVec.ofNat 2 0) (BitVec.ofNat 6 value.toNat)
    (BitVec.ofNat 6 63) (BitVec.ofNat 5 source) (BitVec.ofNat 5 destination)
  have hencw : Encode (.Data (.«BitfieldMove@64» (1, true, true,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) =
      MachineCode.ARM8 w :=
    arm8Encode_bitfieldMove true true (BitVec.ofNat 2 0) _ _ value.toNat 63 _ _
      (by decide) hlt (by norm_num) hmasks
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have hdec : Decode w = instruction.Data (.«BitfieldMove@64» (1, true, true,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination)) :=
    arm8Decode_bitfieldMove_0 _ _ value.toNat 63 _ _ hlt (by norm_num) hmasks
  let v : BitVec 64 := wordShift .asr (s1.regs source) value.toNat
  have hbr : (Run (instruction.Data (.«BitfieldMove@64» (1, true, true,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))
      { ms with branch_hint := none }).branch_hint = none := by
    rw [arm8Run_bitfieldMove, arm8WriteX_of_valid _ _ hd31 hdlt]
  have hexc : (Run (instruction.Data (.«BitfieldMove@64» (1, true, true,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))
      { ms with branch_hint := none }).exception = exception.NoException := by
    rw [arm8Run_bitfieldMove, arm8WriteX_of_valid _ _ hd31 hdlt]
    simpa using hexc0
  have hn := arm8Next_word ms w (instruction.Data (.«BitfieldMove@64» (1, true, true,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))
    hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hX : X (TN := 64) (BitVec.ofNat 5 source) { ms with branch_hint := none } =
      s1.regs source := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg source ⟨hslt, hsav⟩
  have hrun : Run (instruction.Data (.«BitfieldMove@64» (1, true, true,
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) value.toNat),
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - value.toNat + 1))),
        value.toNat, 63, BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))
      { ms with branch_hint := none } =
      { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 destination) v ms.REG } := by
    rw [arm8Run_bitfieldMove, arm8WriteX_of_valid _ _ hd31 hdlt]
    simp [hX, v, holUpdate, wordShift]
    congr 1
    exact asr_mask (s1.regs source) value.toNat hlt
  have hnext : arm8Next ms =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 destination) v ms.REG,
        PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  rw [hlen] at hupd
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd]; simp [asmUpd, instUpd, arithUpd, updPc]
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    intro x; rw [← hupd]; simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
  have hs2regs : ∀ k, s2.regs k = if k = destination then v else s1.regs k := by
    intro k
    rw [← hupd]
    simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc, v, wordShift,
      Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm]
  refine asmCaseOne (.arith (.shift .asr destination source (.imm value))) destination v
    _ s1 s2 ms ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext ?_ ?_ ?_ ?_ ?_ hs2pc hs2mem hs2dom hs2regs
  · rfl
  · intro x; rfl
  · intro k hk hkne
    show (if (BitVec.ofNat 5 destination) = (BitVec.ofNat 5 k) then v
      else ms.REG (BitVec.ofNat 5 k)) = ms.REG (BitVec.ofNat 5 k)
    rw [if_neg]
    intro hh
    apply hkne
    have := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have hd32 : destination % 2 ^ 5 = destination := Nat.mod_eq_of_lt (by omega)
    have hk32 : k % 2 ^ 5 = k := Nat.mod_eq_of_lt (by omega)
    omega
  · show (if (BitVec.ofNat 5 destination) = (BitVec.ofNat 5 destination) then v
      else ms.REG (BitVec.ofNat 5 destination)) = v
    rw [if_pos rfl]
  · rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    have h4 : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
    have hal4 : holAligned 2 (ms.PC + 4) = true := by
      rw [(alignedAddSub 2 ms.PC 4 h4).1, halign]
    change holAligned 2 (ms.PC + 4) = true
    exact hal4

/-- The `.lsl` immediate constructor of `encoder_correct arm8TargetL3`. -/
theorem arm8_encoder_correct_shift_lsl_imm (destination source : Nat) (value : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.shift .lsl destination source (.imm value)))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.shift .lsl destination source (.imm value)))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
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
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hs6 : (63 : BitVec 6) - BitVec.ofNat 6 value.toNat =
      BitVec.ofNat 6 ((63 - value.toNat) % 64) := by
    interval_cases value.toNat <;> decide
  have hr6 : -(BitVec.ofNat 6 value.toNat) =
      BitVec.ofNat 6 ((64 - value.toNat) % 64) := by
    interval_cases value.toNat <;> decide
  have hmasks := decodeBitMasks_lsl value.toNat hlt
  have hbms : bytesInMemoryHOL ms.PC
      (arm8Enc (.inst (.arith (.shift .lsl destination source (.imm value))))) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
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
  have hlen : (arm8Enc (.inst (.arith (.shift .lsl destination source (.imm value))))).length = 4 := by
    rw [henc]; exact arm8Encode_length _
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
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have hdec : Decode w = instruction.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64)
          (holRotate (holPadLeft false 64 (Ones ((63 - value.toNat) % 64 + 1))) ((64 - value.toNat) % 64)),
        BitVec.allOnes 64, (64 - value.toNat) % 64, (63 - value.toNat) % 64,
        BitVec.ofNat 5 source, BitVec.ofNat 5 destination)) :=
    arm8Decode_bitfieldMove_2 _ _ ((64 - value.toNat) % 64) ((63 - value.toNat) % 64) _ _
      (by omega) (by omega) hmasks
  let v : BitVec 64 := wordShift .lsl (s1.regs source) value.toNat
  have hbr : (Run (instruction.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64)
          (holRotate (holPadLeft false 64 (Ones ((63 - value.toNat) % 64 + 1))) ((64 - value.toNat) % 64)),
        BitVec.allOnes 64, (64 - value.toNat) % 64, (63 - value.toNat) % 64,
        BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))
      { ms with branch_hint := none }).branch_hint = none := by
    rw [arm8Run_bitfieldMove, arm8WriteX_of_valid _ _ hd31 hdlt]
  have hexc : (Run (instruction.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64)
          (holRotate (holPadLeft false 64 (Ones ((63 - value.toNat) % 64 + 1))) ((64 - value.toNat) % 64)),
        BitVec.allOnes 64, (64 - value.toNat) % 64, (63 - value.toNat) % 64,
        BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))
      { ms with branch_hint := none }).exception = exception.NoException := by
    rw [arm8Run_bitfieldMove, arm8WriteX_of_valid _ _ hd31 hdlt]
    simpa using hexc0
  have hn := arm8Next_word ms w (instruction.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64)
          (holRotate (holPadLeft false 64 (Ones ((63 - value.toNat) % 64 + 1))) ((64 - value.toNat) % 64)),
        BitVec.allOnes 64, (64 - value.toNat) % 64, (63 - value.toNat) % 64,
        BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))
    hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hX : X (TN := 64) (BitVec.ofNat 5 source) { ms with branch_hint := none } =
      s1.regs source := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg source ⟨hslt, hsav⟩
  have hrun : Run (instruction.Data (.«BitfieldMove@64» (1, true, false,
        Replicate (TN := 64)
          (holRotate (holPadLeft false 64 (Ones ((63 - value.toNat) % 64 + 1))) ((64 - value.toNat) % 64)),
        BitVec.allOnes 64, (64 - value.toNat) % 64, (63 - value.toNat) % 64,
        BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))
      { ms with branch_hint := none } =
      { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 destination) v ms.REG } := by
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
  have hnext : arm8Next ms =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 destination) v ms.REG,
        PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  rw [hlen] at hupd
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd]; simp [asmUpd, instUpd, arithUpd, updPc]
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    intro x; rw [← hupd]; simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
  have hs2regs : ∀ k, s2.regs k = if k = destination then v else s1.regs k := by
    intro k
    rw [← hupd]
    simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc, v, wordShift,
      Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm]
  refine asmCaseOne (.arith (.shift .lsl destination source (.imm value))) destination v
    _ s1 s2 ms ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext ?_ ?_ ?_ ?_ ?_ hs2pc hs2mem hs2dom hs2regs
  · rfl
  · intro x; rfl
  · intro k hk hkne
    show (if (BitVec.ofNat 5 destination) = (BitVec.ofNat 5 k) then v
      else ms.REG (BitVec.ofNat 5 k)) = ms.REG (BitVec.ofNat 5 k)
    rw [if_neg]
    intro hh
    apply hkne
    have := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have hd32 : destination % 2 ^ 5 = destination := Nat.mod_eq_of_lt (by omega)
    have hk32 : k % 2 ^ 5 = k := Nat.mod_eq_of_lt (by omega)
    omega
  · show (if (BitVec.ofNat 5 destination) = (BitVec.ofNat 5 destination) then v
      else ms.REG (BitVec.ofNat 5 destination)) = v
    rw [if_pos rfl]
  · rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    have h4 : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
    have hal4 : holAligned 2 (ms.PC + 4) = true := by
      rw [(alignedAddSub 2 ms.PC 4 h4).1, halign]
    change holAligned 2 (ms.PC + 4) = true
    exact hal4

end Flapjack.Compiler.Encoders.Arm8.L3

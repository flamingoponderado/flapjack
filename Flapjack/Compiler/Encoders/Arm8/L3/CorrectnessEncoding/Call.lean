import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Branch

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# The `Call` constructor of `encoder_correct arm8TargetL3`

`arm8_ast` lowers `Call a` to the single `BranchImmediate (a, BranchType_CALL)`
instruction.  This module records that instruction's word, its `Encode`/`Decode`
inverse, its `Run` semantics at exception level zero (which also writes the
return address `PC + 4` to the link register), and the `Call` case of the L3
`encoder_correct` port.

The word differs from the `Jump` word only in bit 31, the `CALL` bit.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The word emitted for `BranchImmediate` with branch type `CALL`: HOL's
`e_branch` term `1 ++ 00101 ++ imm26`. -/
def arm8CallWord (imm26 : BitVec 26) : BitVec 32 :=
  BitVec.setWidth 32 (holV2w 1 [true] ++ BitVec.setWidth 31 ((BitVec.ofNat 5 5) ++ imm26))

/-- Bits 0..25 of the call word are the branch immediate. -/
theorem arm8CallWord_getLsbD_low (imm26 : BitVec 26) (i : Nat) (hi : i < 26) :
    (arm8CallWord imm26).getLsbD i = imm26.getLsbD i := by
  unfold arm8CallWord
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat]
  simp [hi, show i < 31 by omega, show i < 32 by omega]

/-- Every bit of the call word: the low 26 bits are the branch immediate, bits
26 and 28 carry the `00101` opcode, bit 31 is the `CALL` bit, and the rest are
zero. -/
theorem arm8CallWord_getLsbD (imm26 : BitVec 26) (i : Nat) :
    (arm8CallWord imm26).getLsbD i =
      if i < 26 then imm26.getLsbD i
      else if i = 26 ∨ i = 28 ∨ i = 31 then true else false := by
  unfold arm8CallWord
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat]
  by_cases h : i < 26
  · have h31 : i < 31 := by omega
    have h32 : i < 32 := by omega
    simp [h, h31, h32]
  · by_cases h2 : i = 26 ∨ i = 28 ∨ i = 31
    · rcases h2 with rfl | rfl | rfl <;> (simp; try decide)
    · by_cases h3 : i < 32
      · have hb : i = 27 ∨ i = 29 ∨ i = 30 := by omega
        rcases hb with rfl | rfl | rfl <;> (simp; try decide)
      · have h31 : ¬ i < 31 := by omega
        have hn26 : i ≠ 26 := by omega
        have hn28 : i ≠ 28 := by omega
        have hn31 : i ≠ 31 := by omega
        simp [h, h3, h31, hn26, hn28, hn31]

/-- Bit 26 of the call word (lowest bit of the `00101` opcode). -/
theorem arm8CallWord_bit26 (imm26 : BitVec 26) :
    (arm8CallWord imm26).getLsbD 26 = true := by
  rw [arm8CallWord_getLsbD]
  simp

/-- Bit 27 of the call word. -/
theorem arm8CallWord_bit27 (imm26 : BitVec 26) :
    (arm8CallWord imm26).getLsbD 27 = false := by
  rw [arm8CallWord_getLsbD]
  simp

/-- Bit 28 of the call word. -/
theorem arm8CallWord_bit28 (imm26 : BitVec 26) :
    (arm8CallWord imm26).getLsbD 28 = true := by
  rw [arm8CallWord_getLsbD]
  simp

/-- Bit 29 of the call word. -/
theorem arm8CallWord_bit29 (imm26 : BitVec 26) :
    (arm8CallWord imm26).getLsbD 29 = false := by
  rw [arm8CallWord_getLsbD]
  simp

/-- Bit 30 of the call word. -/
theorem arm8CallWord_bit30 (imm26 : BitVec 26) :
    (arm8CallWord imm26).getLsbD 30 = false := by
  rw [arm8CallWord_getLsbD]
  simp

/-- Bit 31 of the call word: the `CALL` bit is set. -/
theorem arm8CallWord_bit31 (imm26 : BitVec 26) :
    (arm8CallWord imm26).getLsbD 31 = true := by
  rw [arm8CallWord_getLsbD]
  simp

/-- The branch immediate reassembles from the call word's low 26 bits. -/
theorem arm8CallWord_imm26 (imm26 : BitVec 26) :
    holV2w 26 [(arm8CallWord imm26).getLsbD 25, (arm8CallWord imm26).getLsbD 24,
      (arm8CallWord imm26).getLsbD 23, (arm8CallWord imm26).getLsbD 22,
      (arm8CallWord imm26).getLsbD 21, (arm8CallWord imm26).getLsbD 20,
      (arm8CallWord imm26).getLsbD 19, (arm8CallWord imm26).getLsbD 18,
      (arm8CallWord imm26).getLsbD 17, (arm8CallWord imm26).getLsbD 16,
      (arm8CallWord imm26).getLsbD 15, (arm8CallWord imm26).getLsbD 14,
      (arm8CallWord imm26).getLsbD 13, (arm8CallWord imm26).getLsbD 12,
      (arm8CallWord imm26).getLsbD 11, (arm8CallWord imm26).getLsbD 10,
      (arm8CallWord imm26).getLsbD 9, (arm8CallWord imm26).getLsbD 8,
      (arm8CallWord imm26).getLsbD 7, (arm8CallWord imm26).getLsbD 6,
      (arm8CallWord imm26).getLsbD 5, (arm8CallWord imm26).getLsbD 4,
      (arm8CallWord imm26).getLsbD 3, (arm8CallWord imm26).getLsbD 2,
      (arm8CallWord imm26).getLsbD 1, (arm8CallWord imm26).getLsbD 0] = imm26 := by
  have h : ([(arm8CallWord imm26).getLsbD 25, (arm8CallWord imm26).getLsbD 24,
      (arm8CallWord imm26).getLsbD 23, (arm8CallWord imm26).getLsbD 22,
      (arm8CallWord imm26).getLsbD 21, (arm8CallWord imm26).getLsbD 20,
      (arm8CallWord imm26).getLsbD 19, (arm8CallWord imm26).getLsbD 18,
      (arm8CallWord imm26).getLsbD 17, (arm8CallWord imm26).getLsbD 16,
      (arm8CallWord imm26).getLsbD 15, (arm8CallWord imm26).getLsbD 14,
      (arm8CallWord imm26).getLsbD 13, (arm8CallWord imm26).getLsbD 12,
      (arm8CallWord imm26).getLsbD 11, (arm8CallWord imm26).getLsbD 10,
      (arm8CallWord imm26).getLsbD 9, (arm8CallWord imm26).getLsbD 8,
      (arm8CallWord imm26).getLsbD 7, (arm8CallWord imm26).getLsbD 6,
      (arm8CallWord imm26).getLsbD 5, (arm8CallWord imm26).getLsbD 4,
      (arm8CallWord imm26).getLsbD 3, (arm8CallWord imm26).getLsbD 2,
      (arm8CallWord imm26).getLsbD 1, (arm8CallWord imm26).getLsbD 0] : List Bool) =
      holW2v (BitVec.setWidth 26 (arm8CallWord imm26)) := by
    rw [show holW2v (BitVec.setWidth 26 (arm8CallWord imm26)) =
      [(BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 25,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 24,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 23,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 22,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 21,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 20,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 19,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 18,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 17,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 16,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 15,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 14,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 13,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 12,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 11,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 10,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 9,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 8,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 7,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 6,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 5,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 4,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 3,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 2,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 1,
       (BitVec.setWidth 26 (arm8CallWord imm26)).getLsbD 0] from rfl]
    simp
  rw [h, holV2w_holW2v]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, arm8CallWord_getLsbD]
  simp [hi]

/-- `Encode` of a `CALL`-typed `BranchImmediate` in the signed 28-bit range is
the call word. -/
theorem arm8Encode_branchImmediate_call (imm : BitVec 64)
    (h : BitVec.signExtend 64 (BitVec.setWidth 28
      (holWordExtract 26 27 2 imm ++ BitVec.ofNat 2 0)) = imm) :
    Encode (.Branch (.BranchImmediate (imm, .BranchType_CALL))) =
      MachineCode.ARM8 (arm8CallWord (holWordExtract 26 27 2 imm)) := by
  have hc : (imm == BitVec.signExtend 64 (BitVec.setWidth 28
      (holWordExtract 26 27 2 imm ++ BitVec.ofNat 2 0))) = true := by
    rw [h]
    simp
  have hb : (BranchType.BranchType_CALL == BranchType.BranchType_CALL) = true := rfl
  simp only [Encode, e_branch, arm8CallWord]
  rw [hc]
  simp only [hb, Bool.true_and]
  simp [holV2w_one_true]

/-- The rendered `Decode` inverts the call word. -/
theorem arm8Decode_branchImmediate_call (imm26 : BitVec 26) :
    Decode (arm8CallWord imm26) =
      .Branch (.BranchImmediate
        (BitVec.signExtend 64 (BitVec.setWidth 28 (imm26 ++ BitVec.ofNat 2 0)),
          .BranchType_CALL)) := by
  simp only [Decode, boolify32, arm8CallWord_bit31, arm8CallWord_bit30,
    arm8CallWord_bit29, arm8CallWord_bit28, arm8CallWord_bit27,
    arm8CallWord_bit26, holV2w_one_true,
    Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.and_true,
    Bool.and_false, Bool.false_eq_true, ite_true, ite_false]
  rw [arm8CallWord_imm26 imm26]
  simp

/-- `Call` lowers to the single `BranchImmediate` instruction with branch type
`CALL`. -/
theorem arm8Ast_call (target : BitVec 64) :
    arm8Ast (.call target) =
      [.Branch (.BranchImmediate (target, .BranchType_CALL))] := rfl

/-- The four encoded bytes of the `CALL`-typed `BranchImmediate` instruction. -/
theorem arm8EncodeBytes_branchImmediate_call (imm : BitVec 64)
    (h : BitVec.signExtend 64 (BitVec.setWidth 28
      (holWordExtract 26 27 2 imm ++ BitVec.ofNat 2 0)) = imm) :
    arm8Encode (.Branch (.BranchImmediate (imm, .BranchType_CALL))) =
      [BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 imm) >>> 0).toNat),
       BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 imm) >>> 8).toNat),
       BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 imm) >>> 16).toNat),
       BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 imm) >>> 24).toNat)] := by
  rw [arm8Encode, arm8Encode_branchImmediate_call imm h]

/-- The encoded bytes of the `Call` lowering. -/
theorem arm8Enc_call (target : BitVec 64) :
    arm8Enc (.call target) =
      arm8Encode (.Branch (.BranchImmediate (target, .BranchType_CALL))) := by
  simp [arm8Enc, arm8Ast_call]

/-- The `Call` lowering encodes to four bytes. -/
theorem arm8Enc_call_length (target : BitVec 64) :
    (arm8Enc (.call target)).length = 4 := by
  simp [arm8Enc, arm8Ast_call, arm8Encode_length]

/-- `Run` of a `CALL`-typed `BranchImmediate` at exception level zero, with
`TBI0`/`TBI1` clear: the return address `PC + 4` goes to the link register, the
branch hint is set, and `PC` moves to `PC + offset`. -/
theorem arm8Run_branchImmediate_call (l : BitVec 64) (st : arm8_state)
    (hel : st.PSTATE.EL = (0 : BitVec 2))
    (htbi1 : st.TCR_EL1.TBI1 = false) (htbi0 : st.TCR_EL1.TBI0 = false) :
    Run (.Branch (.BranchImmediate (l, .BranchType_CALL))) st =
      { st with
        REG := holUpdate (30 : BitVec 5) (st.PC + 4) st.REG,
        branch_hint := some .BranchType_CALL,
        PC := st.PC + l } := by
  simp [Run, «dfn'BranchImmediate», BranchTo, Hint_Branch, «write'X», hel, htbi1, htbi0]

/-- One `NextStateARM8` step on the emitted `CALL` branch word writes the
return address to the link register, sets the branch hint and moves `PC` to
`PC + offset`. -/
theorem arm8Next_branchImmediate_call (ms : arm8_state) (l : BitVec 64)
    (hround : BitVec.signExtend 64 (BitVec.setWidth 28
      (holWordExtract 26 27 2 l ++ BitVec.ofNat 2 0)) = l)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC =
      BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 l) >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) =
      BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 l) >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) =
      BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 l) >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) =
      BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 l) >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (htbi1 : ms.TCR_EL1.TBI1 = false) (htbi0 : ms.TCR_EL1.TBI0 = false) :
    NextStateARM8 ms =
      some { ms with
        REG := holUpdate (30 : BitVec 5) (ms.PC + 4) ms.REG,
        branch_hint := some .BranchType_CALL,
        PC := ms.PC + l } := by
  let i : instruction := .Branch (.BranchImmediate (l, .BranchType_CALL))
  have hdec : Decode (arm8CallWord (holWordExtract 26 27 2 l)) = i := by
    dsimp only [i]
    rw [arm8Decode_branchImmediate_call, hround]
  have hrun : Run i { ms with branch_hint := none } =
      { ms with
        REG := holUpdate (30 : BitVec 5) (ms.PC + 4) ms.REG,
        branch_hint := some .BranchType_CALL,
        PC := ms.PC + l } := by
    dsimp only [i]
    exact arm8Run_branchImmediate_call l { ms with branch_hint := none }
      (by simpa using hel) (by simpa using htbi1) (by simpa using htbi0)
  have hfetch : Fetch { ms with branch_hint := none } =
      (arm8CallWord (holWordExtract 26 27 2 l), { ms with branch_hint := none }) :=
    arm8Fetch_word { ms with branch_hint := none } _ h0 h1 h2 h3 hal he0 hel
  simp only [NextStateARM8, Next]
  rw [hfetch]
  simp only [hdec]
  rw [hrun]
  simp [hexc0]

/-- `arm8Next` on the emitted `CALL` branch word. -/
theorem arm8Next_branchImmediate_call' (ms : arm8_state) (l : BitVec 64)
    (hround : BitVec.signExtend 64 (BitVec.setWidth 28
      (holWordExtract 26 27 2 l ++ BitVec.ofNat 2 0)) = l)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC =
      BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 l) >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) =
      BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 l) >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) =
      BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 l) >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) =
      BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 l) >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (htbi1 : ms.TCR_EL1.TBI1 = false) (htbi0 : ms.TCR_EL1.TBI0 = false) :
    arm8Next ms =
      { ms with
        REG := holUpdate (30 : BitVec 5) (ms.PC + 4) ms.REG,
        branch_hint := some .BranchType_CALL,
        PC := ms.PC + l } := by
  unfold arm8Next
  rw [arm8Next_branchImmediate_call ms l hround hexc0 h0 h1 h2 h3 hal he0 hel htbi1 htbi0]
  rfl

/-- The `Call` constructor of `encoder_correct arm8TargetL3`: the single
`BranchImmediate` instruction writes the return address to the link register
and moves `PC` to `PC + target`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_call (target : BitVec 64) (s1 s2 : AsmState 64)
    (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.call target) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.call target) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change arm8Ok ms = true at hok
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  obtain ⟨hlo, hhi, hmod⟩ := arm8JumpOk_of_asm target hs.2.2.2.2.2.2
  have hround := arm8BranchRoundtrip target hlo hhi hmod
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := (arm8Ok_iff ms).mp hok
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hdom := bytesInMemoryHOL_domain hs.1
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.call target)) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hs.1, fun n hn => (hmem _ (hdom n hn)).symm⟩
  have hlen : (arm8Enc (.call target)).length = 4 := arm8Enc_call_length target
  have henc : arm8Enc (.call target) =
      [BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 target) >>> 0).toNat),
       BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 target) >>> 8).toNat),
       BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 target) >>> 16).toNat),
       BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 target) >>> 24).toNat)] := by
    rw [arm8Enc_call, arm8EncodeBytes_branchImmediate_call target hround]
  have hb0 : ms.MEM ms.PC =
      BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 target) >>> 0).toNat) := by
    have := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; norm_num)
    rw [henc] at this
    simpa using this
  have hb1 : ms.MEM (ms.PC + 1) =
      BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 target) >>> 8).toNat) := by
    have := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; norm_num)
    rw [henc] at this
    simpa using this
  have hb2 : ms.MEM (ms.PC + 2) =
      BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 target) >>> 16).toNat) := by
    have := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; norm_num)
    rw [henc] at this
    simpa using this
  have hb3 : ms.MEM (ms.PC + 3) =
      BitVec.ofNat 8 ((arm8CallWord (holWordExtract 26 27 2 target) >>> 24).toNat) := by
    have := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; norm_num)
    rw [henc] at this
    simpa using this
  have hn := arm8Next_branchImmediate_call' ms target hround hexc0 hb0 hb1 hb2 hb3 hal
    he0 hel htbi1 htbi0
  have hlr : s1.lr = 30 := hs.2.1
  have hs2 : s2 = updPc (s1.pc + target) (updReg 30 (s1.pc + BitVec.ofNat 64 4) s1) := by
    have hupd := hs.2.2.2.2.1
    simp only [arm8ConfigL3] at hupd
    rw [hlen] at hupd
    rw [← hupd]
    simp [asmUpd, jumpToOffset, updPc, updReg, hlr]
  have hs2dom : s2.memDomain = s1.memDomain := by rw [hs2]; rfl
  have hal2 : holAligned 2 (ms.PC + target) = true := by
    have ht : holAligned 2 target = true := by
      rw [holAligned_iff]
      norm_num
      exact hmod
    rw [(alignedAddSub 2 ms.PC target ht).1, halign]
  have hokPost : arm8Ok { ms with
      REG := holUpdate (30 : BitVec 5) (ms.PC + 4) ms.REG,
      branch_hint := some .BranchType_CALL,
      PC := ms.PC + target } = true := by
    simp [arm8Ok, hel, he0, hsa0, htbi1, htbi0, hexc0]
    exact hal2
  have hq : targetStateRel arm8TargetL3 s2
      { ms with
        REG := holUpdate (30 : BitVec 5) (ms.PC + 4) ms.REG,
        branch_hint := some .BranchType_CALL,
        PC := ms.PC + target } := by
    refine ⟨hokPost, ?_, ?_, ?_, ?_⟩
    · simp only [arm8TargetL3_getPc]
      rw [hs2, hpc]
      simp [updPc, updReg]
    · intro a ha
      simp only [arm8TargetL3_getByte]
      have ha' : s1.memDomain a := by rw [← hs2dom]; exact ha
      rw [hs2]
      exact hmem a ha'
    · intro k hk
      simp only [arm8TargetL3_getReg]
      rw [hs2]
      simp only [updPc]
      by_cases hk30 : k = 30
      · subst hk30
        have h1 : holUpdate (30 : BitVec 5) (ms.PC + 4) ms.REG
            (BitVec.ofNat 5 30) = ms.PC + 4 := by
          simp [holUpdate, Flapjack.RiscV.L3.holUpdate]
        have h2 : (updReg 30 (s1.pc + BitVec.ofNat 64 4) s1).regs 30 =
            s1.pc + BitVec.ofNat 64 4 := by
          simp [updReg]
        rw [h1, h2, hpc]
        simp
      · have hk32 : k < 32 := by simpa [arm8ConfigL3] using hk.1
        have hne : (30 : BitVec 5) ≠ BitVec.ofNat 5 k := by
          intro hh
          have hh' : BitVec.ofNat 5 30 = BitVec.ofNat 5 k := hh
          exact hk30 ((arm8Reg_eq (by norm_num) hk32).mp hh').symm
        have h1 : holUpdate (30 : BitVec 5) (ms.PC + 4) ms.REG
            (BitVec.ofNat 5 k) = ms.REG (BitVec.ofNat 5 k) := by
          simp only [holUpdate, Flapjack.RiscV.L3.holUpdate]
          rw [ite_eq_right hne]
        have h2 : (updReg 30 (s1.pc + BitVec.ofNat 64 4) s1).regs k = s1.regs k := by
          simp only [updReg]
          rw [ite_eq_right hk30]
        rw [h1, h2]
        exact hreg k hk
    · intro k hk
      simp [arm8ConfigL3] at hk
  refine ⟨0, ?_⟩
  intro env henv
  constructor
  · change targetStateRel arm8TargetL3 s2 (env 0 (arm8Next ms))
    rw [hn]
    have hagree : Arm8L3Agree s2.memDomain
        (env 0 { ms with
          REG := holUpdate (30 : BitVec 5) (ms.PC + 4) ms.REG,
          branch_hint := some .BranchType_CALL,
          PC := ms.PC + target })
        { ms with
          REG := holUpdate (30 : BitVec 5) (ms.PC + 4) ms.REG,
          branch_hint := some .BranchType_CALL,
          PC := ms.PC + target } := by
      rw [← arm8Proj_eq_iff]
      have hh := henv 0 { ms with
        REG := holUpdate (30 : BitVec 5) (ms.PC + 4) ms.REG,
        branch_hint := some .BranchType_CALL,
        PC := ms.PC + target }
      rw [hs2dom]
      exact hh
    exact targetStateRel_congr hagree hq
  · refine ⟨fun x _ => ?_, trivial⟩
    rw [hn]

end Flapjack.Compiler.Encoders.Arm8.L3

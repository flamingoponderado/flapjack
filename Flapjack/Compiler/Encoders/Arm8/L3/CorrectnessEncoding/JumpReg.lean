module

public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Branch

@[expose] public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# The `JumpReg` constructor of `encoder_correct arm8TargetL3`

`arm8_ast` lowers `JumpReg r` to the single `BranchRegister (r, BranchType_JMP)`
instruction.  This module records that instruction's word, its `Encode`/`Decode`
inverse, its `Run` semantics at exception level zero, and the `JumpReg` case of
the L3 `encoder_correct` port.

The target is the register's value, so the case also needs the alignment
assertion that `asm_step`'s `~s2.failed` premise guarantees.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The word emitted for `BranchRegister` with a `JMP` branch type: HOL's
`e_branch` term `428 ++ opc ++ 1984 ++ Rn ++ 0`, with `opc = 0`. -/
def arm8JumpRegWord (rn : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((BitVec.ofNat 9 428) ++
    BitVec.setWidth 23 ((BitVec.ofNat 2 0) ++
      BitVec.setWidth 21 ((BitVec.ofNat 11 1984) ++
        BitVec.setWidth 10 (rn ++ BitVec.ofNat 5 0))))

/-- Every bit of the `JMP` branch-register word. -/
theorem arm8JumpRegWord_getLsbD (rn : BitVec 5) (i : Nat) :
    (arm8JumpRegWord rn).getLsbD i =
      if i < 5 then false
      else if i < 10 then rn.getLsbD (i - 5)
      else if i < 21 then (BitVec.ofNat 11 1984).getLsbD (i - 10)
      else if i < 23 then false
      else (BitVec.ofNat 9 428).getLsbD (i - 23) := by
  unfold arm8JumpRegWord
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat]
  by_cases h32 : i < 32
  · interval_cases i <;> simp
  · have h5 : ¬ i < 5 := by omega
    have h10 : ¬ i < 10 := by omega
    have h21 : ¬ i < 21 := by omega
    have h23 : ¬ i < 23 := by omega
    have h9 : ¬ i - 23 < 9 := by omega
    simp [h32, h5, h10, h21, h23, h9]

/-- Bits 4:0 of the branch-register word are zero. -/
theorem arm8JumpRegWord_low (rn : BitVec 5) (i : Nat) (hi : i < 5) :
    (arm8JumpRegWord rn).getLsbD i = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp [hi]

/-- Bits 9:5 of the branch-register word are the register number. -/
theorem arm8JumpRegWord_rn (rn : BitVec 5) (i : Nat) (h5 : 5 ≤ i) (hi : i < 10) :
    (arm8JumpRegWord rn).getLsbD i = rn.getLsbD (i - 5) := by
  rw [arm8JumpRegWord_getLsbD]
  simp [show ¬ i < 5 by omega, hi]

/-- Bits 20:10 of the branch-register word are `1984`. -/
theorem arm8JumpRegWord_mid (rn : BitVec 5) (i : Nat) (h10 : 10 ≤ i) (hi : i < 21) :
    (arm8JumpRegWord rn).getLsbD i = (BitVec.ofNat 11 1984).getLsbD (i - 10) := by
  rw [arm8JumpRegWord_getLsbD]
  simp [show ¬ i < 5 by omega, show ¬ i < 10 by omega, hi]

/-- Bits 22:21 of the branch-register word are zero. -/
theorem arm8JumpRegWord_opc (rn : BitVec 5) (i : Nat) (h21 : 21 ≤ i) (hi : i < 23) :
    (arm8JumpRegWord rn).getLsbD i = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp [show ¬ i < 5 by omega, show ¬ i < 10 by omega, show ¬ i < 21 by omega, hi]

/-- Bits 31:23 of the branch-register word are `428`. -/
theorem arm8JumpRegWord_high (rn : BitVec 5) (i : Nat) (h23 : 23 ≤ i) (hi : i < 32) :
    (arm8JumpRegWord rn).getLsbD i = (BitVec.ofNat 9 428).getLsbD (i - 23) := by
  rw [arm8JumpRegWord_getLsbD]
  simp [show ¬ i < 5 by omega, show ¬ i < 10 by omega, show ¬ i < 21 by omega,
    show ¬ i < 23 by omega]

theorem arm8JumpRegWord_bit0 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 0 = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit1 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 1 = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit2 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 2 = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit3 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 3 = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit4 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 4 = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit10 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 10 = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit11 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 11 = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit12 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 12 = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit13 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 13 = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit14 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 14 = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit15 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 15 = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit16 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 16 = true := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit17 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 17 = true := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit18 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 18 = true := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit19 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 19 = true := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit20 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 20 = true := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit21 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 21 = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit22 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 22 = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit23 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 23 = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit24 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 24 = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit25 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 25 = true := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit26 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 26 = true := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit27 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 27 = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit28 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 28 = true := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit29 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 29 = false := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit30 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 30 = true := by
  rw [arm8JumpRegWord_getLsbD]
  simp

theorem arm8JumpRegWord_bit31 (rn : BitVec 5) :
    (arm8JumpRegWord rn).getLsbD 31 = true := by
  rw [arm8JumpRegWord_getLsbD]
  simp

/-- The five-bit roundtrip through the `Decode` bit list. -/
theorem arm8JumpRegWord_holV2w (rn : BitVec 5) :
    holV2w 5 [(arm8JumpRegWord rn).getLsbD 9, (arm8JumpRegWord rn).getLsbD 8,
      (arm8JumpRegWord rn).getLsbD 7, (arm8JumpRegWord rn).getLsbD 6,
      (arm8JumpRegWord rn).getLsbD 5] = rn := by
  rw [show (arm8JumpRegWord rn).getLsbD 9 = rn.getLsbD 4 from arm8JumpRegWord_rn rn 9 (by omega) (by omega)]
  rw [show (arm8JumpRegWord rn).getLsbD 8 = rn.getLsbD 3 from arm8JumpRegWord_rn rn 8 (by omega) (by omega)]
  rw [show (arm8JumpRegWord rn).getLsbD 7 = rn.getLsbD 2 from arm8JumpRegWord_rn rn 7 (by omega) (by omega)]
  rw [show (arm8JumpRegWord rn).getLsbD 6 = rn.getLsbD 1 from arm8JumpRegWord_rn rn 6 (by omega) (by omega)]
  rw [show (arm8JumpRegWord rn).getLsbD 5 = rn.getLsbD 0 from arm8JumpRegWord_rn rn 5 (by omega) (by omega)]
  exact holV2w_five rn

/-- `Encode` of a `JMP`-typed `BranchRegister` is the branch-register word. -/
theorem arm8Encode_branchRegister (rn : BitVec 5) :
    Encode (.Branch (.BranchRegister (rn, .BranchType_JMP))) =
      MachineCode.ARM8 (arm8JumpRegWord rn) := by
  simp only [Encode, e_branch, arm8JumpRegWord]
  simp

/-- The rendered `Decode` inverts the branch-register word. -/
theorem arm8Decode_branchRegister (rn : BitVec 5) :
    Decode (arm8JumpRegWord rn) =
      .Branch (.BranchRegister (rn, .BranchType_JMP)) := by
  simp only [Decode, boolify32, arm8JumpRegWord_bit0, arm8JumpRegWord_bit1, arm8JumpRegWord_bit2, arm8JumpRegWord_bit3, arm8JumpRegWord_bit4, arm8JumpRegWord_bit10, arm8JumpRegWord_bit11, arm8JumpRegWord_bit12, arm8JumpRegWord_bit13, arm8JumpRegWord_bit14, arm8JumpRegWord_bit15, arm8JumpRegWord_bit16, arm8JumpRegWord_bit17, arm8JumpRegWord_bit18, arm8JumpRegWord_bit19, arm8JumpRegWord_bit20, arm8JumpRegWord_bit21, arm8JumpRegWord_bit22, arm8JumpRegWord_bit23, arm8JumpRegWord_bit24, arm8JumpRegWord_bit25, arm8JumpRegWord_bit26, arm8JumpRegWord_bit27, arm8JumpRegWord_bit28, arm8JumpRegWord_bit29, arm8JumpRegWord_bit30, arm8JumpRegWord_bit31, arm8JumpRegWord_holV2w,
    Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.and_true,
    Bool.and_false, Bool.false_eq_true, if_true, if_false]

/-- `JumpReg` lowers to the single `BranchRegister` instruction with branch
type `JMP`. -/
theorem arm8Ast_jumpReg (register : Nat) :
    arm8Ast (.jumpReg register) =
      [.Branch (.BranchRegister (BitVec.ofNat 5 register, .BranchType_JMP))] := rfl

/-- The four encoded bytes of the `JMP`-typed `BranchRegister` instruction. -/
theorem arm8EncodeBytes_branchRegister (rn : BitVec 5) :
    arm8Encode (.Branch (.BranchRegister (rn, .BranchType_JMP))) =
      [BitVec.ofNat 8 ((arm8JumpRegWord rn >>> 0).toNat),
       BitVec.ofNat 8 ((arm8JumpRegWord rn >>> 8).toNat),
       BitVec.ofNat 8 ((arm8JumpRegWord rn >>> 16).toNat),
       BitVec.ofNat 8 ((arm8JumpRegWord rn >>> 24).toNat)] := by
  rw [arm8Encode, arm8Encode_branchRegister]

/-- The encoded bytes of the `JumpReg` lowering. -/
theorem arm8Enc_jumpReg (register : Nat) :
    arm8Enc (.jumpReg register) =
      arm8Encode (.Branch
        (.BranchRegister (BitVec.ofNat 5 register, .BranchType_JMP))) := by
  simp [arm8Enc, arm8Ast_jumpReg]

/-- The `JumpReg` lowering encodes to four bytes. -/
theorem arm8Enc_jumpReg_length (register : Nat) :
    (arm8Enc (.jumpReg register)).length = 4 := by
  simp [arm8Enc, arm8Ast_jumpReg, arm8Encode_length]

/-- `Run` of a `JMP`-typed `BranchRegister` at exception level zero, with
`TBI0`/`TBI1` clear, sets the branch hint and `PC` to the register's value. -/
theorem arm8Run_branchRegister (rn : BitVec 5) (st : arm8_state)
    (hel : st.PSTATE.EL = (0 : BitVec 2))
    (htbi1 : st.TCR_EL1.TBI1 = false) (htbi0 : st.TCR_EL1.TBI0 = false) :
    Run (.Branch (.BranchRegister (rn, .BranchType_JMP))) st =
      { st with branch_hint := some .BranchType_JMP, PC := X (TN := 64) rn st } := by
  simp [Run, «dfn'BranchRegister», BranchTo, Hint_Branch, hel, htbi1, htbi0]

/-- One `NextStateARM8` step on the emitted `JMP` branch-register word sets the
branch hint and moves `PC` to the register's value. -/
theorem arm8Next_branchRegister (ms : arm8_state) (rn : BitVec 5)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8JumpRegWord rn >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8JumpRegWord rn >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8JumpRegWord rn >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8JumpRegWord rn >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (htbi1 : ms.TCR_EL1.TBI1 = false) (htbi0 : ms.TCR_EL1.TBI0 = false) :
    NextStateARM8 ms =
      some { ms with branch_hint := some .BranchType_JMP, PC := X (TN := 64) rn ms } := by
  let i : instruction := .Branch (.BranchRegister (rn, .BranchType_JMP))
  have hdec : Decode (arm8JumpRegWord rn) = i := by
    dsimp only [i]
    rw [arm8Decode_branchRegister]
  have hrun : Run i { ms with branch_hint := none } =
      { ms with branch_hint := some .BranchType_JMP, PC := X (TN := 64) rn ms } := by
    dsimp only [i]
    exact arm8Run_branchRegister rn { ms with branch_hint := none }
      (by simpa using hel) (by simpa using htbi1) (by simpa using htbi0)
  have hfetch : Fetch { ms with branch_hint := none } =
      (arm8JumpRegWord rn, { ms with branch_hint := none }) :=
    arm8Fetch_word { ms with branch_hint := none } _ h0 h1 h2 h3 hal he0 hel
  simp only [NextStateARM8, Next]
  rw [hfetch]
  simp only [hdec]
  rw [hrun]
  simp [hexc0]

/-- `arm8Next` on the emitted `JMP` branch-register word. -/
theorem arm8Next_branchRegister' (ms : arm8_state) (rn : BitVec 5)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8JumpRegWord rn >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8JumpRegWord rn >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8JumpRegWord rn >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8JumpRegWord rn >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (htbi1 : ms.TCR_EL1.TBI1 = false) (htbi0 : ms.TCR_EL1.TBI0 = false) :
    arm8Next ms =
      { ms with branch_hint := some .BranchType_JMP, PC := X (TN := 64) rn ms } := by
  unfold arm8Next
  rw [arm8Next_branchRegister ms rn hexc0 h0 h1 h2 h3 hal he0 hel htbi1 htbi0]
  rfl

/-- A passing `assertState` means the asserted condition held. -/
theorem assertState_of_not_failed {width : Nat} [NeZero width] (c : Bool)
    (s : AsmState width) (h : ¬(assertState c s).failed) : c = true := by
  by_contra hc
  have hcf : c = false := by simpa using hc
  simp [assertState, hcf] at h

/-- The `JumpReg` constructor of `encoder_correct arm8TargetL3`: the single
`BranchRegister` instruction moves `PC` to the register's value.  The alignment
of that value is forced by `asm_step`'s `~s2.failed` premise. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_jumpReg (register : Nat) (s1 s2 : AsmState 64)
    (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.jumpReg register) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.jumpReg register) s1 s2 ms := by
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
  have hregok : asmRegOkExact register arm8ConfigL3 = true := by
    simpa [asmOkExact, arm8ConfigL3] using hs.2.2.2.2.2.2
  obtain ⟨hr_lt, hr_av, hr_31⟩ := regOk_of_asmL3 hregok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := (arm8Ok_iff ms).mp hok
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hdom := bytesInMemoryHOL_domain hs.1
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.jumpReg register)) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hs.1, fun n hn => (hmem _ (hdom n hn)).symm⟩
  have hlen : (arm8Enc (.jumpReg register)).length = 4 := arm8Enc_jumpReg_length register
  have henc : arm8Enc (.jumpReg register) =
      [BitVec.ofNat 8 ((arm8JumpRegWord (BitVec.ofNat 5 register) >>> 0).toNat),
       BitVec.ofNat 8 ((arm8JumpRegWord (BitVec.ofNat 5 register) >>> 8).toNat),
       BitVec.ofNat 8 ((arm8JumpRegWord (BitVec.ofNat 5 register) >>> 16).toNat),
       BitVec.ofNat 8 ((arm8JumpRegWord (BitVec.ofNat 5 register) >>> 24).toNat)] := by
    rw [arm8Enc_jumpReg, arm8EncodeBytes_branchRegister]
  have hb0 : ms.MEM ms.PC =
      BitVec.ofNat 8 ((arm8JumpRegWord (BitVec.ofNat 5 register) >>> 0).toNat) := by
    have := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; norm_num)
    rw [henc] at this
    simpa using this
  have hb1 : ms.MEM (ms.PC + 1) =
      BitVec.ofNat 8 ((arm8JumpRegWord (BitVec.ofNat 5 register) >>> 8).toNat) := by
    have := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; norm_num)
    rw [henc] at this
    simpa using this
  have hb2 : ms.MEM (ms.PC + 2) =
      BitVec.ofNat 8 ((arm8JumpRegWord (BitVec.ofNat 5 register) >>> 16).toNat) := by
    have := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; norm_num)
    rw [henc] at this
    simpa using this
  have hb3 : ms.MEM (ms.PC + 3) =
      BitVec.ofNat 8 ((arm8JumpRegWord (BitVec.ofNat 5 register) >>> 24).toNat) := by
    have := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; norm_num)
    rw [henc] at this
    simpa using this
  have hn := arm8Next_branchRegister' ms (BitVec.ofNat 5 register) hexc0 hb0 hb1 hb2 hb3
    hal he0 hel htbi1 htbi0
  have hupd := hs.2.2.2.2.1
  have halignAsm : s1.align = 2 := hs.2.2.2.1
  have hs2 : s2 = updPc (s1.regs register)
      (assertState (holAligned 2 (s1.regs register)) s1) := by
    rw [← hupd]
    simp only [asmUpd, halignAsm]
    rfl
  have hnotfailed : ¬s2.failed := hs.2.2.2.2.2.1
  have htarget : holAligned 2 (s1.regs register) = true := by
    rw [hs2] at hnotfailed
    have hf : ¬(assertState (holAligned 2 (s1.regs register)) s1).failed := by
      simpa [updPc] using hnotfailed
    exact assertState_of_not_failed _ _ hf
  have hs2pc : s2.pc = s1.regs register := by
    rw [hs2]
    simp [updPc, assertState]
  have hs2dom : s2.memDomain = s1.memDomain := by rw [hs2]; rfl
  have hne : (BitVec.ofNat 5 register) ≠ (31 : BitVec 5) := by
    intro hh
    have hh' : BitVec.ofNat 5 register = BitVec.ofNat 5 31 := hh
    exact hr_31 ((arm8Reg_eq hr_lt (by norm_num)).mp hh')
  have hX : X (TN := 64) (BitVec.ofNat 5 register) ms = s1.regs register := by
    simp only [X]
    rw [if_neg (by simpa using hne)]
    simp
    exact hreg register ⟨by simpa [arm8ConfigL3] using hr_lt, by simpa [arm8ConfigL3] using hr_av⟩
  have hokPost : arm8Ok { ms with
      branch_hint := some .BranchType_JMP,
      PC := X (TN := 64) (BitVec.ofNat 5 register) ms } = true := by
    rw [hX]
    simp [arm8Ok, hel, he0, hsa0, htbi1, htbi0, hexc0]
    exact htarget
  have hq : targetStateRel arm8TargetL3 s2
      { ms with
        branch_hint := some .BranchType_JMP,
        PC := X (TN := 64) (BitVec.ofNat 5 register) ms } := by
    refine ⟨hokPost, ?_, ?_, ?_, ?_⟩
    · simp only [arm8TargetL3_getPc]
      rw [hX, hs2pc]
    · intro a ha
      simp only [arm8TargetL3_getByte]
      have ha' : s1.memDomain a := by rw [← hs2dom]; exact ha
      rw [hs2]
      simp [updPc, assertState]
      exact hmem a ha'
    · intro k hk
      simp only [arm8TargetL3_getReg]
      rw [hs2]
      simp [updPc, assertState]
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
          branch_hint := some .BranchType_JMP,
          PC := X (TN := 64) (BitVec.ofNat 5 register) ms })
        { ms with
          branch_hint := some .BranchType_JMP,
          PC := X (TN := 64) (BitVec.ofNat 5 register) ms } := by
      rw [← arm8Proj_eq_iff]
      have hh := henv 0 { ms with
        branch_hint := some .BranchType_JMP,
        PC := X (TN := 64) (BitVec.ofNat 5 register) ms }
      rw [hs2dom]
      exact hh
    exact targetStateRel_congr hagree hq
  · refine ⟨fun x _ => ?_, trivial⟩
    rw [hn]

end Flapjack.Compiler.Encoders.Arm8.L3

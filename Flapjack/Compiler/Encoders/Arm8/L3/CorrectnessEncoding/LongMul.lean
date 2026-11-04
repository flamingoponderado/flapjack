import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Multiply
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Simulate

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# The `longMul` constructor of `encoder_correct arm8TargetL3`

`arm8_ast` lowers `Arith (LongMul high low left right)` to two instructions:
`MultiplyHigh` (the top 64 bits of the unsigned 128-bit product) followed by
`MultiplyAddSub@64` against the zero register (the low 64 bits).  This module
assembles the two-step simulation with `asserts 1` / `asserts2 2`.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The `longMul` constructor of `encoder_correct arm8TargetL3`: the two
instructions `MultiplyHigh` and `MultiplyAddSub@64` simulate the single
`longMul` `asmStep` with `n = 1`, so `asserts 1` and `asserts2 2` hold. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_longMul (destinationLeft destinationRight sourceLeft sourceRight : Nat)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight))) s1 s2 ms := by
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
  have hregok := hs.2.2.2.2.2.2
  simp [asmOkExact, asmInstOkExact, asmArithOkExact, arm8ConfigL3, Bool.and_eq_true] at hregok
  obtain ⟨⟨⟨⟨hdl, hdr⟩, hsl⟩, hsr⟩, hne1, hne2⟩ := hregok
  obtain ⟨hdl_lt, hdl_av, hdl_31⟩ := regOk_of_asmL3 hdl
  obtain ⟨hdr_lt, hdr_av, hdr_31⟩ := regOk_of_asmL3 hdr
  obtain ⟨hsl_lt, hsl_av, hsl_31⟩ := regOk_of_asmL3 hsl
  obtain ⟨hsr_lt, hsr_av, hsr_31⟩ := regOk_of_asmL3 hsr
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := (arm8Ok_iff ms).mp hok
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC
      (arm8Enc (.inst (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  let w0 : BitVec 32 := arm8MultiplyHighWord false (BitVec.ofNat 5 sourceRight)
    (BitVec.ofNat 5 sourceLeft) (BitVec.ofNat 5 destinationLeft)
  let w1 : BitVec 32 := arm8MultiplyAddSubWord false (BitVec.ofNat 5 sourceRight) 31
    (BitVec.ofNat 5 sourceLeft) (BitVec.ofNat 5 destinationRight)
  have henc := arm8Enc_longMul destinationLeft destinationRight sourceLeft sourceRight
  have hlen := arm8Enc_longMul_length destinationLeft destinationRight sourceLeft sourceRight
  rw [arm8EncodeBytes_multiplyHigh, arm8EncodeBytes_multiplyAddSub] at henc
  have hbyte (i : Nat) (hi : i < 8) :
      ms.MEM (ms.PC + BitVec.ofNat 64 i) =
        (arm8Enc (.inst (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight)))).getD i 0 :=
    bytesInMemoryHOL_get hbms i (by rw [hlen]; exact hi)
  have hb0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w0 >>> 0).toNat) := by
    have hh := hbyte 0 (by norm_num)
    rw [henc] at hh
    simpa [w0] using hh
  have hb1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w0 >>> 8).toNat) := by
    have hh := hbyte 1 (by norm_num)
    rw [henc] at hh
    simpa [w0] using hh
  have hb2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w0 >>> 16).toNat) := by
    have hh := hbyte 2 (by norm_num)
    rw [henc] at hh
    simpa [w0] using hh
  have hb3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w0 >>> 24).toNat) := by
    have hh := hbyte 3 (by norm_num)
    rw [henc] at hh
    simpa [w0] using hh
  have hb4 : ms.MEM (ms.PC + 4) = BitVec.ofNat 8 ((w1 >>> 0).toNat) := by
    have hh := hbyte 4 (by norm_num)
    rw [henc] at hh
    simpa [w1] using hh
  have hb5 : ms.MEM (ms.PC + 5) = BitVec.ofNat 8 ((w1 >>> 8).toNat) := by
    have hh := hbyte 5 (by norm_num)
    rw [henc] at hh
    simpa [w1] using hh
  have hb6 : ms.MEM (ms.PC + 6) = BitVec.ofNat 8 ((w1 >>> 16).toNat) := by
    have hh := hbyte 6 (by norm_num)
    rw [henc] at hh
    simpa [w1] using hh
  have hb7 : ms.MEM (ms.PC + 7) = BitVec.ofNat 8 ((w1 >>> 24).toNat) := by
    have hh := hbyte 7 (by norm_num)
    rw [henc] at hh
    simpa [w1] using hh
  let hi : BitVec 64 := BitVec.ofNat 64 ((s1.regs sourceLeft).toNat * (s1.regs sourceRight).toNat / 2 ^ 64)
  let lo : BitVec 64 := BitVec.ofNat 64 ((s1.regs sourceLeft).toNat * (s1.regs sourceRight).toNat)
  let T1 : arm8_state := { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 destinationLeft) hi ms.REG, PC := ms.PC + 4 }
  let T2 : arm8_state := { T1 with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 destinationRight) lo T1.REG, PC := T1.PC + 4 }
  have hT1mem : ∀ x, T1.MEM x = ms.MEM x := by intro x; rfl
  have hT1pc : T1.PC = ms.PC + 4 := by rfl
  have hT2pc : T2.PC = ms.PC + 8 := by
    show T1.PC + 4 = ms.PC + 8
    rw [hT1pc, BitVec.add_assoc]
    rfl
  have hT2mem : ∀ x, T2.MEM x = ms.MEM x := by intro x; rfl
  have hT1exc : T1.exception = exception.NoException := hexc0
  have h4 : holAligned 2 (ms.PC + 4) = true := by
    rw [(alignedAddSub 2 ms.PC 4 (by rw [holAligned_iff]; decide)).1]
    exact halign
  have hal4 : Aligned (TN := 64) (T1.PC, 4) = true := by
    rw [hT1pc]
    exact aligned_of_holAligned (ms.PC + 4) h4
  have hn1 : arm8Next ms = T1 := by
    rw [arm8Next_multiplyHigh ms (BitVec.ofNat 5 sourceRight) (BitVec.ofNat 5 sourceLeft)
      destinationLeft hdl_lt hdl_31 hexc0 hb0 hb1 hb2 hb3 hal he0 hel]
    unfold T1 hi
    rw [arm8MultiplyHigh_extract ms sourceLeft sourceRight hsl_lt hsl_31 hsr_lt hsr_31,
      hreg sourceLeft ⟨hsl_lt, hsl_av⟩, hreg sourceRight ⟨hsr_lt, hsr_av⟩]
  have hn2 : arm8Next T1 = T2 := by
    have hb4' : T1.MEM T1.PC = BitVec.ofNat 8 ((w1 >>> 0).toNat) := by rw [hT1mem, hT1pc]; exact hb4
    have hb5' : T1.MEM (T1.PC + 1) = BitVec.ofNat 8 ((w1 >>> 8).toNat) := by
      rw [hT1mem]; rw [hT1pc, BitVec.add_assoc]; exact hb5
    have hb6' : T1.MEM (T1.PC + 2) = BitVec.ofNat 8 ((w1 >>> 16).toNat) := by
      rw [hT1mem]; rw [hT1pc, BitVec.add_assoc]; exact hb6
    have hb7' : T1.MEM (T1.PC + 3) = BitVec.ofNat 8 ((w1 >>> 24).toNat) := by
      rw [hT1mem]; rw [hT1pc, BitVec.add_assoc]; exact hb7
    rw [arm8Next_multiplyAddSub T1 (BitVec.ofNat 5 sourceRight) 31 (BitVec.ofNat 5 sourceLeft)
      destinationRight hdr_lt hdr_31 hT1exc hb4' hb5' hb6' hb7' hal4 he0 hel]
    unfold T2 lo T1
    have hneL : (BitVec.ofNat 5 sourceLeft) ≠ (BitVec.ofNat 5 destinationLeft) := by
      intro hh
      exact hne1 (by have := congrArg BitVec.toNat hh; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega)
    have hneR : (BitVec.ofNat 5 sourceRight) ≠ (BitVec.ofNat 5 destinationLeft) := by
      intro hh
      exact hne2 (by have := congrArg BitVec.toNat hh; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega)
    rw [arm8X_zero_ofNat, arm8Zero_add,
      arm8X_longMulT1 ms hi (BitVec.ofNat 5 destinationLeft) hneL,
      arm8X_longMulT1 ms hi (BitVec.ofNat 5 destinationLeft) hneR,
      arm8X_of_valid _ hsl_31 hsl_lt, arm8X_of_valid _ hsr_31 hsr_lt,
      hreg sourceLeft ⟨hsl_lt, hsl_av⟩, hreg sourceRight ⟨hsr_lt, hsr_av⟩, arm8Mul_ofNat]
  have hok1 : arm8Ok T1 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    rw [hT1pc]
    exact h4
  have hok2 : arm8Ok T2 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    rw [hT2pc]
    rw [show ms.PC + 8 = ms.PC + 4 + 4 from by rw [BitVec.add_assoc]; rfl,
      (alignedAddSub 2 (ms.PC + 4) 4 (by rw [holAligned_iff]; decide)).1]
    exact h4
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  rw [hlen] at hupd
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 8 := by rw [← hupd]; simp [asmUpd, instUpd, arithUpd, updPc]
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by intro x; rw [← hupd]; simp [asmUpd, instUpd, arithUpd, updReg, updPc]
  have hs2dom : s2.memDomain = s1.memDomain := by rw [← hupd]; simp [asmUpd, instUpd, arithUpd, updReg, updPc]
  have hs2regs : ∀ k, s2.regs k = if k = destinationRight then lo else if k = destinationLeft then hi else s1.regs k := by
    intro k
    rw [← hupd]
    simp [asmUpd, instUpd, arithUpd, updReg, updPc, hi, lo,
      Flapjack.Compiler.Encoders.AsmSem.readReg]
  have hq : targetStateRel arm8TargetL3 s2 T2 := by
    refine ⟨hok2, ?_, ?_, ?_, ?_⟩
    · change T2.PC = s2.pc
      rw [hT2pc, hs2pc, hpc]
      simp
    · change ∀ a, s2.memDomain a → T2.MEM a = s2.mem a
      intro a ha
      rw [hT2mem, hs2mem]
      exact hmem a (hs2dom ▸ ha)
    · change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
        T2.REG (BitVec.ofNat 5 k) = s2.regs k
      intro k hk
      have hk32 : k < 32 := by simpa [arm8ConfigL3] using hk.1
      rw [hs2regs k]
      unfold T2 T1
      simp only [Flapjack.RiscV.L3.holUpdate]
      by_cases h1 : k = destinationRight
      · rw [if_pos (by rw [h1]), if_pos h1]
      · rw [if_neg h1]
        by_cases h2 : k = destinationLeft
        · have hne : (BitVec.ofNat 5 destinationRight) ≠ (BitVec.ofNat 5 k) := by
            intro hh
            exact h1 ((arm8Reg_eq hk32 hdr_lt).1 hh.symm)
          rw [if_neg hne, if_pos (by rw [h2]), if_pos h2]
        · have hne1 : (BitVec.ofNat 5 destinationRight) ≠ (BitVec.ofNat 5 k) := by
            intro hh
            exact h1 ((arm8Reg_eq hk32 hdr_lt).1 hh.symm)
          have hne2 : (BitVec.ofNat 5 destinationLeft) ≠ (BitVec.ofNat 5 k) := by
            intro hh
            exact h2 ((arm8Reg_eq hk32 hdl_lt).1 hh.symm)
          rw [if_neg hne1, if_neg hne2, if_neg h2]
          exact hreg k hk
    · intro k hk
      simp [arm8ConfigL3] at hk
  have hdomT1 : ∀ j, j < 4 → s1.memDomain (T1.PC + BitVec.ofNat 64 j) := by
    intro j hj
    have h1 : T1.PC + BitVec.ofNat 64 j = s1.pc + BitVec.ofNat 64 (4 + j) := by
      show ms.PC + (4 : BitVec 64) + BitVec.ofNat 64 j = s1.pc + BitVec.ofNat 64 (4 + j)
      rw [hpc]
      exact bv_add_split s1.pc 4 j
    rw [h1]
    exact hdom (4 + j) (by omega)
  have hb4'' : T1.MEM T1.PC = BitVec.ofNat 8 ((w1 >>> 0).toNat) := by rw [hT1mem, hT1pc]; exact hb4
  have hb5'' : T1.MEM (T1.PC + 1) = BitVec.ofNat 8 ((w1 >>> 8).toNat) := by rw [hT1mem]; rw [hT1pc, BitVec.add_assoc]; exact hb5
  have hb6'' : T1.MEM (T1.PC + 2) = BitVec.ofNat 8 ((w1 >>> 16).toNat) := by rw [hT1mem]; rw [hT1pc, BitVec.add_assoc]; exact hb6
  have hb7'' : T1.MEM (T1.PC + 3) = BitVec.ofNat 8 ((w1 >>> 24).toNat) := by rw [hT1mem]; rw [hT1pc, BitVec.add_assoc]; exact hb7
  refine asmCaseChain _ 1 (fun k => if k = 1 then T1 else T2) s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hlen ?_ ?_ ?_ ?_ ?_ hs2dom hq
  · intro k hk u hu
    interval_cases k
    · rw [hu.1 rfl, hn1]
      exact Arm8L3Agree.refl _ _
    · have hh := arm8Next_multiplyAddSub_agree s1.memDomain u T1 (hu.2 (by decide))
        (by rw [arm8Ok_congr (hu.2 (by decide))]; exact hok1) (BitVec.ofNat 5 sourceRight) 31
        (BitVec.ofNat 5 sourceLeft) destinationRight hdr_lt hdr_31
        (by intro hh; exact hsl_31 ((arm8Reg_eq hsl_lt (by norm_num)).1 hh))
        (by intro hh; exact hsr_31 ((arm8Reg_eq hsr_lt (by norm_num)).1 hh))
        (by intro j hj; exact hdomT1 j hj)
        hb4'' hb5'' hb6'' hb7''
      rw [hn2] at hh
      exact hh
  · intro k hk u hu x _
    interval_cases k
    · rw [hu.1 rfl, hn1]
    · have hu1 : Arm8L3Agree s1.memDomain u T1 := hu.2 (by decide)
      obtain ⟨b0, b1, b2, b3⟩ := hu1.word hdomT1 _ hb4'' hb5'' hb6'' hb7''
      exact arm8Next_multiplyAddSub_mem u (BitVec.ofNat 5 sourceRight) 31
        (BitVec.ofNat 5 sourceLeft) destinationRight hdr_lt hdr_31
        (by rw [hu1.exc]; exact hexc0) b0 b1 b2 b3 (by rw [hu1.pc]; exact hal4)
        (by rw [hu1.sctlr]; exact he0) (by rw [hu1.pstate]; exact hel) x
  · intro k h1 h2
    obtain rfl : k = 1 := by omega
    exact hok1
  · intro k h1 h2
    obtain rfl : k = 1 := by omega
    exact hT1pc
  · intro k h1 h2 x _
    obtain rfl : k = 1 := by omega
    exact hT1mem x

end Flapjack.Compiler.Encoders.Arm8.L3

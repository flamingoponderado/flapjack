module

public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Branch

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# `BranchConditional`: the conditional-branch word

`arm8_ast` lowers `JumpCmp` to a flag-setting compare followed by a
`BranchConditional`.  This module records the conditional-branch word
(`01010100 imm19 0 cd`), its `Encode`/`Decode` inverse, the byte split, the
`Run` semantics (`BranchTo` when the condition holds, unchanged otherwise) and
one `NextStateARM8` step.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The conditional-branch word: `01010100 imm19 0 cd`. -/
def arm8BranchCondWord (imm19 : BitVec 19) (cd : BitVec 4) : BitVec 32 :=
  BitVec.setWidth 32 ((BitVec.ofNat 8 84) ++
    BitVec.setWidth 24 (imm19 ++ BitVec.setWidth 5 ((BitVec.ofNat 1 0) ++ cd)))

/-- Every bit of the conditional-branch word: `cd` in bits 0--3, zero in bit 4,
`imm19` in bits 5--23 and the `01010100` opcode in bits 24--31. -/
theorem arm8BranchCondWord_getLsbD (imm19 : BitVec 19) (cd : BitVec 4) (i : Nat)
    (hi : i < 32) :
    (arm8BranchCondWord imm19 cd).getLsbD i =
      if i < 4 then cd.getLsbD i
      else if i = 4 then false
      else if i < 24 then imm19.getLsbD (i - 5)
      else (BitVec.ofNat 8 84).getLsbD (i - 24) := by
  unfold arm8BranchCondWord
  rw [BitVec.setWidth_eq]
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat]
  interval_cases i <;> simp

/-- An `imm19` bit of the conditional-branch word. -/
theorem arm8BranchCondWord_imm_bit (imm19 : BitVec 19) (cd : BitVec 4) (k : Nat)
    (h1 : 5 ≤ k) (h2 : k < 24) :
    (arm8BranchCondWord imm19 cd).getLsbD k = imm19.getLsbD (k - 5) := by
  rw [arm8BranchCondWord_getLsbD imm19 cd k (by omega)]
  rw [if_neg (by omega : ¬ (k < 4)), if_neg (by omega : ¬ (k = 4)), if_pos h2]

/-- A `cd` bit of the conditional-branch word. -/
theorem arm8BranchCondWord_cd_bit (imm19 : BitVec 19) (cd : BitVec 4) (k : Nat)
    (hk : k < 4) :
    (arm8BranchCondWord imm19 cd).getLsbD k = cd.getLsbD k := by
  rw [arm8BranchCondWord_getLsbD imm19 cd k (by omega)]
  rw [if_pos hk]

theorem arm8BranchCondWord_bit4 (imm19 : BitVec 19) (cd : BitVec 4) :
    (arm8BranchCondWord imm19 cd).getLsbD 4 = false := by
  rw [arm8BranchCondWord_getLsbD imm19 cd 4 (by omega)]
  rw [if_neg (by decide : ¬ (4 < 4)), if_pos (by decide : 4 = 4)]

theorem arm8BranchCondWord_bit24 (imm19 : BitVec 19) (cd : BitVec 4) :
    (arm8BranchCondWord imm19 cd).getLsbD 24 = false := by
  rw [arm8BranchCondWord_getLsbD imm19 cd 24 (by omega)]
  rw [if_neg (by decide : ¬ (24 < 4)), if_neg (by decide : ¬ (24 = 4)),
    if_neg (by decide : ¬ (24 < 24))]
  decide

theorem arm8BranchCondWord_bit25 (imm19 : BitVec 19) (cd : BitVec 4) :
    (arm8BranchCondWord imm19 cd).getLsbD 25 = false := by
  rw [arm8BranchCondWord_getLsbD imm19 cd 25 (by omega)]
  rw [if_neg (by decide : ¬ (25 < 4)), if_neg (by decide : ¬ (25 = 4)),
    if_neg (by decide : ¬ (25 < 24))]
  decide

theorem arm8BranchCondWord_bit26 (imm19 : BitVec 19) (cd : BitVec 4) :
    (arm8BranchCondWord imm19 cd).getLsbD 26 = true := by
  rw [arm8BranchCondWord_getLsbD imm19 cd 26 (by omega)]
  rw [if_neg (by decide : ¬ (26 < 4)), if_neg (by decide : ¬ (26 = 4)),
    if_neg (by decide : ¬ (26 < 24))]
  decide

theorem arm8BranchCondWord_bit27 (imm19 : BitVec 19) (cd : BitVec 4) :
    (arm8BranchCondWord imm19 cd).getLsbD 27 = false := by
  rw [arm8BranchCondWord_getLsbD imm19 cd 27 (by omega)]
  rw [if_neg (by decide : ¬ (27 < 4)), if_neg (by decide : ¬ (27 = 4)),
    if_neg (by decide : ¬ (27 < 24))]
  decide

theorem arm8BranchCondWord_bit28 (imm19 : BitVec 19) (cd : BitVec 4) :
    (arm8BranchCondWord imm19 cd).getLsbD 28 = true := by
  rw [arm8BranchCondWord_getLsbD imm19 cd 28 (by omega)]
  rw [if_neg (by decide : ¬ (28 < 4)), if_neg (by decide : ¬ (28 = 4)),
    if_neg (by decide : ¬ (28 < 24))]
  decide

theorem arm8BranchCondWord_bit29 (imm19 : BitVec 19) (cd : BitVec 4) :
    (arm8BranchCondWord imm19 cd).getLsbD 29 = false := by
  rw [arm8BranchCondWord_getLsbD imm19 cd 29 (by omega)]
  rw [if_neg (by decide : ¬ (29 < 4)), if_neg (by decide : ¬ (29 = 4)),
    if_neg (by decide : ¬ (29 < 24))]
  decide

theorem arm8BranchCondWord_bit30 (imm19 : BitVec 19) (cd : BitVec 4) :
    (arm8BranchCondWord imm19 cd).getLsbD 30 = true := by
  rw [arm8BranchCondWord_getLsbD imm19 cd 30 (by omega)]
  rw [if_neg (by decide : ¬ (30 < 4)), if_neg (by decide : ¬ (30 = 4)),
    if_neg (by decide : ¬ (30 < 24))]
  decide

theorem arm8BranchCondWord_bit31 (imm19 : BitVec 19) (cd : BitVec 4) :
    (arm8BranchCondWord imm19 cd).getLsbD 31 = false := by
  rw [arm8BranchCondWord_getLsbD imm19 cd 31 (by omega)]
  rw [if_neg (by decide : ¬ (31 < 4)), if_neg (by decide : ¬ (31 = 4)),
    if_neg (by decide : ¬ (31 < 24))]
  decide

/-- The `imm19` field reassembles from bits 23--5. -/
theorem arm8BranchCondWord_imm19 (imm19 : BitVec 19) (cd : BitVec 4) :
    holV2w 19 [(arm8BranchCondWord imm19 cd).getLsbD 23, (arm8BranchCondWord imm19 cd).getLsbD 22, (arm8BranchCondWord imm19 cd).getLsbD 21, (arm8BranchCondWord imm19 cd).getLsbD 20, (arm8BranchCondWord imm19 cd).getLsbD 19, (arm8BranchCondWord imm19 cd).getLsbD 18, (arm8BranchCondWord imm19 cd).getLsbD 17, (arm8BranchCondWord imm19 cd).getLsbD 16, (arm8BranchCondWord imm19 cd).getLsbD 15, (arm8BranchCondWord imm19 cd).getLsbD 14, (arm8BranchCondWord imm19 cd).getLsbD 13, (arm8BranchCondWord imm19 cd).getLsbD 12, (arm8BranchCondWord imm19 cd).getLsbD 11, (arm8BranchCondWord imm19 cd).getLsbD 10, (arm8BranchCondWord imm19 cd).getLsbD 9, (arm8BranchCondWord imm19 cd).getLsbD 8, (arm8BranchCondWord imm19 cd).getLsbD 7, (arm8BranchCondWord imm19 cd).getLsbD 6, (arm8BranchCondWord imm19 cd).getLsbD 5] = imm19 := by
  rw [show holV2w 19 [(arm8BranchCondWord imm19 cd).getLsbD 23, (arm8BranchCondWord imm19 cd).getLsbD 22, (arm8BranchCondWord imm19 cd).getLsbD 21, (arm8BranchCondWord imm19 cd).getLsbD 20, (arm8BranchCondWord imm19 cd).getLsbD 19, (arm8BranchCondWord imm19 cd).getLsbD 18, (arm8BranchCondWord imm19 cd).getLsbD 17, (arm8BranchCondWord imm19 cd).getLsbD 16, (arm8BranchCondWord imm19 cd).getLsbD 15, (arm8BranchCondWord imm19 cd).getLsbD 14, (arm8BranchCondWord imm19 cd).getLsbD 13, (arm8BranchCondWord imm19 cd).getLsbD 12, (arm8BranchCondWord imm19 cd).getLsbD 11, (arm8BranchCondWord imm19 cd).getLsbD 10, (arm8BranchCondWord imm19 cd).getLsbD 9, (arm8BranchCondWord imm19 cd).getLsbD 8, (arm8BranchCondWord imm19 cd).getLsbD 7, (arm8BranchCondWord imm19 cd).getLsbD 6, (arm8BranchCondWord imm19 cd).getLsbD 5] = holV2w 19 (holW2v imm19) from by
    congr 1
    rw [show holW2v imm19 = [imm19.getLsbD 18, imm19.getLsbD 17, imm19.getLsbD 16, imm19.getLsbD 15, imm19.getLsbD 14, imm19.getLsbD 13, imm19.getLsbD 12, imm19.getLsbD 11, imm19.getLsbD 10, imm19.getLsbD 9, imm19.getLsbD 8, imm19.getLsbD 7, imm19.getLsbD 6, imm19.getLsbD 5, imm19.getLsbD 4, imm19.getLsbD 3, imm19.getLsbD 2, imm19.getLsbD 1, imm19.getLsbD 0] from rfl]
    rw [arm8BranchCondWord_imm_bit imm19 cd 23 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 22 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 21 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 20 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 19 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 18 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 17 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 16 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 15 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 14 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 13 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 12 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 11 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 10 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 9 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 8 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 7 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 6 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 5 (by decide) (by decide)],
    holV2w_holW2v]

/-- The `cd` field reassembles from bits 3--0. -/
theorem arm8BranchCondWord_cd (imm19 : BitVec 19) (cd : BitVec 4) :
    holV2w 4 [(arm8BranchCondWord imm19 cd).getLsbD 3, (arm8BranchCondWord imm19 cd).getLsbD 2, (arm8BranchCondWord imm19 cd).getLsbD 1, (arm8BranchCondWord imm19 cd).getLsbD 0] = cd := by
  rw [show holV2w 4 [(arm8BranchCondWord imm19 cd).getLsbD 3, (arm8BranchCondWord imm19 cd).getLsbD 2, (arm8BranchCondWord imm19 cd).getLsbD 1, (arm8BranchCondWord imm19 cd).getLsbD 0] = holV2w 4 (holW2v cd) from by
    congr 1
    rw [show holW2v cd = [cd.getLsbD 3, cd.getLsbD 2, cd.getLsbD 1, cd.getLsbD 0] from rfl]
    rw [arm8BranchCondWord_cd_bit imm19 cd 3 (by decide),
      arm8BranchCondWord_cd_bit imm19 cd 2 (by decide),
      arm8BranchCondWord_cd_bit imm19 cd 1 (by decide),
      arm8BranchCondWord_cd_bit imm19 cd 0 (by decide)],
    holV2w_holW2v]

/-- The bits 20:2 of a word sit at positions `i - 2` after a two-bit shift
masked to nineteen bits. -/
theorem arm8TestBit_shift_mod19 (x i : Nat) (h2 : 2 ≤ i) (hi : i < 21) :
    (x >>> 2 % 524288).testBit (i - 2) = x.testBit i := by
  have h := Nat.testBit_mod_two_pow (x >>> 2) 19 (i - 2)
  rw [show (2 : Nat) ^ 19 = 524288 from rfl] at h
  rw [h]
  rw [Nat.testBit_shiftRight]
  have h3 : 2 + (i - 2) = i := by omega
  rw [h3]
  simp [show i - 2 < 19 from by omega]

/-- The 19-bit branch immediate followed by two zero bits reassembles to the
low 21 bits of a four-byte-aligned offset. -/
theorem arm8BranchCondBits (imm : BitVec 64) (hal : imm.toNat % 4 = 0) :
    holWordExtract 19 20 2 imm ++ BitVec.ofNat 2 0 = BitVec.setWidth 21 imm := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [holWordExtract, Flapjack.RiscV.L3.holWordExtract, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat]
  norm_num
  by_cases h2 : i < 2
  · have him : imm.getLsbD i = false := by
      simp [BitVec.getLsbD, arm8TestBit_mod_four_zero imm.toNat i hal h2]
    rw [him]
    simp [h2, hi]
  · have h19 : i - 2 < 19 := by omega
    have h64 : i - 2 < 64 := by omega
    rw [arm8TestBit_shift_mod19 imm.toNat i (by omega) (by omega)]
    simp [BitVec.getLsbD, h2, h19, h64, hi]

/-- The signed value of the low 21 bits of an offset in the signed 21-bit
branch range is the offset itself. -/
theorem arm8BranchCondSignExtend (imm : BitVec 64)
    (hlo : -(2 ^ 20 : Int) ≤ imm.toInt) (hhi : imm.toInt ≤ 2 ^ 20 - 1) :
    BitVec.signExtend 64 (BitVec.setWidth 21 imm) = imm := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend, BitVec.toInt_setWidth, BitVec.toInt_eq_toNat_bmod]
  norm_num
  have hdvd64 : ((2 ^ 64 : ℕ) : ℤ) ∣ imm.toInt - ((imm.toNat : ℕ) : ℤ) := by
    rw [BitVec.toInt_eq_toNat_bmod]
    exact ((Int.bmod_eq_iff (by norm_num : 0 < 2 ^ 64)).mp rfl).2.2
  have hdvd21 : ((2 ^ 21 : ℕ) : ℤ) ∣ imm.toInt - ((imm.toNat : ℕ) : ℤ) := by
    obtain ⟨c, hc⟩ := hdvd64
    refine ⟨c * (2 ^ 43 : ℤ), ?_⟩
    rw [hc]
    push_cast
    omega
  have hb21 : 0 < (2 ^ 21 : ℕ) := by norm_num
  rw [← BitVec.toInt_eq_toNat_bmod]
  refine (Int.bmod_eq_iff hb21).mpr ⟨?_, ?_, hdvd21⟩
  · push_cast; omega
  · push_cast; omega

/-- The conditional-branch immediate reassembles to the offset when the offset
is in the signed 21-bit range and four-byte aligned. -/
theorem arm8BranchCondRoundtrip (imm : BitVec 64)
    (hlo : -(2 ^ 20 : Int) ≤ imm.toInt) (hhi : imm.toInt ≤ 2 ^ 20 - 1)
    (hal : imm.toNat % 4 = 0) :
    BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 imm ++ BitVec.ofNat 2 0)) = imm := by
  rw [arm8BranchCondBits imm hal]
  exact arm8BranchCondSignExtend imm hlo hhi

/-- `Encode` of a `BranchConditional` in the signed 21-bit range is the
conditional-branch word. -/
theorem arm8Encode_branchConditional (imm : BitVec 64) (cd : BitVec 4)
    (h : BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 imm ++ BitVec.ofNat 2 0)) = imm) :
    Encode (.Branch (.BranchConditional (imm, cd))) =
      MachineCode.ARM8 (arm8BranchCondWord (holWordExtract 19 20 2 imm) cd) := by
  have hc : (imm == BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 imm ++ BitVec.ofNat 2 0))) = true := by
    rw [h]; simp
  simp only [Encode, e_branch, arm8BranchCondWord]
  rw [hc]
  rfl

/-- The rendered `Decode` inverts the conditional-branch word. -/
theorem arm8Decode_branchConditional (imm19 : BitVec 19) (cd : BitVec 4) :
    Decode (arm8BranchCondWord imm19 cd) =
      .Branch (.BranchConditional
        (BitVec.signExtend 64 (BitVec.setWidth 21 (imm19 ++ BitVec.ofNat 2 0)), cd)) := by
  simp only [Decode, boolify32, arm8BranchCondWord_bit31, arm8BranchCondWord_bit30,
    arm8BranchCondWord_bit29, arm8BranchCondWord_bit28, arm8BranchCondWord_bit27,
    arm8BranchCondWord_bit26, arm8BranchCondWord_bit25, arm8BranchCondWord_bit24,
    arm8BranchCondWord_bit4, holV2w_one_false,
    Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.and_true,
    Bool.and_false, Bool.false_eq_true, if_true, if_false]
  rw [arm8BranchCondWord_imm_bit imm19 cd 23 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 22 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 21 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 20 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 19 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 18 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 17 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 16 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 15 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 14 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 13 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 12 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 11 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 10 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 9 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 8 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 7 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 6 (by decide) (by decide),
      arm8BranchCondWord_imm_bit imm19 cd 5 (by decide) (by decide),
    arm8BranchCondWord_cd_bit imm19 cd 3 (by decide),
      arm8BranchCondWord_cd_bit imm19 cd 2 (by decide),
      arm8BranchCondWord_cd_bit imm19 cd 1 (by decide),
      arm8BranchCondWord_cd_bit imm19 cd 0 (by decide)]
  rw [show holV2w 19 [imm19.getLsbD 18, imm19.getLsbD 17, imm19.getLsbD 16, imm19.getLsbD 15, imm19.getLsbD 14, imm19.getLsbD 13, imm19.getLsbD 12, imm19.getLsbD 11, imm19.getLsbD 10, imm19.getLsbD 9, imm19.getLsbD 8, imm19.getLsbD 7, imm19.getLsbD 6, imm19.getLsbD 5, imm19.getLsbD 4, imm19.getLsbD 3, imm19.getLsbD 2, imm19.getLsbD 1, imm19.getLsbD 0] = imm19 from holV2w_holW2v imm19,
    show holV2w 4 [cd.getLsbD 3, cd.getLsbD 2, cd.getLsbD 1, cd.getLsbD 0] = cd from holV2w_holW2v cd]

/-- The four encoded bytes of the conditional-branch word. -/
theorem arm8EncodeBytes_branchConditional (imm : BitVec 64) (cd : BitVec 4)
    (h : BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 imm ++ BitVec.ofNat 2 0)) = imm) :
    arm8Encode (.Branch (.BranchConditional (imm, cd))) =
      [BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 imm) cd >>> 0).toNat),
       BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 imm) cd >>> 8).toNat),
       BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 imm) cd >>> 16).toNat),
       BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 imm) cd >>> 24).toNat)] := by
  rw [arm8Encode, arm8Encode_branchConditional imm cd h]

/-- `ConditionHolds` reads only `PSTATE`. -/
theorem arm8ConditionHolds_congr (cd : BitVec 4) {s t : arm8_state}
    (h : s.PSTATE = t.PSTATE) :
    ConditionHolds cd s = ConditionHolds cd t := by
  simp only [ConditionHolds, h]

/-- `Run` of `BranchConditional`: when the condition holds, branch to
`PC + offset`; otherwise leave the state unchanged. -/
theorem arm8Run_branchConditional (l : BitVec 64) (cd : BitVec 4) (st : arm8_state)
    (hel : st.PSTATE.EL = (0 : BitVec 2))
    (htbi1 : st.TCR_EL1.TBI1 = false) (htbi0 : st.TCR_EL1.TBI0 = false) :
    Run (.Branch (.BranchConditional (l, cd))) st =
      (if ConditionHolds cd st then
        { st with branch_hint := some .BranchType_JMP, PC := st.PC + l }
       else st) := by
  simp only [Run, «dfn'BranchConditional»]
  by_cases hc : ConditionHolds cd st = true
  · simp [hc, BranchTo, Hint_Branch, hel, htbi1, htbi0]
  · have hc' : ConditionHolds cd st = false := by
      cases h : ConditionHolds cd st
      · rfl
      · exact absurd h hc
    simp [hc']

/-- One `NextStateARM8` step on the emitted conditional-branch word: when the
condition holds `PC` becomes `PC + offset` and the branch hint is set; otherwise
the state is unchanged and `PC` advances by four. -/
theorem arm8Next_branchConditional (ms : arm8_state) (l : BitVec 64) (cd : BitVec 4)
    (hround : BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 l ++ BitVec.ofNat 2 0)) = l)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) =
      BitVec.ofNat 8 ((arm8BranchCondWord (holWordExtract 19 20 2 l) cd >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (htbi1 : ms.TCR_EL1.TBI1 = false) (htbi0 : ms.TCR_EL1.TBI0 = false) :
    NextStateARM8 ms =
      some (if ConditionHolds cd ms then
        { ms with branch_hint := some .BranchType_JMP, PC := ms.PC + l }
       else { ms with branch_hint := none, PC := ms.PC + 4 }) := by
  let i : instruction := .Branch (.BranchConditional (l, cd))
  have hdec : Decode (arm8BranchCondWord (holWordExtract 19 20 2 l) cd) = i := by
    dsimp only [i]
    rw [arm8Decode_branchConditional, hround]
  have hfetch : Fetch { ms with branch_hint := none } =
      (arm8BranchCondWord (holWordExtract 19 20 2 l) cd, { ms with branch_hint := none }) :=
    arm8Fetch_word { ms with branch_hint := none } _ h0 h1 h2 h3 hal he0 hel
  have hrun := arm8Run_branchConditional l cd { ms with branch_hint := none }
    (by simpa using hel) (by simpa using htbi1) (by simpa using htbi0)
  by_cases hc : ConditionHolds cd ms = true
  · have hc2 : ConditionHolds cd { ms with branch_hint := none } = true := by
      rw [arm8ConditionHolds_congr cd (s := { ms with branch_hint := none }) (t := ms) (by rfl)]
      exact hc
    have hrunA : Run i { ms with branch_hint := none } =
        { ms with branch_hint := some .BranchType_JMP, PC := ms.PC + l } := by
      rw [hrun, if_pos hc2]
    have hnextA : Next ms =
        { ms with branch_hint := some .BranchType_JMP, PC := ms.PC + l } := by
      simp only [Next]
      rw [hfetch]
      simp only [hdec]
      rw [hrunA]
      simp
    have hA : NextStateARM8 ms =
        some { ms with branch_hint := some .BranchType_JMP, PC := ms.PC + l } := by
      simp only [NextStateARM8, hnextA]
      simp [hexc0]
    rw [hA]
    simp [hc]
  · have hc' : ConditionHolds cd ms = false := by
      cases h : ConditionHolds cd ms
      · rfl
      · exact absurd h hc
    have hc2 : ConditionHolds cd { ms with branch_hint := none } = false := by
      rw [arm8ConditionHolds_congr cd (s := { ms with branch_hint := none }) (t := ms) (by rfl)]
      exact hc'
    have hrunB : Run i { ms with branch_hint := none } =
        { ms with branch_hint := none } := by
      rw [hrun, if_neg (by rw [hc2]; simp)]
    have hnextB : Next ms = { ms with branch_hint := none, PC := ms.PC + 4 } := by
      simp only [Next]
      rw [hfetch]
      simp only [hdec]
      rw [hrunB]
      simp
    have hB : NextStateARM8 ms = some { ms with branch_hint := none, PC := ms.PC + 4 } := by
      simp only [NextStateARM8, hnextB]
      simp [hexc0]
    rw [hB]
    simp [hc']

end Flapjack.Compiler.Encoders.Arm8.L3

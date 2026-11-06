import Flapjack.Compiler.Encoders.Arm8.L3.Executable.Logical
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Branch
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.BranchConditional

/-!
# Branch instructions: bytes for the L3 bridge

`Arm8.encodeInsn32` encodes `BranchImmediate` and `BranchConditional` from the
low 26/19 bits of the offset, guarded by a signed-range and four-byte-alignment
test.  The L3 `Encode` instead tests that the offset is the sign extension of
those bits.  This module proves `Arm8.encodeBytes` equals `L3.arm8Encode` for
both forms, taking the two guards as hypotheses; the caller discharges them
from the shared signed-range and alignment facts (`arm8BranchRoundtrip`,
`arm8BranchCondRoundtrip`, `fitsSigned_iff_signExtend`).

No new HOL claim is introduced: the bridge relates two Lean renderings of the
same instruction word.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-- The branch word for a `call`/`jmp` immediate: `(call = CALL) ++ 00101 ++ imm26`. -/
def arm8BranchWordGen (call : Bool) (imm26 : BitVec 26) : BitVec 32 :=
  BitVec.setWidth 32 (holV2w 1 [call] ++ BitVec.setWidth 31 ((BitVec.ofNat 5 5) ++ imm26))

/-- The `BranchImmediate` word: `fields` and the L3 concatenation agree. -/
theorem fields_branchImmediate (call : Bool) (imm : BitVec 64) :
    fields [(1, bit call), (5, 5), (26, (imm >>> 2).toNat % 2 ^ 26)] =
      arm8BranchWordGen call (BitVec.ofNat 26 ((imm >>> 2).toNat % 2 ^ 26)) := by
  cases call <;>
    · simp only [fields, List.foldl_cons, List.foldl_nil, arm8BranchWordGen,
        bit_false, bit_true, holV2w_one_true, holV2w_one_false]
      rw [ofNat_mod_setWidth 1, ofNat_mod_setWidth 5, ofNat_mod_setWidth 26]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
        BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
      interval_cases i <;> simp

/-- The low 26 bits of `imm >>> 2` are `holWordExtract 26 27 2 imm`. -/
theorem ofNat26_shift_eq (imm : BitVec 64) :
    BitVec.ofNat 26 ((imm >>> 2).toNat % 2 ^ 26) = holWordExtract 26 27 2 imm := by
  simp only [holWordExtract]
  rw [holWordExtract_eq_setWidth 26 27 2 imm (by decide) (by decide) (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.mod_lt ((imm >>> 2).toNat) (by norm_num : 0 < 2 ^ 26))]
  rfl

/-- `arm8Encode` of a `BranchImmediate` is the word's bytes. -/
theorem arm8EncodeBytes_branchImmediate_gen (call : Bool) (imm : BitVec 64)
    (hl3 : BitVec.signExtend 64 (BitVec.setWidth 28
      (holWordExtract 26 27 2 imm ++ BitVec.ofNat 2 0)) = imm) :
    arm8Encode (.Branch (.BranchImmediate
        (imm, if call then .BranchType_CALL else .BranchType_JMP))) =
      [BitVec.ofNat 8 ((arm8BranchWordGen call (holWordExtract 26 27 2 imm) >>> 0).toNat),
       BitVec.ofNat 8 ((arm8BranchWordGen call (holWordExtract 26 27 2 imm) >>> 8).toNat),
       BitVec.ofNat 8 ((arm8BranchWordGen call (holWordExtract 26 27 2 imm) >>> 16).toNat),
       BitVec.ofNat 8 ((arm8BranchWordGen call (holWordExtract 26 27 2 imm) >>> 24).toNat)] := by
  cases call
  · exact arm8EncodeBytes_branchImmediate imm hl3
  · have hc : (imm == BitVec.signExtend 64 (BitVec.setWidth 28
        (holWordExtract 26 27 2 imm ++ BitVec.ofNat 2 0))) = true := by
      rw [hl3]
      simp
    have hb : (decide True ||
        (decide (BranchType.BranchType_CALL = BranchType.BranchType_JMP) || false)) = true := by
      decide
    have hb1 : (BranchType.BranchType_CALL == BranchType.BranchType_CALL) = true := rfl
    simp only [arm8Encode, Encode, e_branch, hc, hb, Bool.true_and, hb1,
      holV2w_one_true, arm8BranchWordGen, if_true]

/-- A `BranchImmediate` encodes to the same four bytes on both sides. -/
theorem encodeBytes_branchImmediate_of_guard (imm : BitVec 64) (call : Bool)
    (hguard : (fitsSigned 28 imm && decide (imm.toNat % 4 = 0)) = true)
    (hl3 : BitVec.signExtend 64 (BitVec.setWidth 28
      (holWordExtract 26 27 2 imm ++ BitVec.ofNat 2 0)) = imm) :
    encodeBytes (.branchImmediate imm call) =
      arm8Encode (.Branch (.BranchImmediate
        (imm, if call then .BranchType_CALL else .BranchType_JMP))) := by
  have hw : encodeInsn32 (.branchImmediate imm call) =
      some (fields [(1, bit call), (5, 5), (26, (imm >>> 2).toNat % 2 ^ 26)]) := by
    simp only [encodeInsn32]
    simp only [hguard, if_true]
  rw [encodeBytes_eq_of_encodeInsn32 _ _ hw, fields_branchImmediate, ofNat26_shift_eq]
  exact (arm8EncodeBytes_branchImmediate_gen call imm hl3).symm

/-- The `BranchConditional` word: `fields` and the L3 concatenation agree. -/
theorem fields_branchConditional (imm : BitVec 64) (cond : Nat) :
    fields [(8, 84), (19, (imm >>> 2).toNat % 2 ^ 19), (1, 0), (4, cond)] =
      arm8BranchCondWord (BitVec.ofNat 19 ((imm >>> 2).toNat % 2 ^ 19))
        (BitVec.ofNat 4 cond) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, arm8BranchCondWord]
  rw [ofNat_mod_setWidth 8, ofNat_mod_setWidth 19, ofNat_mod_setWidth 1,
    ofNat_mod_setWidth 4]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
  interval_cases i <;> simp

/-- The low 19 bits of `imm >>> 2` are `holWordExtract 19 20 2 imm`. -/
theorem ofNat19_shift_eq (imm : BitVec 64) :
    BitVec.ofNat 19 ((imm >>> 2).toNat % 2 ^ 19) = holWordExtract 19 20 2 imm := by
  simp only [holWordExtract]
  rw [holWordExtract_eq_setWidth 19 20 2 imm (by decide) (by decide) (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.mod_lt ((imm >>> 2).toNat) (by norm_num : 0 < 2 ^ 19))]
  rfl

/-- A `BranchConditional` encodes to the same four bytes on both sides. -/
theorem encodeBytes_branchConditional_of_guard (imm : BitVec 64) (cond : Nat)
    (hguard : (fitsSigned 21 imm && decide (imm.toNat % 4 = 0)) = true)
    (hl3 : BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 imm ++ BitVec.ofNat 2 0)) = imm) :
    encodeBytes (.branchConditional imm cond) =
      arm8Encode (.Branch (.BranchConditional (imm, BitVec.ofNat 4 cond))) := by
  have hw : encodeInsn32 (.branchConditional imm cond) =
      some (fields [(8, 84), (19, (imm >>> 2).toNat % 2 ^ 19), (1, 0), (4, cond)]) := by
    simp only [encodeInsn32]
    simp only [hguard, if_true]
  rw [encodeBytes_eq_of_encodeInsn32 _ _ hw, fields_branchConditional, ofNat19_shift_eq]
  rw [arm8Encode, arm8Encode_branchConditional imm (BitVec.ofNat 4 cond) hl3]

/-- The computable branch-immediate guard is exactly the L3 sign-extension guard
at 28 bits. -/
theorem branchGuard28_iff (imm : BitVec 64) :
    (fitsSigned 28 imm && decide (imm.toNat % 4 = 0)) = true ↔
      BitVec.signExtend 64 (BitVec.setWidth 28
        (holWordExtract 26 27 2 imm ++ BitVec.ofNat 2 0)) = imm := by
  have hx4 : (BitVec.setWidth 28
      (holWordExtract 26 27 2 imm ++ BitVec.ofNat 2 0)).toNat % 4 = 0 := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_append]
    simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.or_zero, Nat.zero_mod]
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 4 ∣ 2 ^ 28)]
    exact Nat.mul_mod_left _ _
  constructor
  · intro h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hf, ha⟩ := h
    rw [arm8BranchBits imm ha, BitVec.setWidth_setWidth_of_le imm (by decide)]
    exact ((fitsSigned_iff_signExtend 28 (by decide) (by decide) imm).mp hf).symm
  · intro h
    have hmod : imm.toNat % 4 = 0 := by
      rw [← h, BitVec.toNat_signExtend, BitVec.toNat_setWidth]
      have hlt : (BitVec.setWidth 28
          (holWordExtract 26 27 2 imm ++ BitVec.ofNat 2 0)).toNat < 2 ^ 64 := by
        have := BitVec.isLt (BitVec.setWidth 28
          (holWordExtract 26 27 2 imm ++ BitVec.ofNat 2 0))
        omega
      rw [Nat.mod_eq_of_lt hlt, Nat.add_mod, hx4]
      split <;> norm_num
    have hf : fitsSigned 28 imm = true := by
      rw [fitsSigned_iff_signExtend 28 (by decide) (by decide)]
      rw [← arm8BranchBits imm hmod]
      exact h.symm
    rw [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hf, hmod⟩

/-- The computable conditional-branch guard is exactly the L3 sign-extension
guard at 21 bits. -/
theorem branchGuard21_iff (imm : BitVec 64) :
    (fitsSigned 21 imm && decide (imm.toNat % 4 = 0)) = true ↔
      BitVec.signExtend 64 (BitVec.setWidth 21
        (holWordExtract 19 20 2 imm ++ BitVec.ofNat 2 0)) = imm := by
  have hx4 : (BitVec.setWidth 21
      (holWordExtract 19 20 2 imm ++ BitVec.ofNat 2 0)).toNat % 4 = 0 := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_append]
    simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.or_zero, Nat.zero_mod]
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 4 ∣ 2 ^ 21)]
    exact Nat.mul_mod_left _ _
  constructor
  · intro h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hf, ha⟩ := h
    rw [arm8BranchCondBits imm ha, BitVec.setWidth_setWidth_of_le imm (by decide)]
    exact ((fitsSigned_iff_signExtend 21 (by decide) (by decide) imm).mp hf).symm
  · intro h
    have hmod : imm.toNat % 4 = 0 := by
      rw [← h, BitVec.toNat_signExtend, BitVec.toNat_setWidth]
      have hlt : (BitVec.setWidth 21
          (holWordExtract 19 20 2 imm ++ BitVec.ofNat 2 0)).toNat < 2 ^ 64 := by
        have := BitVec.isLt (BitVec.setWidth 21
          (holWordExtract 19 20 2 imm ++ BitVec.ofNat 2 0))
        omega
      rw [Nat.mod_eq_of_lt hlt, Nat.add_mod, hx4]
      split <;> norm_num
    have hf : fitsSigned 21 imm = true := by
      rw [fitsSigned_iff_signExtend 21 (by decide) (by decide)]
      rw [← arm8BranchCondBits imm hmod]
      exact h.symm
    rw [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hf, hmod⟩

/-- When the L3 branch-immediate guard fails, `arm8Encode` is four zero bytes. -/
theorem arm8EncodeBytes_branchImmediate_bad (call : Bool) (imm : BitVec 64)
    (hl3 : ¬ (BitVec.signExtend 64 (BitVec.setWidth 28
      (holWordExtract 26 27 2 imm ++ BitVec.ofNat 2 0)) = imm)) :
    arm8Encode (.Branch (.BranchImmediate
        (imm, if call then .BranchType_CALL else .BranchType_JMP))) = [0, 0, 0, 0] := by
  have hc : (imm == BitVec.signExtend 64 (BitVec.setWidth 28
      (holWordExtract 26 27 2 imm ++ BitVec.ofNat 2 0))) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    exact hl3 h.symm
  cases call <;>
    simp only [arm8Encode, Encode, e_branch, hc, Bool.false_and, Bool.false_eq_true, if_false]

/-- When the L3 conditional-branch guard fails, `arm8Encode` is four zero bytes. -/
theorem arm8EncodeBytes_branchConditional_bad (imm : BitVec 64) (cd : BitVec 4)
    (hl3 : ¬ (BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 imm ++ BitVec.ofNat 2 0)) = imm)) :
    arm8Encode (.Branch (.BranchConditional (imm, cd))) = [0, 0, 0, 0] := by
  have hc : (imm == BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 imm ++ BitVec.ofNat 2 0))) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    exact hl3 h.symm
  simp only [arm8Encode, Encode, e_branch, hc, Bool.false_eq_true, if_false]

/-- A `BranchImmediate` encodes to the same four bytes on both sides, at every
offset (both encoders fall back to zero bytes outside the range). -/
theorem encodeBytes_branchImmediate (imm : BitVec 64) (call : Bool) :
    encodeBytes (.branchImmediate imm call) =
      arm8Encode (.Branch (.BranchImmediate
        (imm, if call then .BranchType_CALL else .BranchType_JMP))) := by
  by_cases hg : (fitsSigned 28 imm && decide (imm.toNat % 4 = 0)) = true
  · exact encodeBytes_branchImmediate_of_guard imm call hg ((branchGuard28_iff imm).mp hg)
  · have hl3 : ¬ (BitVec.signExtend 64 (BitVec.setWidth 28
        (holWordExtract 26 27 2 imm ++ BitVec.ofNat 2 0)) = imm) :=
      fun h => hg ((branchGuard28_iff imm).mpr h)
    have hgf : (fitsSigned 28 imm && decide (imm.toNat % 4 = 0)) = false := by
      cases h : (fitsSigned 28 imm && decide (imm.toNat % 4 = 0))
      · rfl
      · exact absurd h hg
    have hw : encodeInsn32 (.branchImmediate imm call) = none := by
      simp only [encodeInsn32]
      rw [hgf]
      simp
    rw [encodeBytes_eq_of_encodeInsn32_none _ hw]
    exact (arm8EncodeBytes_branchImmediate_bad call imm hl3).symm

/-- A `BranchConditional` encodes to the same four bytes on both sides, at every
offset. -/
theorem encodeBytes_branchConditional (imm : BitVec 64) (cond : Nat) :
    encodeBytes (.branchConditional imm cond) =
      arm8Encode (.Branch (.BranchConditional (imm, BitVec.ofNat 4 cond))) := by
  by_cases hg : (fitsSigned 21 imm && decide (imm.toNat % 4 = 0)) = true
  · exact encodeBytes_branchConditional_of_guard imm cond hg ((branchGuard21_iff imm).mp hg)
  · have hl3 : ¬ (BitVec.signExtend 64 (BitVec.setWidth 21
        (holWordExtract 19 20 2 imm ++ BitVec.ofNat 2 0)) = imm) :=
      fun h => hg ((branchGuard21_iff imm).mpr h)
    have hgf : (fitsSigned 21 imm && decide (imm.toNat % 4 = 0)) = false := by
      cases h : (fitsSigned 21 imm && decide (imm.toNat % 4 = 0))
      · rfl
      · exact absurd h hg
    have hw : encodeInsn32 (.branchConditional imm cond) = none := by
      simp only [encodeInsn32]
      rw [hgf]
      simp
    rw [encodeBytes_eq_of_encodeInsn32_none _ hw]
    exact (arm8EncodeBytes_branchConditional_bad imm (BitVec.ofNat 4 cond) hl3).symm

end Flapjack.Compiler.Encoders.Arm8.L3

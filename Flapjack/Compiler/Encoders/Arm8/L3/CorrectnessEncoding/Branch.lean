module

public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Loc

@[expose] public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# The `Jump` constructor of `encoder_correct arm8TargetL3`

`arm8_ast` lowers `Jump a` to the single `BranchImmediate (a, BranchType_JMP)`
instruction.  This module records that instruction's word, its `Encode`/`Decode`
inverse, its `Run` semantics at exception level zero, and the `Jump` case of the
L3 `encoder_correct` port.

The `BranchTo` clause masks the target's top byte only when `TBI0`/`TBI1` are
set; `arm8_ok` clears both, so the target reaches `PC` unchanged.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The word emitted for `BranchImmediate` with a `JMP`/`CALL` branch type:
HOL's `e_branch` term `(btype = CALL) ++ 00101 ++ imm26`. -/
def arm8BranchWord (imm26 : BitVec 26) : BitVec 32 :=
  BitVec.setWidth 32 (holV2w 1 [false] ++ BitVec.setWidth 31 ((BitVec.ofNat 5 5) ++ imm26))

/-- Every bit of the branch word: the low 26 bits are the branch immediate,
bits 26 and 28 carry the `00101` opcode, and the rest are zero. -/
theorem arm8BranchWord_getLsbD (imm26 : BitVec 26) (i : Nat) :
    (arm8BranchWord imm26).getLsbD i =
      if i < 26 then imm26.getLsbD i
      else if i = 26 ∨ i = 28 then true else false := by
  unfold arm8BranchWord
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat]
  by_cases h : i < 26
  · have h31 : i < 31 := by omega
    have h32 : i < 32 := by omega
    simp [h, h31, h32]
  · by_cases h2 : i = 26 ∨ i = 28
    · rw [ite_eq_right h, ite_eq_left h2]
      rcases h2 with rfl | rfl <;> (simp; try decide)
    · rw [ite_eq_right h, ite_eq_right h2]
      by_cases h3 : i < 32
      · have hb : i = 27 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
        rcases hb with rfl | rfl | rfl | rfl <;> (simp; try decide)
      · have hn26 : i ≠ 26 := by omega
        have hn28 : i ≠ 28 := by omega
        have h31 : ¬ i < 31 := by omega
        simp [h, h3, h31]

/-- Bit 26 of the branch word (lowest bit of the `00101` opcode). -/
theorem arm8BranchWord_bit26 (imm26 : BitVec 26) :
    (arm8BranchWord imm26).getLsbD 26 = true := by
  rw [arm8BranchWord_getLsbD]
  simp

/-- Bit 27 of the branch word. -/
theorem arm8BranchWord_bit27 (imm26 : BitVec 26) :
    (arm8BranchWord imm26).getLsbD 27 = false := by
  rw [arm8BranchWord_getLsbD]
  simp

/-- Bit 28 of the branch word. -/
theorem arm8BranchWord_bit28 (imm26 : BitVec 26) :
    (arm8BranchWord imm26).getLsbD 28 = true := by
  rw [arm8BranchWord_getLsbD]
  simp

/-- Bit 29 of the branch word. -/
theorem arm8BranchWord_bit29 (imm26 : BitVec 26) :
    (arm8BranchWord imm26).getLsbD 29 = false := by
  rw [arm8BranchWord_getLsbD]
  simp

/-- Bit 30 of the branch word. -/
theorem arm8BranchWord_bit30 (imm26 : BitVec 26) :
    (arm8BranchWord imm26).getLsbD 30 = false := by
  rw [arm8BranchWord_getLsbD]
  simp

/-- Bit 31 of the branch word: the `CALL` bit is clear for `JMP`. -/
theorem arm8BranchWord_bit31 (imm26 : BitVec 26) :
    (arm8BranchWord imm26).getLsbD 31 = false := by
  rw [arm8BranchWord_getLsbD]
  simp

/-- The branch immediate reassembles from the branch word's low 26 bits. -/
theorem arm8BranchWord_imm26 (imm26 : BitVec 26) :
    holV2w 26 [(arm8BranchWord imm26).getLsbD 25, (arm8BranchWord imm26).getLsbD 24,
      (arm8BranchWord imm26).getLsbD 23, (arm8BranchWord imm26).getLsbD 22,
      (arm8BranchWord imm26).getLsbD 21, (arm8BranchWord imm26).getLsbD 20,
      (arm8BranchWord imm26).getLsbD 19, (arm8BranchWord imm26).getLsbD 18,
      (arm8BranchWord imm26).getLsbD 17, (arm8BranchWord imm26).getLsbD 16,
      (arm8BranchWord imm26).getLsbD 15, (arm8BranchWord imm26).getLsbD 14,
      (arm8BranchWord imm26).getLsbD 13, (arm8BranchWord imm26).getLsbD 12,
      (arm8BranchWord imm26).getLsbD 11, (arm8BranchWord imm26).getLsbD 10,
      (arm8BranchWord imm26).getLsbD 9, (arm8BranchWord imm26).getLsbD 8,
      (arm8BranchWord imm26).getLsbD 7, (arm8BranchWord imm26).getLsbD 6,
      (arm8BranchWord imm26).getLsbD 5, (arm8BranchWord imm26).getLsbD 4,
      (arm8BranchWord imm26).getLsbD 3, (arm8BranchWord imm26).getLsbD 2,
      (arm8BranchWord imm26).getLsbD 1, (arm8BranchWord imm26).getLsbD 0] = imm26 := by
  have h : ([(arm8BranchWord imm26).getLsbD 25, (arm8BranchWord imm26).getLsbD 24,
      (arm8BranchWord imm26).getLsbD 23, (arm8BranchWord imm26).getLsbD 22,
      (arm8BranchWord imm26).getLsbD 21, (arm8BranchWord imm26).getLsbD 20,
      (arm8BranchWord imm26).getLsbD 19, (arm8BranchWord imm26).getLsbD 18,
      (arm8BranchWord imm26).getLsbD 17, (arm8BranchWord imm26).getLsbD 16,
      (arm8BranchWord imm26).getLsbD 15, (arm8BranchWord imm26).getLsbD 14,
      (arm8BranchWord imm26).getLsbD 13, (arm8BranchWord imm26).getLsbD 12,
      (arm8BranchWord imm26).getLsbD 11, (arm8BranchWord imm26).getLsbD 10,
      (arm8BranchWord imm26).getLsbD 9, (arm8BranchWord imm26).getLsbD 8,
      (arm8BranchWord imm26).getLsbD 7, (arm8BranchWord imm26).getLsbD 6,
      (arm8BranchWord imm26).getLsbD 5, (arm8BranchWord imm26).getLsbD 4,
      (arm8BranchWord imm26).getLsbD 3, (arm8BranchWord imm26).getLsbD 2,
      (arm8BranchWord imm26).getLsbD 1, (arm8BranchWord imm26).getLsbD 0] : List Bool) =
      holW2v (BitVec.setWidth 26 (arm8BranchWord imm26)) := by
    rw [show holW2v (BitVec.setWidth 26 (arm8BranchWord imm26)) =
      [(BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 25,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 24,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 23,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 22,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 21,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 20,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 19,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 18,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 17,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 16,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 15,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 14,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 13,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 12,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 11,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 10,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 9,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 8,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 7,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 6,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 5,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 4,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 3,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 2,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 1,
       (BitVec.setWidth 26 (arm8BranchWord imm26)).getLsbD 0] from rfl]
    simp
  rw [h, holV2w_holW2v]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, arm8BranchWord_getLsbD]
  simp [hi]

/-- `Encode` of a `JMP`-typed `BranchImmediate` in the signed 28-bit range is
the branch word. -/
theorem arm8Encode_branchImmediate (imm : BitVec 64)
    (h : BitVec.signExtend 64 (BitVec.setWidth 28
      (holWordExtract 26 27 2 imm ++ BitVec.ofNat 2 0)) = imm) :
    Encode (.Branch (.BranchImmediate (imm, .BranchType_JMP))) =
      MachineCode.ARM8 (arm8BranchWord (holWordExtract 26 27 2 imm)) := by
  have hc : (imm == BitVec.signExtend 64 (BitVec.setWidth 28
      (holWordExtract 26 27 2 imm ++ BitVec.ofNat 2 0))) = true := by
    rw [h]
    simp
  have hb : (BranchType.BranchType_JMP == BranchType.BranchType_CALL) = false := rfl
  simp only [Encode, e_branch, arm8BranchWord]
  rw [hc]
  simp only [hb, holV2w_one_false]
  rfl

/-- The rendered `Decode` inverts the branch word. -/
theorem arm8Decode_branchImmediate (imm26 : BitVec 26) :
    Decode (arm8BranchWord imm26) =
      .Branch (.BranchImmediate
        (BitVec.signExtend 64 (BitVec.setWidth 28 (imm26 ++ BitVec.ofNat 2 0)),
          .BranchType_JMP)) := by
  simp only [Decode, boolify32, arm8BranchWord_bit31, arm8BranchWord_bit30,
    arm8BranchWord_bit29, arm8BranchWord_bit28, arm8BranchWord_bit27,
    arm8BranchWord_bit26, holV2w_one_false,
    Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.and_true,
    Bool.and_false, Bool.false_eq_true, ite_true, ite_false]
  rw [arm8BranchWord_imm26 imm26]
  simp


/-- Low bits of a four-byte-aligned word are clear. -/
theorem arm8TestBit_mod_four_zero (x i : Nat) (h : x % 4 = 0) (hi : i < 2) :
    x.testBit i = false := by
  rw [← arm8TestBit_mod_four x i hi, h]
  simp

/-- The bits 27:2 of a word sit at positions `i - 2` after a two-bit shift. -/
theorem arm8TestBit_shift_mod28 (x i : Nat) (h2 : 2 ≤ i) (hi : i < 28) :
    (x >>> 2 % 67108864).testBit (i - 2) = x.testBit i := by
  have h := Nat.testBit_mod_two_pow (x >>> 2) 26 (i - 2)
  rw [show (2 : Nat) ^ 26 = 67108864 from rfl] at h
  rw [h]
  rw [Nat.testBit_shiftRight]
  have h3 : 2 + (i - 2) = i := by omega
  rw [h3]
  simp [show i - 2 < 26 from by omega]

/-- The 26-bit branch immediate followed by two zero bits reassembles to the
low 28 bits of a four-byte-aligned offset. -/
theorem arm8BranchBits (imm : BitVec 64) (hal : imm.toNat % 4 = 0) :
    holWordExtract 26 27 2 imm ++ BitVec.ofNat 2 0 = BitVec.setWidth 28 imm := by
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
  · have h26 : i - 2 < 26 := by omega
    have h64 : i - 2 < 64 := by omega
    rw [arm8TestBit_shift_mod28 imm.toNat i (by omega) (by omega)]
    simp [BitVec.getLsbD, h2, h26, h64, hi]

/-- The signed value of the low 28 bits of an offset in the signed 28-bit
branch range is the offset itself. -/
theorem arm8SignExtend28 (imm : BitVec 64)
    (hlo : -(2 ^ 27 : Int) ≤ imm.toInt) (hhi : imm.toInt ≤ 2 ^ 27 - 1) :
    BitVec.signExtend 64 (BitVec.setWidth 28 imm) = imm := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend, BitVec.toInt_setWidth, BitVec.toInt_eq_toNat_bmod]
  norm_num
  have hdvd64 : ((2 ^ 64 : ℕ) : ℤ) ∣ imm.toInt - ((imm.toNat : ℕ) : ℤ) := by
    rw [BitVec.toInt_eq_toNat_bmod]
    exact ((Int.bmod_eq_iff (by norm_num : 0 < 2 ^ 64)).mp rfl).2.2
  have hdvd28 : ((2 ^ 28 : ℕ) : ℤ) ∣ imm.toInt - ((imm.toNat : ℕ) : ℤ) := by
    obtain ⟨c, hc⟩ := hdvd64
    refine ⟨c * (2 ^ 36 : ℤ), ?_⟩
    rw [hc]
    push_cast
    omega
  have hb28 : 0 < (2 ^ 28 : ℕ) := by norm_num
  rw [← BitVec.toInt_eq_toNat_bmod]
  refine (Int.bmod_eq_iff hb28).mpr ⟨?_, ?_, hdvd28⟩
  · push_cast; omega
  · push_cast; omega

/-- The branch immediate reassembles to the offset when the offset is in the
signed 28-bit branch range and four-byte aligned. -/
theorem arm8BranchRoundtrip (imm : BitVec 64)
    (hlo : -(2 ^ 27 : Int) ≤ imm.toInt) (hhi : imm.toInt ≤ 2 ^ 27 - 1)
    (hal : imm.toNat % 4 = 0) :
    BitVec.signExtend 64 (BitVec.setWidth 28
      (holWordExtract 26 27 2 imm ++ BitVec.ofNat 2 0)) = imm := by
  rw [arm8BranchBits imm hal]
  exact arm8SignExtend28 imm hlo hhi

/-- `Jump` lowers to the single `BranchImmediate` instruction with branch type
`JMP`. -/
theorem arm8Ast_jump (target : BitVec 64) :
    arm8Ast (.jump target) =
      [.Branch (.BranchImmediate (target, .BranchType_JMP))] := rfl

/-- The four encoded bytes of the `JMP`-typed `BranchImmediate` instruction. -/
theorem arm8EncodeBytes_branchImmediate (imm : BitVec 64)
    (h : BitVec.signExtend 64 (BitVec.setWidth 28
      (holWordExtract 26 27 2 imm ++ BitVec.ofNat 2 0)) = imm) :
    arm8Encode (.Branch (.BranchImmediate (imm, .BranchType_JMP))) =
      [BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 imm) >>> 0).toNat),
       BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 imm) >>> 8).toNat),
       BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 imm) >>> 16).toNat),
       BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 imm) >>> 24).toNat)] := by
  rw [arm8Encode, arm8Encode_branchImmediate imm h]

/-- The encoded bytes of the `Jump` lowering. -/
theorem arm8Enc_jump (target : BitVec 64) :
    arm8Enc (.jump target) =
      arm8Encode (.Branch (.BranchImmediate (target, .BranchType_JMP))) := by
  simp [arm8Enc, arm8Ast_jump]

/-- The `Jump` lowering encodes to four bytes. -/
theorem arm8Enc_jump_length (target : BitVec 64) :
    (arm8Enc (.jump target)).length = 4 := by
  simp [arm8Enc, arm8Ast_jump, arm8Encode_length]

/-- `Run` of a `JMP`-typed `BranchImmediate` at exception level zero, with
`TBI0`/`TBI1` clear, sets the branch hint and the PC. -/
theorem arm8Run_branchImmediate (l : BitVec 64) (st : arm8_state)
    (hel : st.PSTATE.EL = (0 : BitVec 2))
    (htbi1 : st.TCR_EL1.TBI1 = false) (htbi0 : st.TCR_EL1.TBI0 = false) :
    Run (.Branch (.BranchImmediate (l, .BranchType_JMP))) st =
      { st with branch_hint := some .BranchType_JMP, PC := st.PC + l } := by
  simp [Run, «dfn'BranchImmediate», BranchTo, Hint_Branch, hel, htbi1, htbi0]

/-- `decide` of an arbitrary decision procedure of `p` that returns `true`
gives `p` (the offset bounds are decided by `Int.decLe`). -/
theorem arm8OfDecideTrue {p : Prop} (inst : Decidable p) (h : @decide p inst = true) : p := by
  cases inst with
  | isTrue hp => exact hp
  | isFalse _ => exact Bool.noConfusion h

/-- The `jump` offset window of `arm8ConfigL3` gives the encoder's 28-bit
branch range and the four-byte alignment. -/
theorem arm8JumpOk_of_asm (target : BitVec 64)
    (h : asmOkExact (.jump target) arm8ConfigL3 = true) :
    (-134217728 : Int) ≤ target.toInt ∧ target.toInt ≤ 134217727 ∧
      target.toNat % 4 = 0 := by
  simp only [asmOkExact, arm8ConfigL3, asmJumpOffsetOkExact, asmOffsetOkExact,
    Bool.and_eq_true] at h
  obtain ⟨⟨hlo, hhi⟩, hal⟩ := h
  have hlo' := arm8OfDecideTrue _ hlo
  have hhi' := arm8OfDecideTrue _ hhi
  have hmod : target.toNat % 4 = 0 := by simpa [asmAligned] using hal
  refine ⟨hlo', ?_, hmod⟩
  simpa using hhi'

/-- One `NextStateARM8` step on the emitted `JMP` branch word sets the branch
hint and moves `PC` to `PC + offset`. -/
theorem arm8Next_branchImmediate (ms : arm8_state) (l : BitVec 64)
    (hround : BitVec.signExtend 64 (BitVec.setWidth 28
      (holWordExtract 26 27 2 l ++ BitVec.ofNat 2 0)) = l)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC =
      BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 l) >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) =
      BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 l) >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) =
      BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 l) >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) =
      BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 l) >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (htbi1 : ms.TCR_EL1.TBI1 = false) (htbi0 : ms.TCR_EL1.TBI0 = false) :
    NextStateARM8 ms =
      some { ms with branch_hint := some .BranchType_JMP, PC := ms.PC + l } := by
  let i : instruction := .Branch (.BranchImmediate (l, .BranchType_JMP))
  have hdec : Decode (arm8BranchWord (holWordExtract 26 27 2 l)) = i := by
    dsimp only [i]
    rw [arm8Decode_branchImmediate, hround]
  have hrun : Run i { ms with branch_hint := none } =
      { ms with branch_hint := some .BranchType_JMP, PC := ms.PC + l } := by
    dsimp only [i]
    exact arm8Run_branchImmediate l { ms with branch_hint := none }
      (by simpa using hel) (by simpa using htbi1) (by simpa using htbi0)
  have hfetch : Fetch { ms with branch_hint := none } =
      (arm8BranchWord (holWordExtract 26 27 2 l), { ms with branch_hint := none }) :=
    arm8Fetch_word { ms with branch_hint := none } _ h0 h1 h2 h3 hal he0 hel
  simp only [NextStateARM8, Next]
  rw [hfetch]
  simp only [hdec]
  rw [hrun]
  simp [hexc0]

/-- `arm8Next` on the emitted `JMP` branch word. -/
theorem arm8Next_branchImmediate' (ms : arm8_state) (l : BitVec 64)
    (hround : BitVec.signExtend 64 (BitVec.setWidth 28
      (holWordExtract 26 27 2 l ++ BitVec.ofNat 2 0)) = l)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC =
      BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 l) >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) =
      BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 l) >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) =
      BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 l) >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) =
      BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 l) >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (htbi1 : ms.TCR_EL1.TBI1 = false) (htbi0 : ms.TCR_EL1.TBI0 = false) :
    arm8Next ms =
      { ms with branch_hint := some .BranchType_JMP, PC := ms.PC + l } := by
  unfold arm8Next
  rw [arm8Next_branchImmediate ms l hround hexc0 h0 h1 h2 h3 hal he0 hel htbi1 htbi0]
  rfl

/-- The `Jump` constructor of `encoder_correct arm8TargetL3`: the single
`BranchImmediate` instruction sets the branch hint and moves `PC` to
`PC + target`, without advancing it by four. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_jump (target : BitVec 64) (s1 s2 : AsmState 64)
    (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.jump target) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.jump target) s1 s2 ms := by
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
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.jump target)) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hs.1, fun n hn => (hmem _ (hdom n hn)).symm⟩
  have hlen : (arm8Enc (.jump target)).length = 4 := arm8Enc_jump_length target
  have henc : arm8Enc (.jump target) =
      [BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 target) >>> 0).toNat),
       BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 target) >>> 8).toNat),
       BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 target) >>> 16).toNat),
       BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 target) >>> 24).toNat)] := by
    rw [arm8Enc_jump, arm8EncodeBytes_branchImmediate target hround]
  have hb0 : ms.MEM ms.PC =
      BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 target) >>> 0).toNat) := by
    have := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; norm_num)
    rw [henc] at this
    simpa using this
  have hb1 : ms.MEM (ms.PC + 1) =
      BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 target) >>> 8).toNat) := by
    have := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; norm_num)
    rw [henc] at this
    simpa using this
  have hb2 : ms.MEM (ms.PC + 2) =
      BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 target) >>> 16).toNat) := by
    have := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; norm_num)
    rw [henc] at this
    simpa using this
  have hb3 : ms.MEM (ms.PC + 3) =
      BitVec.ofNat 8 ((arm8BranchWord (holWordExtract 26 27 2 target) >>> 24).toNat) := by
    have := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; norm_num)
    rw [henc] at this
    simpa using this
  have hn := arm8Next_branchImmediate' ms target hround hexc0 hb0 hb1 hb2 hb3 hal he0 hel
    htbi1 htbi0
  have hs2 : s2 = updPc (s1.pc + target) s1 := by
    have hupd := hs.2.2.2.2.1
    simp only [arm8ConfigL3] at hupd
    rw [hlen] at hupd
    rw [← hupd]
    simp [asmUpd, jumpToOffset, updPc]
  have hs2dom : s2.memDomain = s1.memDomain := by rw [hs2]; rfl
  have hal2 : holAligned 2 (ms.PC + target) = true := by
    have ht : holAligned 2 target = true := by
      rw [holAligned_iff]
      norm_num
      exact hmod
    rw [(alignedAddSub 2 ms.PC target ht).1, halign]
  have hokPost : arm8Ok { ms with branch_hint := some .BranchType_JMP, PC := ms.PC + target } = true := by
    simp [arm8Ok, hel, he0, hsa0, htbi1, htbi0, hexc0]
    exact hal2
  have hq : targetStateRel arm8TargetL3 s2
      { ms with branch_hint := some .BranchType_JMP, PC := ms.PC + target } := by
    refine ⟨hokPost, ?_, ?_, ?_, ?_⟩
    · simp only [arm8TargetL3_getPc]
      rw [hs2, hpc]
      simp [updPc]
    · intro a ha
      simp only [arm8TargetL3_getByte]
      have ha' : s1.memDomain a := by rw [← hs2dom]; exact ha
      rw [hs2]
      exact hmem a ha'
    · intro k hk
      simp only [arm8TargetL3_getReg]
      rw [hs2]
      exact hreg k hk
    · intro k hk
      simp [arm8ConfigL3] at hk
  refine ⟨0, ?_⟩
  intro env henv
  constructor
  · change targetStateRel arm8TargetL3 s2 (env 0 (arm8Next ms))
    rw [hn]
    have hagree : Arm8L3Agree s2.memDomain
        (env 0 { ms with branch_hint := some .BranchType_JMP, PC := ms.PC + target })
        { ms with branch_hint := some .BranchType_JMP, PC := ms.PC + target } := by
      rw [← arm8Proj_eq_iff]
      have hh := henv 0 { ms with branch_hint := some .BranchType_JMP, PC := ms.PC + target }
      rw [hs2dom]
      exact hh
    exact targetStateRel_congr hagree hq
  · refine ⟨fun x _ => ?_, trivial⟩
    rw [hn]

end Flapjack.Compiler.Encoders.Arm8.L3

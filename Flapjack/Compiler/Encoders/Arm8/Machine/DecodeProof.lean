/-
Copyright (c) 2025 Flapjack contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.IntervalCases
import Flapjack.Compiler.Encoders.Arm8.Machine.ExecuteProof

/-!
# ARMv8 decoder inverses

This module records the first kernel-checked decoder inverse for the closed
ARMv8 model.  The full per-instruction inverse is future work; the existing
`decodeInsn`/`encodeInsn` bridge is deliberately stated with explicit
hypotheses on the fetched word.
-/

namespace Flapjack.Compiler.Encoders.Arm8

/-- A 32-bit `ofNat` is the width-`n` truncation zero-extended to 32 bits. -/
theorem ofNat_mod_self32 (x n : Nat) :
    BitVec.ofNat 32 (x % 2 ^ n) = (BitVec.ofNat n x).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth]

/-- `part` of a word is the `toNat` of the corresponding width-typed slice. -/
theorem part_eq_of_setWidth {w : BitVec 32} {lo len : Nat} {x : BitVec len}
    (h : (w >>> lo).setWidth len = x) : part w lo len = x.toNat := by
  unfold part
  rw [h]

/-- The 32-bit encoding of `noOp` decodes back to `noOp`. -/
theorem decode_encode_noOp32 :
    decodeInsn32 (fields [(24, 0xD50320), (3, 0), (5, 31)]) = some .noOp := by
  decide

/-- The 64-bit carrier encoding of `noOp`. -/
theorem encodeInsn_noOp :
    encodeInsn .noOp = some ((fields [(24, 0xD50320), (3, 0), (5, 31)]).setWidth 64) := rfl

/-- The 32-bit word of a `moveWide` instruction, over width-typed atoms. -/
def moveWideWord (op : BitVec 2) (hw : BitVec 2) (imm : BitVec 16) (rd : BitVec 5) : BitVec 32 :=
  ((((((1 : BitVec 32) <<< 2 ||| op.setWidth 32) <<< 6 ||| (37 : BitVec 32)) <<< 2 |||
      hw.setWidth 32) <<< 16 ||| imm.setWidth 32) <<< 5 ||| rd.setWidth 32)

/-- The `fields` composition of a `moveWide` is the width-typed word. -/
theorem fields_moveWide (op hw imm16 rd : Nat) :
    fields [(1, 1), (2, op), (6, 0b100101), (2, hw), (16, imm16), (5, rd)]
      = moveWideWord (BitVec.ofNat 2 op) (BitVec.ofNat 2 hw)
          (BitVec.ofNat 16 imm16) (BitVec.ofNat 5 rd) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed `moveWide` word. -/
theorem decode_moveWide_word (opB : BitVec 2) (hwB : BitVec 2) (immB : BitVec 16)
    (rdB : BitVec 5) (h0 : opB = 0 ∨ opB = 2 ∨ opB = 3) :
    decodeInsn32 (moveWideWord opB hwB immB rdB)
      = some (.moveWide (if opB = 0 then .n else if opB = 2 then .z else .k)
          hwB.toNat immB.toNat rdB.toNat) := by
  simp only [decodeInsn32]
  have hK : bitMatches (moveWideWord opB hwB immB rdB) 0x9F800000 0x92800000 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [moveWideWord]
    simp
    interval_cases i <;> simp
  have c1 : bitMatches (moveWideWord opB hwB immB rdB) 0xFFFFFFFF 0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun w : BitVec 32 => w.getLsbD 24) h
    simp only [moveWideWord] at hb
    simp at hb
  simp only [c1, hK]
  have f1 : part (moveWideWord opB hwB immB rdB) 29 2 = opB.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [moveWideWord]
    simp
    interval_cases i <;> simp
  have f2 : part (moveWideWord opB hwB immB rdB) 21 2 = hwB.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [moveWideWord]
    simp
    interval_cases i <;> simp
  have f3 : part (moveWideWord opB hwB immB rdB) 5 16 = immB.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [moveWideWord]
    simp
    interval_cases i <;> simp
  have f4 : part (moveWideWord opB hwB immB rdB) 0 5 = rdB.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [moveWideWord]
    simp
  simp only [f1, f2, f3, f4]
  rcases h0 with rfl | rfl | rfl <;> rfl

/-- `moveWide` survives a round trip through `encodeInsn32`/`decodeInsn32`. -/
theorem decode_encode_moveWide32 (op : MoveWideOp) (hw imm16 rd : Nat)
    (hh : hw < 4) (hi : imm16 < 65536) (hr : rd < 32) :
    decodeInsn32 (fields [(1, 1), (2, moveWideOpBits op), (6, 0b100101),
      (2, hw), (16, imm16), (5, rd)]) = some (.moveWide op hw imm16 rd) := by
  rw [fields_moveWide (moveWideOpBits op) hw imm16 rd]
  rw [decode_moveWide_word (BitVec.ofNat 2 (moveWideOpBits op))
    (BitVec.ofNat 2 hw) (BitVec.ofNat 16 imm16) (BitVec.ofNat 5 rd)
    (by cases op <;> decide)]
  cases op <;> simp [moveWideOpBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hh,
    Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hr]

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form. -/
theorem decode_encode_moveWide (op : MoveWideOp) (hw imm16 rd : Nat)
    (hh : hw < 4) (hi : imm16 < 65536) (hr : rd < 32) :
    decodeInsn ((fields [(1, 1), (2, moveWideOpBits op), (6, 0b100101),
      (2, hw), (16, imm16), (5, rd)]).setWidth 64) = some (.moveWide op hw imm16 rd) := by
  rw [show decodeInsn ((fields [(1, 1), (2, moveWideOpBits op), (6, 0b100101),
      (2, hw), (16, imm16), (5, rd)]).setWidth 64)
      = decodeInsn32 (fields [(1, 1), (2, moveWideOpBits op), (6, 0b100101),
          (2, hw), (16, imm16), (5, rd)]) by
    simp [decodeInsn]]
  exact decode_encode_moveWide32 op hw imm16 rd hh hi hr

/-- The 64-bit carrier word emitted for `moveWide`. -/
theorem encodeInsn_moveWide (op : MoveWideOp) (hw imm16 rd : Nat) :
    encodeInsn (.moveWide op hw imm16 rd) =
      some ((fields [(1, 1), (2, moveWideOpBits op), (6, 0b100101),
        (2, hw), (16, imm16), (5, rd)]).setWidth 64) := rfl

/-- `decodeInsn` inverts `encodeInsn` on `moveWide`. -/
theorem decode_encode_moveWideInsn (op : MoveWideOp) (hw imm16 rd : Nat)
    (hh : hw < 4) (hi : imm16 < 65536) (hr : rd < 32) :
    decodeInsn ((encodeInsn (.moveWide op hw imm16 rd)).getD 0)
      = some (.moveWide op hw imm16 rd) := by
  rw [encodeInsn_moveWide, Option.getD_some]
  exact decode_encode_moveWide op hw imm16 rd hh hi hr

/-- One machine step executes a `moveWide` instruction whose bytes are at the
PC. -/
theorem arm8Next_moveWide (s : Arm8State) (d : BitVec 64 → Prop)
    (op : MoveWideOp) (hw imm16 rd : Nat)
    (hh : hw < 4) (hi : imm16 < 65536) (hr : rd < 32)
    (hbytes : bytesInMemoryHOL s.pc (encodeBytes (.moveWide op hw imm16 rd)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 } (.moveWide op hw imm16 rd) := by
  rw [arm8Next_encodeBytes s (.moveWide op hw imm16 rd)
    ((fields [(1, 1), (2, moveWideOpBits op), (6, 0b100101),
      (2, hw), (16, imm16), (5, rd)]).setWidth 64) d
    (encodeInsn_moveWide op hw imm16 rd)
    (decode_encode_moveWideInsn op hw imm16 rd hh hi hr) hbytes]

end Flapjack.Compiler.Encoders.Arm8

import Mathlib.Tactic
import Flapjack.Compiler.Encoders.X64.Machine.Bytes

/-!
# Decoder inverses for the emitted memory-operand forms

The x86-64 backend emits loads, stores and `lea` with a base register and a
displacement.  `e_ModRM` writes a `ModRM` byte whose `mod` field records the
displacement width, adds a `SIB` byte when the base register is RSP/R12, and
appends one or four displacement bytes.  This module proves that the closed
decoder recovers the source instruction from those bytes.
-/

set_option maxHeartbeats 4000000

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm

/-! ## Encoded byte layouts -/

/-- The encoded byte list of `movRM .z64`, as an abbreviation so proofs can
unfold it without repeating the literal. -/
abbrev movRMZ64Bytes (dst base : Nat) (disp : BitVec 64) : List (BitVec 8) :=
  [byte (72 + (if 8 ≤ dst then 4 else 0) + (if 8 ≤ base then 1 else 0)),
   byte 0x8B,
   byte ((if disp = 0 ∧ base % 8 ≠ 5 then 0
          else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
         8 * (dst % 8) + base % 8)] ++
  (if base % 8 = 4 then [byte 0x24] else []) ++
  (if disp = 0 ∧ base % 8 ≠ 5 then []
   else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat]
   else [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])

/-- The encoded bytes of `movRM .z64`: a REX.W byte, the `8B` opcode, the
`ModRM` byte, an optional `SIB` byte for an RSP/R12 base, and the
displacement. -/
theorem encodeInsn_movRM_z64_bytes (dst base : Nat) (hd : dst < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    encodeInsn (.movRM .z64 dst base disp) =
      [byte (72 + (if 8 ≤ dst then 4 else 0) + (if 8 ≤ base then 1 else 0)),
       byte 0x8B,
       byte ((if disp = 0 ∧ base % 8 ≠ 5 then 0
              else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
             8 * (dst % 8) + base % 8)] ++
      (if base % 8 = 4 then [byte 0x24] else []) ++
      (if disp = 0 ∧ base % 8 ≠ 5 then []
       else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat]
       else [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)]) := by
  interval_cases dst <;> interval_cases base
  all_goals
    simp only [encodeInsn, eGenRmReg, eModRM, eOpsize, rexPrefix, mkRex, eImm8_32, eImm8, eImm32, byte, modField]
    simp only [Nat.reduceMod, Nat.reduceMul, Nat.reduceDiv]
    simp
    by_cases h0 : disp = 0
    · subst h0
      simp
    · have h0' : disp ≠ 0#64 := h0
      by_cases h8 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
      · simp [h0', h8]
      · have h32 : -2147483648 ≤ disp.toInt ∧ disp.toInt ≤ 2147483647 := by omega
        simp [h0', h8, h32]

/-- `encodeInsn (.movRM .z64 dst base disp)` is `movRMZ64Bytes dst base disp`. -/
theorem encodeInsn_movRM_z64 (dst base : Nat) (hd : dst < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    encodeInsn (.movRM .z64 dst base disp) = movRMZ64Bytes dst base disp :=
  encodeInsn_movRM_z64_bytes dst base hd hb disp hlo hhi

open Flapjack Compiler.Encoders.Asm in
/-- `parseRM` recovers a `[base + disp]` memory operand from any encoding whose
bytes 2.. match the emitted `mov`-memory layout, for any two-byte prefix. -/
theorem parseRM_rmBase_z64 (b0 b1 : BitVec 8) (reg base : Nat) (hr : reg < 8) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    parseRM (byteListReader
      ([b0, b1,
        byte ((if disp = 0 ∧ base % 8 ≠ 5 then 0
               else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
              8 * reg + base % 8)] ++
        (if base % 8 = 4 then [byte 0x24] else []) ++
        (if disp = 0 ∧ base % 8 ≠ 5 then []
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat]
         else [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536),
           byte (disp.toNat / 16777216)]))) 2 (decide (8 ≤ base)) =
      some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0
                         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
             regBits := reg,
             rm := .zm none (.regBase base) disp,
             len := (if base % 8 = 4 then 1 else 0) +
                    (if disp = 0 ∧ base % 8 ≠ 5 then 1
                     else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
  have hb8 : base % 8 < 8 := by omega
  have hhi' : (if 8 ≤ base then 8 else 0) = (if decide (8 ≤ base) then 8 else 0) := by
    by_cases h : 8 ≤ base <;> simp [h]
  have h1_lt : 8 * (reg) + 4 < 256 := by omega
  have h2_lt : 64 + 8 * (reg) + 4 < 256 := by omega
  have h3_lt : 128 + 8 * (reg) + 4 < 256 := by omega
  have hb0_lt : 8 * (reg) + base % 8 < 256 := by omega
  have hb1_lt : 64 + 8 * (reg) + base % 8 < 256 := by omega
  have hb2_lt : 128 + 8 * (reg) + base % 8 < 256 := by omega
  by_cases hsib : base % 8 = 4
  · have hbase : base = 4 ∨ base = 12 := by omega
    have hb4 : (if 8 ≤ base then 8 else 0) + 4 = base := by
      rcases hbase with h | h <;> subst h <;> decide
    by_cases hz : disp = 0
    · have hcond : disp = 0 ∧ base % 8 ≠ 5 := ⟨hz, by omega⟩
      simp only [if_pos hcond, if_pos hsib]
      simp only [hsib]
      simp only [Nat.zero_add, List.append_nil]
      change parseRM (byteListReader [b0,
          b1, byte (8 * (reg) + 4), byte 0x24]) 2 (decide (8 ≤ base)) =
        some { modBits := 0, regBits := reg, rm := .zm none (.regBase base) disp, len := 2 }
      have hm : (byteListReader [b0,
          b1, byte (8 * (reg) + 4), byte 0x24] 2).toNat = 8 * (reg) + 4 := by
        simp [byteListReader, byte, h1_lt]
      have hsibm : (byteListReader [b0,
          b1, byte (8 * (reg) + 4), byte 0x24] 3).toNat = 36 := by
        simp [byteListReader, byte]
      have hs := parseRM_sib0 (byteListReader [b0,
          b1, byte (8 * (reg) + 4), byte 0x24]) 2 (reg)
          (if 8 ≤ base then 8 else 0) (decide (8 ≤ base)) hm hr hsibm hhi'
      rw [hb4] at hs
      rw [hs, hz]
    · by_cases h8 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
      · have hcond : ¬ (disp = 0 ∧ base % 8 ≠ 5) := by intro hc; exact hz hc.1
        simp only [if_neg hcond, if_pos h8, if_pos hsib]
        simp only [hsib]
        change parseRM (byteListReader [b0,
            b1, byte (64 + 8 * (reg) + 4), byte 0x24, byte disp.toNat]) 2 (decide (8 ≤ base)) =
          some { modBits := 1, regBits := reg, rm := .zm none (.regBase base) disp, len := 3 }
        have hm : (byteListReader [b0,
            b1, byte (64 + 8 * (reg) + 4), byte 0x24, byte disp.toNat] 2).toNat
            = 64 + 8 * (reg) + 4 := by
          simp [byteListReader, byte, h2_lt]
        have hsibm : (byteListReader [b0,
            b1, byte (64 + 8 * (reg) + 4), byte 0x24, byte disp.toNat] 3).toNat = 36 := by
          simp [byteListReader, byte]
        have hdisp : (byteListReader [b0,
            b1, byte (64 + 8 * (reg) + 4), byte 0x24, byte disp.toNat] 4) = byte disp.toNat := by
          simp [byteListReader]
        have hd4 : imm8 (byteListReader [b0,
            b1, byte (64 + 8 * (reg) + 4), byte 0x24, byte disp.toNat]) 4 = disp :=
          imm8_at disp 4 _ hdisp h8.1 (by omega)
        have hs := parseRM_sib1 (byteListReader [b0,
            b1, byte (64 + 8 * (reg) + 4), byte 0x24, byte disp.toNat]) 2 (reg)
            (if 8 ≤ base then 8 else 0) (decide (8 ≤ base)) hm hr hsibm hhi'
        rw [hb4] at hs
        rw [hs, hd4]
      · have hcond : ¬ (disp = 0 ∧ base % 8 ≠ 5) := by intro hc; exact hz hc.1
        simp only [if_neg hcond, if_neg h8, if_pos hsib]
        simp only [hsib]
        change parseRM (byteListReader [b0,
            b1, byte (128 + 8 * (reg) + 4), byte 0x24,
            byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)]) 2 (decide (8 ≤ base)) =
          some { modBits := 2, regBits := reg, rm := .zm none (.regBase base) disp, len := 6 }
        have hm : (byteListReader [b0,
            b1, byte (128 + 8 * (reg) + 4), byte 0x24,
            byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)] 2).toNat
            = 128 + 8 * (reg) + 4 := by
          simp [byteListReader, byte, h3_lt]
        have hsibm : (byteListReader [b0,
            b1, byte (128 + 8 * (reg) + 4), byte 0x24,
            byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)] 3).toNat = 36 := by
          simp [byteListReader, byte]
        have hd : ∀ j, j < 4 → (byteListReader [b0,
            b1, byte (128 + 8 * (reg) + 4), byte 0x24,
            byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)] (4 + j))
            = byte (disp.toNat / 2^(8*j)) := by
          intro j hj
          interval_cases j <;> simp [byteListReader]
        have hd4 : imm32 (byteListReader [b0,
            b1, byte (128 + 8 * (reg) + 4), byte 0x24,
            byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)]) 4 = disp :=
          imm32_eImm32_at disp 4 _ hd hlo hhi
        have hs := parseRM_sib2 (byteListReader [b0,
            b1, byte (128 + 8 * (reg) + 4), byte 0x24,
            byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)]) 2 (reg)
            (if 8 ≤ base then 8 else 0) (decide (8 ≤ base)) hm hr hsibm hhi'
        rw [hb4] at hs
        rw [hs, hd4]
  · have hb4 : (if 8 ≤ base then 8 else 0) + base % 8 = base := by
      have : base = base % 8 + 8 * (base / 8) := by omega
      by_cases h : 8 ≤ base <;> simp [h] <;> omega
    by_cases h0 : disp = 0 ∧ base % 8 ≠ 5
    · simp only [if_pos h0, if_neg hsib]
      simp only [Nat.zero_add, List.append_nil]
      change parseRM (byteListReader [b0,
          b1, byte (8 * (reg) + base % 8)]) 2 (decide (8 ≤ base)) =
        some { modBits := 0, regBits := reg, rm := .zm none (.regBase base) disp, len := 1 }
      have hm : (byteListReader [b0,
          b1, byte (8 * (reg) + base % 8)] 2).toNat = 8 * (reg) + base % 8 := by
        simp [byteListReader, byte, hb0_lt]
      have hs := parseRM_base0 (byteListReader [b0,
          b1, byte (8 * (reg) + base % 8)]) 2 (reg) (base % 8)
          (if 8 ≤ base then 8 else 0) (decide (8 ≤ base)) hm hr hb8 (by omega) h0.2 hhi'
      rw [hb4] at hs
      rw [hs, h0.1]
    · by_cases h8 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
      · simp only [if_neg h0, if_pos h8, if_neg hsib]
        change parseRM (byteListReader [b0,
            b1, byte (64 + 8 * (reg) + base % 8), byte disp.toNat]) 2 (decide (8 ≤ base)) =
          some { modBits := 1, regBits := reg, rm := .zm none (.regBase base) disp, len := 2 }
        have hm : (byteListReader [b0,
            b1, byte (64 + 8 * (reg) + base % 8), byte disp.toNat] 2).toNat
            = 64 + 8 * (reg) + base % 8 := by
          simp [byteListReader, byte, hb1_lt]
        have hdisp : (byteListReader [b0,
            b1, byte (64 + 8 * (reg) + base % 8), byte disp.toNat] 3) = byte disp.toNat := by
          simp [byteListReader]
        have hd3 : imm8 (byteListReader [b0,
            b1, byte (64 + 8 * (reg) + base % 8), byte disp.toNat]) 3 = disp :=
          imm8_at disp 3 _ hdisp h8.1 (by omega)
        have hs := parseRM_base1 (byteListReader [b0,
            b1, byte (64 + 8 * (reg) + base % 8), byte disp.toNat]) 2 (reg) (base % 8)
            (if 8 ≤ base then 8 else 0) (decide (8 ≤ base)) hm hr hb8 (by omega) hhi'
        rw [hb4] at hs
        rw [hs, hd3]
      · simp only [if_neg h0, if_neg h8, if_neg hsib]
        change parseRM (byteListReader [b0,
            b1, byte (128 + 8 * (reg) + base % 8),
            byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)]) 2 (decide (8 ≤ base)) =
          some { modBits := 2, regBits := reg, rm := .zm none (.regBase base) disp, len := 5 }
        have hm : (byteListReader [b0,
            b1, byte (128 + 8 * (reg) + base % 8),
            byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)] 2).toNat
            = 128 + 8 * (reg) + base % 8 := by
          simp [byteListReader, byte, hb2_lt]
        have hd : ∀ j, j < 4 → (byteListReader [b0,
            b1, byte (128 + 8 * (reg) + base % 8),
            byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)] (3 + j))
            = byte (disp.toNat / 2^(8*j)) := by
          intro j hj
          interval_cases j <;> simp [byteListReader]
        have hd3 : imm32 (byteListReader [b0,
            b1, byte (128 + 8 * (reg) + base % 8),
            byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)]) 3 = disp :=
          imm32_eImm32_at disp 3 _ hd hlo hhi
        have hs := parseRM_base2 (byteListReader [b0,
            b1, byte (128 + 8 * (reg) + base % 8),
            byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)]) 2 (reg) (base % 8)
            (if 8 ≤ base then 8 else 0) (decide (8 ≤ base)) hm hr hb8 (by omega) hhi'
        rw [hb4] at hs
        rw [hs, hd3]


/-- `parseRM` recovers the `movRM .z64` memory operand from its encoding. -/
theorem parseRM_movRM_z64 (dst base : Nat) (hd : dst < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    parseRM (byteListReader (encodeInsn (.movRM .z64 dst base disp))) 2 (decide (8 ≤ base)) =
      some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0
                         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
             regBits := dst % 8,
             rm := .zm none (.regBase base) disp,
             len := (if base % 8 = 4 then 1 else 0) +
                    (if disp = 0 ∧ base % 8 ≠ 5 then 1
                     else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
  rw [encodeInsn_movRM_z64 dst base hd hb disp hlo hhi]
  exact parseRM_rmBase_z64 _ (byte 0x8B) (dst % 8) base (by omega) hb disp hlo hhi

theorem decode_movRM_z64 (dst base : Nat) (hd : dst < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    decode (byteListReader (encodeInsn (.movRM .z64 dst base disp))) =
      some (.movRM .z64 dst base disp,
        2 + (if base % 8 = 4 then 1 else 0) +
          (if disp = 0 ∧ base % 8 ≠ 5 then 1
           else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
  rw [encodeInsn_movRM_z64 dst base hd hb disp hlo hhi]
  have hpm := parseRM_movRM_z64 dst base hd hb disp hlo hhi
  rw [encodeInsn_movRM_z64 dst base hd hb disp hlo hhi] at hpm
  set L : List (BitVec 8) := movRMZ64Bytes dst base disp with hL
  have hb0 : (byteListReader L 0).toNat =
      72 + (if 8 ≤ dst then 4 else 0) + (if 8 ≤ base then 1 else 0) := by
    rw [hL]
    have hlt : 72 + (if 8 ≤ dst then 4 else 0) + (if 8 ≤ base then 1 else 0) < 256 := by
      split <;> split <;> omega
    simp [movRMZ64Bytes, byteListReader, byte, hlt]
  have hb1 : (byteListReader L 1).toNat = 0x8B := by
    rw [hL]; rfl
  by_cases hd8 : 8 ≤ dst <;> by_cases hb8 : 8 ≤ base
  all_goals
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [hd8, hb8, if_true, if_false] at hpm ⊢
    simp only [decodeRex, hb1]
    simp only [Nat.reduceAdd, Nat.reduceMod, decide_eq_true_eq, Nat.reduceLeDiff]
    simp
    simp only [decide_true, decide_false] at hpm
    rw [hpm]
    simp only [baseOfRM]
    have hmod : (if disp = 0 ∧ base % 8 ≠ 5 then 0
        else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2) ≠ 3 := by
      intro h
      by_cases h1 : disp = 0 ∧ base % 8 ≠ 5
      · rw [if_pos h1] at h; omega
      · rw [if_neg h1] at h
        by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
        · rw [if_pos h2] at h; omega
        · rw [if_neg h2] at h; omega
    rw [if_neg hmod]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · simp only [X64Insn.movRM.injEq, true_and, and_true]
      first
      | (rw [Nat.mod_eq_sub_mod hd8, Nat.mod_eq_of_lt (by omega)]; try omega)
      | (rw [Nat.mod_eq_of_lt (by omega)]; try omega)
    · by_cases h1 : disp = 0 ∧ base % 8 ≠ 5 <;>
        by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 <;> simp [h1, h2] <;> omega


end Flapjack.Compiler.Encoders.X64

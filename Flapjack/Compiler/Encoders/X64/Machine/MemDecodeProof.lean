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

/-- The encoded byte list of `movRM .z32`. -/
abbrev movRMZ32Bytes (dst base : Nat) (disp : BitVec 64) : List (BitVec 8) :=
  (if 8 ≤ dst ∨ 8 ≤ base then
    [byte (64 + (if 8 ≤ dst then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) ++
  [byte 0x8B,
   byte ((if disp = 0 ∧ base % 8 ≠ 5 then 0
          else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
         8 * (dst % 8) + base % 8)] ++
  (if base % 8 = 4 then [byte 0x24] else []) ++
  (if disp = 0 ∧ base % 8 ≠ 5 then []
   else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat]
   else [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])

/-- The encoded byte list of `movMR .z64`. -/
abbrev movMRZ64Bytes (src base : Nat) (disp : BitVec 64) : List (BitVec 8) :=
  [byte (72 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0)),
   byte 0x89,
   byte ((if disp = 0 ∧ base % 8 ≠ 5 then 0
          else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
         8 * (src % 8) + base % 8)] ++
  (if base % 8 = 4 then [byte 0x24] else []) ++
  (if disp = 0 ∧ base % 8 ≠ 5 then []
   else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat]
   else [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])

/-- The encoded byte list of `movMR .z32`. -/
abbrev movMRZ32Bytes (src base : Nat) (disp : BitVec 64) : List (BitVec 8) :=
  (if 8 ≤ src ∨ 8 ≤ base then
    [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) ++
  [byte 0x89,
   byte ((if disp = 0 ∧ base % 8 ≠ 5 then 0
          else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
         8 * (src % 8) + base % 8)] ++
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
/-- The encoded bytes of `movMR .z64`. -/
theorem encodeInsn_movMR_z64_bytes (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    encodeInsn (.movMR .z64 src base disp) = movMRZ64Bytes src base disp := by
  interval_cases src <;> interval_cases base
  all_goals
    simp only [encodeInsn, movMRZ64Bytes, eGenRmReg, eModRM, eOpsize, rexPrefix, mkRex, eImm8_32,
      eImm8, eImm32, byte, modField]
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

/-- `encodeInsn (.movMR .z64 src base disp)` is `movMRZ64Bytes src base disp`. -/
theorem encodeInsn_movMR_z64 (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    encodeInsn (.movMR .z64 src base disp) = movMRZ64Bytes src base disp :=
  encodeInsn_movMR_z64_bytes src base hs hb disp hlo hhi

/-- The encoded bytes of `movRM .z32`. -/
theorem encodeInsn_movRM_z32_bytes (dst base : Nat) (hd : dst < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    encodeInsn (.movRM .z32 dst base disp) =
      (if 8 ≤ dst ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ dst then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) ++
      [byte 0x8B,
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

/-- `encodeInsn (.movRM .z32 dst base disp)` is `movRMZ32Bytes dst base disp`. -/
theorem encodeInsn_movRM_z32 (dst base : Nat) (hd : dst < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    encodeInsn (.movRM .z32 dst base disp) = movRMZ32Bytes dst base disp :=
  encodeInsn_movRM_z32_bytes dst base hd hb disp hlo hhi


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
    try simp only [if_true]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · simp only [X64Insn.movRM.injEq, true_and, and_true]
      first
      | (rw [Nat.mod_eq_sub_mod hd8, Nat.mod_eq_of_lt (by omega)]; try omega)
      | (rw [Nat.mod_eq_of_lt (by omega)]; try omega)
    · by_cases h1 : disp = 0 ∧ base % 8 ≠ 5 <;>
        by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 <;> simp [h1, h2] <;> omega


/-- The `parseRM` inverse at offset 1, for the no-REX-prefix 32-bit forms. -/
theorem parseRM_rmBase_noRex (b : BitVec 8) (reg base : Nat) (hr : reg < 8) (hb : base < 8)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    parseRM (byteListReader
      ([b,
        byte ((if disp = 0 ∧ base % 8 ≠ 5 then 0
               else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
              8 * reg + base % 8)] ++
        (if base % 8 = 4 then [byte 0x24] else []) ++
        (if disp = 0 ∧ base % 8 ≠ 5 then []
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat]
         else [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536),
           byte (disp.toNat / 16777216)]))) 1 false =
      some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0
                         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
             regBits := reg,
             rm := .zm none (.regBase base) disp,
             len := (if base % 8 = 4 then 1 else 0) +
                    (if disp = 0 ∧ base % 8 ≠ 5 then 1
                     else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
  have h := parseRM_rmBase_z64 (byte 0) b reg base hr (by omega) disp hlo hhi
  have hd : decide (8 ≤ base) = false := by simp; omega
  rw [hd] at h
  exact h

/-- Dropping one byte from the front of a byte list shifts `parseRM`'s offset
by one.  This lets the two-byte-prefix `parseRM` lemmas be reused for the
`0x66`-prefixed forms. -/
theorem parseRM_shift (a : BitVec 8) (l : List (BitVec 8)) (off : Nat) (rexB : Bool) :
    parseRM (byteListReader (a :: l)) (off + 1) rexB =
      parseRM (byteListReader l) off rexB := by
  rfl

/-- `parseRM` recovers the `movMR .z64` memory operand from its encoding. -/
theorem parseRM_movMR_z64 (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    parseRM (byteListReader (encodeInsn (.movMR .z64 src base disp))) 2 (decide (8 ≤ base)) =
      some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0
                         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
             regBits := src % 8,
             rm := .zm none (.regBase base) disp,
             len := (if base % 8 = 4 then 1 else 0) +
                    (if disp = 0 ∧ base % 8 ≠ 5 then 1
                     else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
  rw [encodeInsn_movMR_z64 src base hs hb disp hlo hhi]
  exact parseRM_rmBase_z64 _ (byte 0x89) (src % 8) base (by omega) hb disp hlo hhi

theorem decode_movMR_z64 (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    decode (byteListReader (encodeInsn (.movMR .z64 src base disp))) =
      some (.movMR .z64 src base disp,
        2 + (if base % 8 = 4 then 1 else 0) +
          (if disp = 0 ∧ base % 8 ≠ 5 then 1
           else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
  rw [encodeInsn_movMR_z64 src base hs hb disp hlo hhi]
  have hpm := parseRM_movMR_z64 src base hs hb disp hlo hhi
  rw [encodeInsn_movMR_z64 src base hs hb disp hlo hhi] at hpm
  set L : List (BitVec 8) := movMRZ64Bytes src base disp with hL
  have hb0 : (byteListReader L 0).toNat =
      72 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0) := by
    rw [hL]
    have hlt : 72 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0) < 256 := by
      split <;> split <;> omega
    simp [movMRZ64Bytes, byteListReader, byte, hlt]
  have hb1 : (byteListReader L 1).toNat = 0x89 := by
    rw [hL]; rfl
  by_cases hs8 : 8 ≤ src <;> by_cases hb8 : 8 ≤ base
  all_goals
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [hs8, hb8, if_true, if_false] at hpm ⊢
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
    try simp only [if_true]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · simp only [X64Insn.movMR.injEq, true_and, and_true]
      first
      | (rw [Nat.mod_eq_sub_mod hs8, Nat.mod_eq_of_lt (by omega)]; try omega)
      | (rw [Nat.mod_eq_of_lt (by omega)]; try omega)
    · by_cases h1 : disp = 0 ∧ base % 8 ≠ 5 <;>
        by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 <;> simp [h1, h2] <;> omega


theorem decode_movRM_z32 (dst base : Nat) (hd : dst < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    decode (byteListReader (encodeInsn (.movRM .z32 dst base disp))) =
      some (.movRM .z32 dst base disp,
        (if 8 ≤ dst ∨ 8 ≤ base then 1 else 0) + 1 +
          ((if base % 8 = 4 then 1 else 0) +
            (if disp = 0 ∧ base % 8 ≠ 5 then 1
             else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5))) := by
  rw [encodeInsn_movRM_z32 dst base hd hb disp hlo hhi]
  have hmod3 : (if disp = 0 ∧ base % 8 ≠ 5 then 0
      else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2) ≠ 3 := by
    intro h
    by_cases h1 : disp = 0 ∧ base % 8 ≠ 5
    · rw [if_pos h1] at h; omega
    · rw [if_neg h1] at h
      by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
      · rw [if_pos h2] at h; omega
      · rw [if_neg h2] at h; omega
  by_cases hd8 : 8 ≤ dst <;> by_cases hb8 : 8 ≤ base
  · -- dst >= 8, base >= 8: REX 0x45, rexR true, rexB true
    have hb0 : (byteListReader (movRMZ32Bytes dst base disp) 0).toNat = 69 := by
      simp [movRMZ32Bytes, byteListReader, byte, hd8, hb8]
    have hb1 : (byteListReader (movRMZ32Bytes dst base disp) 1).toNat = 0x8B := by
      simp [movRMZ32Bytes, byteListReader, byte, hd8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 69) (byte 0x8B) (dst % 8) base (by omega) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = true := by simp [hb8]
    rw [hdt] at hpm
    have hpre : (if 8 ≤ dst ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ dst then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [byte 69] := by
      rw [if_pos (Or.inl hd8), if_pos hd8, if_pos hb8]
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    try simp only [if_true]
    simp only [decodeRex, hb1]
    simp only [movRMZ32Bytes, hpre]
    simp only [List.singleton_append, decide_true]
    rw [hpm]
    simp only [baseOfRM]
    rw [if_neg hmod3]
    try simp only [decide_true]
    rw [if_pos (by rfl : (true && true) = true)]
    rw [show decide (5 ≥ 8) = false from by decide, show decide (5 ≥ 4) = true from by decide]
    simp only [if_neg (by decide : ¬ false = true)]
    try simp only [if_true]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · simp only [X64Insn.movRM.injEq, true_and, and_true]
      rw [Nat.mod_eq_sub_mod hd8, Nat.mod_eq_of_lt (by omega)]
      omega
    · by_cases h1 : disp = 0 ∧ base % 8 ≠ 5 <;>
        by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 <;> simp [h1, h2] <;> omega
  · -- dst >= 8, base < 8: REX 0x44, rexR true, rexB false
    have hb0 : (byteListReader (movRMZ32Bytes dst base disp) 0).toNat = 68 := by
      simp [movRMZ32Bytes, byteListReader, byte, hd8, hb8]
    have hb1 : (byteListReader (movRMZ32Bytes dst base disp) 1).toNat = 0x8B := by
      simp [movRMZ32Bytes, byteListReader, byte, hd8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 68) (byte 0x8B) (dst % 8) base (by omega) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = false := by simp; omega
    rw [hdt] at hpm
    have hpre : (if 8 ≤ dst ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ dst then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [byte 68] := by
      rw [if_pos (Or.inl hd8), if_pos hd8, if_neg hb8]
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    try simp only [if_true]
    simp only [decodeRex, hb1]
    simp only [movRMZ32Bytes, hpre]
    simp only [List.singleton_append]
    rw [show decide (0 = 1) = false from by decide]
    rw [hpm]
    simp only [baseOfRM]
    rw [if_neg hmod3]
    try simp only [decide_true]
    rw [if_pos (by rfl : (true && true) = true)]
    rw [show decide (4 ≥ 8) = false from by decide, show decide (4 ≥ 4) = true from by decide]
    simp only [if_neg (by decide : ¬ false = true)]
    try simp only [if_true]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · simp only [X64Insn.movRM.injEq, true_and, and_true]
      rw [Nat.mod_eq_sub_mod hd8, Nat.mod_eq_of_lt (by omega)]
      omega
    · by_cases h1 : disp = 0 ∧ base % 8 ≠ 5 <;>
        by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 <;> simp [h1, h2] <;> omega
  · -- dst < 8, base >= 8: REX 0x41, rexR false, rexB true
    have hb0 : (byteListReader (movRMZ32Bytes dst base disp) 0).toNat = 65 := by
      simp [movRMZ32Bytes, byteListReader, byte, hd8, hb8]
    have hb1 : (byteListReader (movRMZ32Bytes dst base disp) 1).toNat = 0x8B := by
      simp [movRMZ32Bytes, byteListReader, byte, hd8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 65) (byte 0x8B) (dst % 8) base (by omega) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = true := by simp [hb8]
    rw [hdt] at hpm
    have hpre : (if 8 ≤ dst ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ dst then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [byte 65] := by
      rw [if_pos (Or.inr hb8), if_neg hd8, if_pos hb8]
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    try simp only [if_true]
    simp only [decodeRex, hb1]
    simp only [movRMZ32Bytes, hpre]
    simp only [List.singleton_append, decide_true]
    rw [hpm]
    simp only [baseOfRM]
    rw [if_neg hmod3]
    try simp only [decide_true]
    rw [if_pos (by rfl : (true && true) = true)]
    rw [show decide (1 ≥ 8) = false from by decide, show decide (1 ≥ 4) = false from by decide]
    simp only [if_neg (by decide : ¬ false = true)]
    try simp only [if_true]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · simp only [X64Insn.movRM.injEq, true_and, and_true]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · by_cases h1 : disp = 0 ∧ base % 8 ≠ 5 <;>
        by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 <;> simp [h1, h2] <;> omega
  · -- dst < 8, base < 8: no REX, opcode 0x8B at offset 0
    have hb0 : (byteListReader (movRMZ32Bytes dst base disp) 0).toNat = 0x8B := by
      simp [movRMZ32Bytes, byteListReader, byte, hd8, hb8]
    have hpm := parseRM_rmBase_noRex (byte 0x8B) (dst % 8) base (by omega) (by omega) disp hlo hhi
    have hpre : (if 8 ≤ dst ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ dst then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [] := by
      rw [if_neg (by omega : ¬ (8 ≤ dst ∨ 8 ≤ base))]
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [movRMZ32Bytes, hpre, List.nil_append]
    rw [hpm]
    simp only [baseOfRM]
    rw [if_neg hmod3]
    try simp only [if_true]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · simp only [X64Insn.movRM.injEq, true_and, and_true]
      rw [Nat.mod_eq_of_lt (by omega)]
      try omega
    · by_cases h1 : disp = 0 ∧ base % 8 ≠ 5 <;>
        by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 <;> simp [h1, h2] <;> omega


theorem encodeInsn_movMR_z32_bytes (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    encodeInsn (.movMR .z32 src base disp) =
      (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) ++
      [byte 0x89,
       byte ((if disp = 0 ∧ base % 8 ≠ 5 then 0
              else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
             8 * (src % 8) + base % 8)] ++
      (if base % 8 = 4 then [byte 0x24] else []) ++
      (if disp = 0 ∧ base % 8 ≠ 5 then []
       else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat]
       else [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)]) := by
  interval_cases src <;> interval_cases base
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

theorem encodeInsn_movMR_z32 (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    encodeInsn (.movMR .z32 src base disp) = movMRZ32Bytes src base disp :=
  encodeInsn_movMR_z32_bytes src base hs hb disp hlo hhi

theorem parseRM_movMR_z32 (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    parseRM (byteListReader (encodeInsn (.movMR .z32 src base disp)))
      (if 8 ≤ src ∨ 8 ≤ base then 2 else 1) (decide (8 ≤ base)) =
      some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0
                         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
             regBits := src % 8,
             rm := .zm none (.regBase base) disp,
             len := (if base % 8 = 4 then 1 else 0) +
                    (if disp = 0 ∧ base % 8 ≠ 5 then 1
                     else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
  rw [encodeInsn_movMR_z32 src base hs hb disp hlo hhi]
  by_cases hpre : 8 ≤ src ∨ 8 ≤ base
  · simp only [movMRZ32Bytes, hpre, if_true]
    have h := parseRM_rmBase_z64
      (byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0)))
      (byte 0x89) (src % 8) base (by omega) hb disp hlo hhi
    simpa using h
  · simp only [movMRZ32Bytes, hpre, if_false, List.nil_append]
    have hb8 : base < 8 := by omega
    have h8 : decide (8 ≤ base) = false := by simp; omega
    rw [h8]
    simpa using parseRM_rmBase_noRex (byte 0x89) (src % 8) base (by omega) hb8 disp hlo hhi

theorem decode_movMR_z32 (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    decode (byteListReader (encodeInsn (.movMR .z32 src base disp))) =
      some (.movMR .z32 src base disp,
        (if 8 ≤ src ∨ 8 ≤ base then 1 else 0) + 1 +
          ((if base % 8 = 4 then 1 else 0) +
            (if disp = 0 ∧ base % 8 ≠ 5 then 1
             else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5))) := by
  rw [encodeInsn_movMR_z32 src base hs hb disp hlo hhi]
  have hmod3 : (if disp = 0 ∧ base % 8 ≠ 5 then 0
      else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2) ≠ 3 := by
    intro h
    by_cases h1 : disp = 0 ∧ base % 8 ≠ 5
    · rw [if_pos h1] at h; omega
    · rw [if_neg h1] at h
      by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
      · rw [if_pos h2] at h; omega
      · rw [if_neg h2] at h; omega
  by_cases hs8 : 8 ≤ src <;> by_cases hb8 : 8 ≤ base
  · have hb0 : (byteListReader (movMRZ32Bytes src base disp) 0).toNat = 69 := by
      simp [movMRZ32Bytes, byteListReader, byte, hs8, hb8]
    have hb1 : (byteListReader (movMRZ32Bytes src base disp) 1).toNat = 0x89 := by
      simp [movMRZ32Bytes, byteListReader, byte, hs8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 69) (byte 0x89) (src % 8) base (by omega) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = true := by simp [hb8]
    rw [hdt] at hpm
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [byte 69] := by
      rw [if_pos (Or.inl hs8), if_pos hs8, if_pos hb8]
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    try simp only [if_true]
    simp only [decodeRex, hb1]
    simp only [movMRZ32Bytes, hpre]
    simp only [List.singleton_append, decide_true]
    rw [hpm]
    simp only [baseOfRM]
    rw [if_neg hmod3]
    try simp only [decide_true]
    rw [if_pos (by rfl : (true && true) = true)]
    rw [show decide (5 ≥ 8) = false from by decide, show decide (5 ≥ 4) = true from by decide]
    simp only [if_neg (by decide : ¬ false = true)]
    try simp only [if_true]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · simp only [X64Insn.movMR.injEq, true_and, and_true]
      rw [Nat.mod_eq_sub_mod hs8, Nat.mod_eq_of_lt (by omega)]
      omega
    · by_cases h1 : disp = 0 ∧ base % 8 ≠ 5 <;>
        by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 <;> simp [h1, h2] <;> omega
  · have hb0 : (byteListReader (movMRZ32Bytes src base disp) 0).toNat = 68 := by
      simp [movMRZ32Bytes, byteListReader, byte, hs8, hb8]
    have hb1 : (byteListReader (movMRZ32Bytes src base disp) 1).toNat = 0x89 := by
      simp [movMRZ32Bytes, byteListReader, byte, hs8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 68) (byte 0x89) (src % 8) base (by omega) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = false := by simp; omega
    rw [hdt] at hpm
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [byte 68] := by
      rw [if_pos (Or.inl hs8), if_pos hs8, if_neg hb8]
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    try simp only [if_true]
    simp only [decodeRex, hb1]
    simp only [movMRZ32Bytes, hpre]
    simp only [List.singleton_append]
    rw [show decide (0 = 1) = false from by decide]
    rw [hpm]
    simp only [baseOfRM]
    rw [if_neg hmod3]
    try simp only [decide_true]
    rw [if_pos (by rfl : (true && true) = true)]
    rw [show decide (4 ≥ 8) = false from by decide, show decide (4 ≥ 4) = true from by decide]
    simp only [if_neg (by decide : ¬ false = true)]
    try simp only [if_true]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · simp only [X64Insn.movMR.injEq, true_and, and_true]
      rw [Nat.mod_eq_sub_mod hs8, Nat.mod_eq_of_lt (by omega)]
      omega
    · by_cases h1 : disp = 0 ∧ base % 8 ≠ 5 <;>
        by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 <;> simp [h1, h2] <;> omega
  · have hb0 : (byteListReader (movMRZ32Bytes src base disp) 0).toNat = 65 := by
      simp [movMRZ32Bytes, byteListReader, byte, hs8, hb8]
    have hb1 : (byteListReader (movMRZ32Bytes src base disp) 1).toNat = 0x89 := by
      simp [movMRZ32Bytes, byteListReader, byte, hs8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 65) (byte 0x89) (src % 8) base (by omega) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = true := by simp [hb8]
    rw [hdt] at hpm
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [byte 65] := by
      rw [if_pos (Or.inr hb8), if_neg hs8, if_pos hb8]
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    try simp only [if_true]
    simp only [decodeRex, hb1]
    simp only [movMRZ32Bytes, hpre]
    simp only [List.singleton_append, decide_true]
    rw [hpm]
    simp only [baseOfRM]
    rw [if_neg hmod3]
    try simp only [decide_true]
    rw [if_pos (by rfl : (true && true) = true)]
    rw [show decide (1 ≥ 8) = false from by decide, show decide (1 ≥ 4) = false from by decide]
    simp only [if_neg (by decide : ¬ false = true)]
    try simp only [if_true]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · simp only [X64Insn.movMR.injEq, true_and, and_true]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · by_cases h1 : disp = 0 ∧ base % 8 ≠ 5 <;>
        by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 <;> simp [h1, h2] <;> omega
  · have hb0 : (byteListReader (movMRZ32Bytes src base disp) 0).toNat = 0x89 := by
      simp [movMRZ32Bytes, byteListReader, byte, hs8, hb8]
    have hpm := parseRM_rmBase_noRex (byte 0x89) (src % 8) base (by omega) (by omega) disp hlo hhi
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [] := by
      rw [if_neg (by omega : ¬ (8 ≤ src ∨ 8 ≤ base))]
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [movMRZ32Bytes, hpre, List.nil_append]
    rw [hpm]
    simp only [baseOfRM]
    rw [if_neg hmod3]
    try simp only [if_true]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · simp only [X64Insn.movMR.injEq, true_and, and_true]
      rw [Nat.mod_eq_of_lt (by omega)]
      try omega
    · by_cases h1 : disp = 0 ∧ base % 8 ≠ 5 <;>
        by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 <;> simp [h1, h2] <;> omega

theorem eGenRmReg_regBase (sz : ZSize) (reg base : Nat) (hr : reg < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31)
    (p : List (BitVec 8)) (opc : BitVec 8) (mo : Option (BitVec 8)) :
    eGenRmReg sz (.zm none (.regBase base) disp) (BitVec.ofNat 4 reg) p opc mo =
      (match sz with
       | .z8 haveRex =>
           (if 8 ≤ reg ∨ 8 ≤ base then
             [byte (64 + (if 8 ≤ reg then 4 else 0) + (if 8 ≤ base then 1 else 0))]
            else if haveRex then [byte 0x40] else [])
       | .z16 =>
           [byte 0x66] ++
             (if 8 ≤ reg ∨ 8 ≤ base then
               [byte (64 + (if 8 ≤ reg then 4 else 0) + (if 8 ≤ base then 1 else 0))]
              else [])
       | .z32 =>
           (if 8 ≤ reg ∨ 8 ≤ base then
             [byte (64 + (if 8 ≤ reg then 4 else 0) + (if 8 ≤ base then 1 else 0))]
            else [])
       | .z64 =>
           [byte (72 + (if 8 ≤ reg then 4 else 0) + (if 8 ≤ base then 1 else 0))]) ++
      p ++
      [opc ||| (mo.getD (match sz with | .z8 _ => 0 | _ => 1))] ++
      [byte ((if disp = 0 ∧ base % 8 ≠ 5 then 0
              else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
             8 * (reg % 8) + base % 8)] ++
      (if base % 8 = 4 then [byte 0x24] else []) ++
      (if disp = 0 ∧ base % 8 ≠ 5 then []
       else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat]
       else [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)]) := by
  cases sz with
  | z8 haveRex =>
    cases haveRex
    · interval_cases reg <;> interval_cases base
      all_goals
        simp only [eGenRmReg, eModRM, eOpsize, rexPrefix, mkRex, eImm8_32, eImm8, eImm32, byte, modField]
        simp only [Nat.reduceMod, Nat.reduceMul, Nat.reduceDiv]
        simp
        by_cases h0 : disp = 0
        · subst h0; simp
        · have h0' : disp ≠ 0#64 := h0
          by_cases h8 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
          · simp [h0', h8]
          · have h32 : -2147483648 ≤ disp.toInt ∧ disp.toInt ≤ 2147483647 := by omega
            simp [h0', h8, h32]
    · interval_cases reg <;> interval_cases base
      all_goals
        simp only [eGenRmReg, eModRM, eOpsize, rexPrefix, mkRex, eImm8_32, eImm8, eImm32, byte, modField]
        simp only [Nat.reduceMod, Nat.reduceMul, Nat.reduceDiv]
        simp
        by_cases h0 : disp = 0
        · subst h0; simp
        · have h0' : disp ≠ 0#64 := h0
          by_cases h8 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
          · simp [h0', h8]
          · have h32 : -2147483648 ≤ disp.toInt ∧ disp.toInt ≤ 2147483647 := by omega
            simp [h0', h8, h32]
  | z16 =>
    interval_cases reg <;> interval_cases base
    all_goals
      simp only [eGenRmReg, eModRM, eOpsize, rexPrefix, mkRex, eImm8_32, eImm8, eImm32, byte, modField]
      simp only [Nat.reduceMod, Nat.reduceMul, Nat.reduceDiv]
      simp
      by_cases h0 : disp = 0
      · subst h0; simp
      · have h0' : disp ≠ 0#64 := h0
        by_cases h8 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
        · simp [h0', h8]
        · have h32 : -2147483648 ≤ disp.toInt ∧ disp.toInt ≤ 2147483647 := by omega
          simp [h0', h8, h32]
  | z32 =>
    interval_cases reg <;> interval_cases base
    all_goals
      simp only [eGenRmReg, eModRM, eOpsize, rexPrefix, mkRex, eImm8_32, eImm8, eImm32, byte, modField]
      simp only [Nat.reduceMod, Nat.reduceMul, Nat.reduceDiv]
      simp
      by_cases h0 : disp = 0
      · subst h0; simp
      · have h0' : disp ≠ 0#64 := h0
        by_cases h8 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
        · simp [h0', h8]
        · have h32 : -2147483648 ≤ disp.toInt ∧ disp.toInt ≤ 2147483647 := by omega
          simp [h0', h8, h32]
  | z64 =>
    interval_cases reg <;> interval_cases base
    all_goals
      simp only [eGenRmReg, eModRM, eOpsize, rexPrefix, mkRex, eImm8_32, eImm8, eImm32, byte, modField]
      simp only [Nat.reduceMod, Nat.reduceMul, Nat.reduceDiv]
      simp
      by_cases h0 : disp = 0
      · subst h0; simp
      · have h0' : disp ≠ 0#64 := h0
        by_cases h8 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
        · simp [h0', h8]
        · have h32 : -2147483648 ≤ disp.toInt ∧ disp.toInt ≤ 2147483647 := by omega
          simp [h0', h8, h32]

/-- The encoded byte list of `movMR .z16`. -/
abbrev movMRZ16Bytes (src base : Nat) (disp : BitVec 64) : List (BitVec 8) :=
  [byte 0x66] ++
  (if 8 ≤ src ∨ 8 ≤ base then
    [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) ++
  [byte 0x89,
   byte ((if disp = 0 ∧ base % 8 ≠ 5 then 0
          else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
         8 * (src % 8) + base % 8)] ++
  (if base % 8 = 4 then [byte 0x24] else []) ++
  (if disp = 0 ∧ base % 8 ≠ 5 then []
   else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat]
   else [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536),
     byte (disp.toNat / 16777216)])

/-- `encodeInsn (.movMR .z16 src base disp)` is `movMRZ16Bytes src base disp`. -/
theorem encodeInsn_movMR_z16 (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    encodeInsn (.movMR .z16 src base disp) = movMRZ16Bytes src base disp := by
  rw [encodeInsn, eGenRmReg_regBase .z16 src base hs hb disp hlo hhi [] (byte 0x88) none]
  simp [movMRZ16Bytes]
  decide

set_option maxHeartbeats 1000000 in
theorem decode_movMR_z16 (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    decode (byteListReader (encodeInsn (.movMR .z16 src base disp))) =
      some (.movMR .z16 src base disp,
        2 + (if 8 ≤ src ∨ 8 ≤ base then 1 else 0) +
          ((if base % 8 = 4 then 1 else 0) +
            (if disp = 0 ∧ base % 8 ≠ 5 then 1
             else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5))) := by
  rw [encodeInsn_movMR_z16 src base hs hb disp hlo hhi]
  have hmod3 : (if disp = 0 ∧ base % 8 ≠ 5 then 0
      else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2) ≠ 3 := by
    intro h
    by_cases h1 : disp = 0 ∧ base % 8 ≠ 5
    · rw [if_pos h1] at h; omega
    · rw [if_neg h1] at h
      by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
      · rw [if_pos h2] at h; omega
      · rw [if_neg h2] at h; omega
  have hsib : (if base % 8 = 4 then [byte 0x24] else []) = (if base % 8 = 4 then [byte 0x24] else []) := rfl
  by_cases hs8 : 8 ≤ src <;> by_cases hb8 : 8 ≤ base
  · have hb0 : (byteListReader (movMRZ16Bytes src base disp) 0).toNat = 0x66 := by
      simp [movMRZ16Bytes, byteListReader, byte, hs8, hb8]
    have hb1 : (byteListReader (movMRZ16Bytes src base disp) 1).toNat = 69 := by
      simp [movMRZ16Bytes, byteListReader, byte, hs8, hb8]
    have hb2 : (byteListReader (movMRZ16Bytes src base disp) 2).toNat = 0x89 := by
      simp [movMRZ16Bytes, byteListReader, byte, hs8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 69) (byte 0x89) (src % 8) base
      (Nat.mod_lt src (by norm_num)) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = true := by simp [hb8]
    rw [hdt] at hpm
    have hpm' : parseRM (byteListReader (byte 69 :: byte 0x89 :: byte
        ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
            8 * (src % 8) + base % 8) ::
        ((if base % 8 = 4 then [byte 0x24] else []) ++
         (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
           [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 true =
        some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
               regBits := src % 8, rm := .zm none (.regBase base) disp,
               len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
      simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
    simp only [decode, decodeNoRex]
    rw [hb0]
    rw [hb1]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    rw [hb2]
    simp only [decide_true, Bool.true_and, if_true, if_false, Nat.reduceEqDiff]
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [byte 69] := by
      rw [if_pos (Or.inl hs8), if_pos hs8, if_pos hb8]
    simp only [movMRZ16Bytes, hpre, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [hmod3, if_false, baseOfRM]
    have hsrc : (if (5:ℕ) ≥ 4 then 8 else 0) + src % 8 = src := by
      rw [if_pos (by decide : (5:ℕ) ≥ 4), Nat.mod_eq_sub_mod hs8, Nat.mod_eq_of_lt (by omega)]
      omega
    have hlen : 3 + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) =
        (2 + (if 8 ≤ src ∨ 8 ≤ base then 1 else 0)) + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
      by_cases hpre2 : 8 ≤ src ∨ 8 ≤ base
      · simp [hpre2]
      · exact absurd hpre2 (by omega)
    rw [hsrc]
    simp only [Option.some.injEq, Prod.mk.injEq, true_and]
    exact hlen
  · have hb0 : (byteListReader (movMRZ16Bytes src base disp) 0).toNat = 0x66 := by
      simp [movMRZ16Bytes, byteListReader, byte, hs8, hb8]
    have hb1 : (byteListReader (movMRZ16Bytes src base disp) 1).toNat = 68 := by
      simp [movMRZ16Bytes, byteListReader, byte, hs8, hb8]
    have hb2 : (byteListReader (movMRZ16Bytes src base disp) 2).toNat = 0x89 := by
      simp [movMRZ16Bytes, byteListReader, byte, hs8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 68) (byte 0x89) (src % 8) base
      (Nat.mod_lt src (by norm_num)) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = false := by simp; omega
    rw [hdt] at hpm
    have hpm' : parseRM (byteListReader (byte 68 :: byte 0x89 :: byte
        ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
            8 * (src % 8) + base % 8) ::
        ((if base % 8 = 4 then [byte 0x24] else []) ++
         (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
           [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 false =
        some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
               regBits := src % 8, rm := .zm none (.regBase base) disp,
               len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
      simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
    simp only [decode, decodeNoRex]
    rw [hb0]
    rw [hb1]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    rw [hb2]
    simp only [decide_true, decide_false, Bool.true_and, if_true, if_false, Nat.reduceEqDiff]
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [byte 68] := by
      rw [if_pos (Or.inl hs8), if_pos hs8, if_neg hb8]
    simp only [movMRZ16Bytes, hpre, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [hmod3, if_false, baseOfRM]
    have hsrc : (if (4:ℕ) ≥ 4 then 8 else 0) + src % 8 = src := by
      rw [if_pos (by decide : (4:ℕ) ≥ 4), Nat.mod_eq_sub_mod hs8, Nat.mod_eq_of_lt (by omega)]
      omega
    have hlen : 3 + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) =
        (2 + (if 8 ≤ src ∨ 8 ≤ base then 1 else 0)) + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
      by_cases hpre2 : 8 ≤ src ∨ 8 ≤ base
      · simp [hpre2]
      · exact absurd hpre2 (by omega)
    rw [hsrc]
    simp only [Option.some.injEq, Prod.mk.injEq, true_and]
    exact hlen
  · have hb0 : (byteListReader (movMRZ16Bytes src base disp) 0).toNat = 0x66 := by
      simp [movMRZ16Bytes, byteListReader, byte, hs8, hb8]
    have hb1 : (byteListReader (movMRZ16Bytes src base disp) 1).toNat = 65 := by
      simp [movMRZ16Bytes, byteListReader, byte, hs8, hb8]
    have hb2 : (byteListReader (movMRZ16Bytes src base disp) 2).toNat = 0x89 := by
      simp [movMRZ16Bytes, byteListReader, byte, hs8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 65) (byte 0x89) (src % 8) base
      (Nat.mod_lt src (by norm_num)) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = true := by simp [hb8]
    rw [hdt] at hpm
    have hpm' : parseRM (byteListReader (byte 65 :: byte 0x89 :: byte
        ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
            8 * (src % 8) + base % 8) ::
        ((if base % 8 = 4 then [byte 0x24] else []) ++
         (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
           [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 true =
        some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
                regBits := src % 8, rm := .zm none (.regBase base) disp,
               len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
      simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
    simp only [decode, decodeNoRex]
    rw [hb0]
    rw [hb1]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    rw [hb2]
    simp only [decide_true, Bool.true_and, if_true, if_false, Nat.reduceEqDiff]
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [byte 65] := by
      rw [if_pos (Or.inr hb8), if_neg hs8, if_pos hb8]
    simp only [movMRZ16Bytes, hpre, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [hmod3, if_false, baseOfRM]
    have hsrc : (if (1:ℕ) ≥ 4 then 8 else 0) + src % 8 = src := by
      rw [if_neg (by decide : ¬ ((1:ℕ) ≥ 4)), Nat.mod_eq_of_lt (by omega)]
      omega
    have hlen : 3 + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) =
        (2 + (if 8 ≤ src ∨ 8 ≤ base then 1 else 0)) + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
      by_cases hpre2 : 8 ≤ src ∨ 8 ≤ base
      · simp [hpre2]
      · exact absurd hpre2 (by omega)
    rw [hsrc]
    simp only [Option.some.injEq, Prod.mk.injEq, true_and]
    exact hlen
  · have hb0 : (byteListReader (movMRZ16Bytes src base disp) 0).toNat = 0x66 := by
      simp [movMRZ16Bytes, byteListReader, byte, hs8, hb8]
    have hb1 : (byteListReader (movMRZ16Bytes src base disp) 1).toNat = 0x89 := by
      simp [movMRZ16Bytes, byteListReader, byte, hs8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 0x66) (byte 0x89) (src % 8) base
      (Nat.mod_lt src (by norm_num)) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = false := by simp; omega
    rw [hdt] at hpm
    have hpm' : parseRM (byteListReader (byte 0x66 :: byte 0x89 :: byte
        ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
            8 * (src % 8) + base % 8) ::
        ((if base % 8 = 4 then [byte 0x24] else []) ++
         (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
           [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 false =
        some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
                regBits := src % 8, rm := .zm none (.regBase base) disp,
               len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
      simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
    simp only [decode, decodeNoRex]
    rw [hb0]
    rw [hb1]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    simp only [decide_true, decide_false, Bool.true_and, Bool.false_eq_true, if_true, if_false, Nat.reduceEqDiff]
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [] := by
      rw [if_neg (by omega : ¬ (8 ≤ src ∨ 8 ≤ base))]
    simp only [movMRZ16Bytes, hpre, List.cons_append, List.nil_append]
    rw [hpm']
    simp only [hmod3, if_false, baseOfRM]
    have hsrc : src % 8 = src := Nat.mod_eq_of_lt (by omega)
    have hlen : 2 + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) =
        (2 + (if 8 ≤ src ∨ 8 ≤ base then 1 else 0)) + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
      rw [if_neg (by omega : ¬ (8 ≤ src ∨ 8 ≤ base))]
    rw [hsrc]
    simp only [Option.some.injEq, Prod.mk.injEq, true_and]
    exact hlen

/-- The encoded byte list of `movRM .z16`. -/
abbrev movRMZ16Bytes (dst base : Nat) (disp : BitVec 64) : List (BitVec 8) :=
  [byte 0x66] ++
  (if 8 ≤ dst ∨ 8 ≤ base then
    [byte (64 + (if 8 ≤ dst then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) ++
  [byte 0x8B,
   byte ((if disp = 0 ∧ base % 8 ≠ 5 then 0
          else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
         8 * (dst % 8) + base % 8)] ++
  (if base % 8 = 4 then [byte 0x24] else []) ++
  (if disp = 0 ∧ base % 8 ≠ 5 then []
   else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat]
   else [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536),
     byte (disp.toNat / 16777216)])

theorem encodeInsn_movRM_z16 (dst base : Nat) (hd : dst < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    encodeInsn (.movRM .z16 dst base disp) = movRMZ16Bytes dst base disp := by
  rw [encodeInsn, eGenRmReg_regBase .z16 dst base hd hb disp hlo hhi [] (byte 0x8A) none]
  simp [movRMZ16Bytes]
  decide

set_option maxHeartbeats 1000000 in
theorem decode_movRM_z16 (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    decode (byteListReader (encodeInsn (.movRM .z16 src base disp))) =
      some (.movRM .z16 src base disp,
        2 + (if 8 ≤ src ∨ 8 ≤ base then 1 else 0) +
          ((if base % 8 = 4 then 1 else 0) +
            (if disp = 0 ∧ base % 8 ≠ 5 then 1
             else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5))) := by
  rw [encodeInsn_movRM_z16 src base hs hb disp hlo hhi]
  have hmod3 : (if disp = 0 ∧ base % 8 ≠ 5 then 0
      else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2) ≠ 3 := by
    intro h
    by_cases h1 : disp = 0 ∧ base % 8 ≠ 5
    · rw [if_pos h1] at h; omega
    · rw [if_neg h1] at h
      by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
      · rw [if_pos h2] at h; omega
      · rw [if_neg h2] at h; omega
  have hsib : (if base % 8 = 4 then [byte 0x24] else []) = (if base % 8 = 4 then [byte 0x24] else []) := rfl
  by_cases hs8 : 8 ≤ src <;> by_cases hb8 : 8 ≤ base
  · have hb0 : (byteListReader (movRMZ16Bytes src base disp) 0).toNat = 0x66 := by
      simp [movRMZ16Bytes, byteListReader, byte, hs8, hb8]
    have hb1 : (byteListReader (movRMZ16Bytes src base disp) 1).toNat = 69 := by
      simp [movRMZ16Bytes, byteListReader, byte, hs8, hb8]
    have hb2 : (byteListReader (movRMZ16Bytes src base disp) 2).toNat = 0x8B := by
      simp [movRMZ16Bytes, byteListReader, byte, hs8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 69) (byte 0x8B) (src % 8) base
      (Nat.mod_lt src (by norm_num)) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = true := by simp [hb8]
    rw [hdt] at hpm
    have hpm' : parseRM (byteListReader (byte 69 :: byte 0x8B :: byte
        ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
            8 * (src % 8) + base % 8) ::
        ((if base % 8 = 4 then [byte 0x24] else []) ++
         (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
           [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 true =
        some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
               regBits := src % 8, rm := .zm none (.regBase base) disp,
               len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
      simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
    simp only [decode, decodeNoRex]
    rw [hb0]
    rw [hb1]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    rw [hb2]
    simp only [decide_true, Bool.true_and, if_true, if_false, Nat.reduceEqDiff]
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [byte 69] := by
      rw [if_pos (Or.inl hs8), if_pos hs8, if_pos hb8]
    simp only [movRMZ16Bytes, hpre, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [hmod3, if_false, baseOfRM]
    have hsrc : (if (5:ℕ) ≥ 4 then 8 else 0) + src % 8 = src := by
      rw [if_pos (by decide : (5:ℕ) ≥ 4), Nat.mod_eq_sub_mod hs8, Nat.mod_eq_of_lt (by omega)]
      omega
    have hlen : 3 + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) =
        (2 + (if 8 ≤ src ∨ 8 ≤ base then 1 else 0)) + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
      by_cases hpre2 : 8 ≤ src ∨ 8 ≤ base
      · simp [hpre2]
      · exact absurd hpre2 (by omega)
    rw [hsrc]
    simp only [Option.some.injEq, Prod.mk.injEq, true_and]
    exact hlen
  · have hb0 : (byteListReader (movRMZ16Bytes src base disp) 0).toNat = 0x66 := by
      simp [movRMZ16Bytes, byteListReader, byte, hs8, hb8]
    have hb1 : (byteListReader (movRMZ16Bytes src base disp) 1).toNat = 68 := by
      simp [movRMZ16Bytes, byteListReader, byte, hs8, hb8]
    have hb2 : (byteListReader (movRMZ16Bytes src base disp) 2).toNat = 0x8B := by
      simp [movRMZ16Bytes, byteListReader, byte, hs8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 68) (byte 0x8B) (src % 8) base
      (Nat.mod_lt src (by norm_num)) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = false := by simp; omega
    rw [hdt] at hpm
    have hpm' : parseRM (byteListReader (byte 68 :: byte 0x8B :: byte
        ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
            8 * (src % 8) + base % 8) ::
        ((if base % 8 = 4 then [byte 0x24] else []) ++
         (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
           [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 false =
        some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
               regBits := src % 8, rm := .zm none (.regBase base) disp,
               len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
      simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
    simp only [decode, decodeNoRex]
    rw [hb0]
    rw [hb1]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    rw [hb2]
    simp only [decide_true, decide_false, Bool.true_and, if_true, if_false, Nat.reduceEqDiff]
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [byte 68] := by
      rw [if_pos (Or.inl hs8), if_pos hs8, if_neg hb8]
    simp only [movRMZ16Bytes, hpre, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [hmod3, if_false, baseOfRM]
    have hsrc : (if (4:ℕ) ≥ 4 then 8 else 0) + src % 8 = src := by
      rw [if_pos (by decide : (4:ℕ) ≥ 4), Nat.mod_eq_sub_mod hs8, Nat.mod_eq_of_lt (by omega)]
      omega
    have hlen : 3 + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) =
        (2 + (if 8 ≤ src ∨ 8 ≤ base then 1 else 0)) + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
      by_cases hpre2 : 8 ≤ src ∨ 8 ≤ base
      · simp [hpre2]
      · exact absurd hpre2 (by omega)
    rw [hsrc]
    simp only [Option.some.injEq, Prod.mk.injEq, true_and]
    exact hlen
  · have hb0 : (byteListReader (movRMZ16Bytes src base disp) 0).toNat = 0x66 := by
      simp [movRMZ16Bytes, byteListReader, byte, hs8, hb8]
    have hb1 : (byteListReader (movRMZ16Bytes src base disp) 1).toNat = 65 := by
      simp [movRMZ16Bytes, byteListReader, byte, hs8, hb8]
    have hb2 : (byteListReader (movRMZ16Bytes src base disp) 2).toNat = 0x8B := by
      simp [movRMZ16Bytes, byteListReader, byte, hs8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 65) (byte 0x8B) (src % 8) base
      (Nat.mod_lt src (by norm_num)) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = true := by simp [hb8]
    rw [hdt] at hpm
    have hpm' : parseRM (byteListReader (byte 65 :: byte 0x8B :: byte
        ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
            8 * (src % 8) + base % 8) ::
        ((if base % 8 = 4 then [byte 0x24] else []) ++
         (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
           [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 true =
        some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
                regBits := src % 8, rm := .zm none (.regBase base) disp,
               len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
      simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
    simp only [decode, decodeNoRex]
    rw [hb0]
    rw [hb1]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    rw [hb2]
    simp only [decide_true, Bool.true_and, if_true, if_false, Nat.reduceEqDiff]
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [byte 65] := by
      rw [if_pos (Or.inr hb8), if_neg hs8, if_pos hb8]
    simp only [movRMZ16Bytes, hpre, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [hmod3, if_false, baseOfRM]
    have hsrc : (if (1:ℕ) ≥ 4 then 8 else 0) + src % 8 = src := by
      rw [if_neg (by decide : ¬ ((1:ℕ) ≥ 4)), Nat.mod_eq_of_lt (by omega)]
      omega
    have hlen : 3 + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) =
        (2 + (if 8 ≤ src ∨ 8 ≤ base then 1 else 0)) + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
      by_cases hpre2 : 8 ≤ src ∨ 8 ≤ base
      · simp [hpre2]
      · exact absurd hpre2 (by omega)
    rw [hsrc]
    simp only [Option.some.injEq, Prod.mk.injEq, true_and]
    exact hlen
  · have hb0 : (byteListReader (movRMZ16Bytes src base disp) 0).toNat = 0x66 := by
      simp [movRMZ16Bytes, byteListReader, byte, hs8, hb8]
    have hb1 : (byteListReader (movRMZ16Bytes src base disp) 1).toNat = 0x8B := by
      simp [movRMZ16Bytes, byteListReader, byte, hs8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 0x66) (byte 0x8B) (src % 8) base
      (Nat.mod_lt src (by norm_num)) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = false := by simp; omega
    rw [hdt] at hpm
    have hpm' : parseRM (byteListReader (byte 0x66 :: byte 0x8B :: byte
        ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
            8 * (src % 8) + base % 8) ::
        ((if base % 8 = 4 then [byte 0x24] else []) ++
         (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
           [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 false =
        some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
                regBits := src % 8, rm := .zm none (.regBase base) disp,
               len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
      simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
    simp only [decode, decodeNoRex]
    rw [hb0]
    rw [hb1]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    simp only [decide_true, decide_false, Bool.true_and, Bool.false_eq_true, if_true, if_false, Nat.reduceEqDiff]
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [] := by
      rw [if_neg (by omega : ¬ (8 ≤ src ∨ 8 ≤ base))]
    simp only [movRMZ16Bytes, hpre, List.cons_append, List.nil_append]
    rw [hpm']
    simp only [hmod3, if_false, baseOfRM]
    have hsrc : src % 8 = src := Nat.mod_eq_of_lt (by omega)
    have hlen : 2 + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) =
        (2 + (if 8 ≤ src ∨ 8 ≤ base then 1 else 0)) + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
      rw [if_neg (by omega : ¬ (8 ≤ src ∨ 8 ≤ base))]
    rw [hsrc]
    simp only [Option.some.injEq, Prod.mk.injEq, true_and]
    exact hlen

/-- The encoded byte list of `movMR (.z8 h)`. -/
abbrev movMRZ8Bytes (h : Bool) (src base : Nat) (disp : BitVec 64) : List (BitVec 8) :=
  (if 8 ≤ src ∨ 8 ≤ base then
    [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))]
   else if h = true then [byte 0x40] else []) ++
  [byte 0x88,
   byte ((if disp = 0 ∧ base % 8 ≠ 5 then 0
          else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
         8 * (src % 8) + base % 8)] ++
  (if base % 8 = 4 then [byte 0x24] else []) ++
  (if disp = 0 ∧ base % 8 ≠ 5 then []
   else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat]
   else [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536),
     byte (disp.toNat / 16777216)])

theorem encodeInsn_movMR_z8 (h : Bool) (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    encodeInsn (.movMR (.z8 h) src base disp) = movMRZ8Bytes h src base disp := by
  rw [encodeInsn, eGenRmReg_regBase (.z8 h) src base hs hb disp hlo hhi [] (byte 0x88) none]
  simp [movMRZ8Bytes]

set_option maxHeartbeats 1000000 in
theorem decode_movMR_z8 (h : Bool) (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    decode (byteListReader (encodeInsn (.movMR (.z8 h) src base disp))) =
      some (.movMR (.z8 (if 8 ≤ src ∨ 8 ≤ base then true else h)) src base disp,
        1 + (if 8 ≤ src ∨ 8 ≤ base then 1 else if h = true then 1 else 0) +
          ((if base % 8 = 4 then 1 else 0) +
            (if disp = 0 ∧ base % 8 ≠ 5 then 1
             else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5))) := by
  rw [encodeInsn_movMR_z8 h src base hs hb disp hlo hhi]
  have hmod3 : (if disp = 0 ∧ base % 8 ≠ 5 then 0
      else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2) ≠ 3 := by
    intro hh
    by_cases h1 : disp = 0 ∧ base % 8 ≠ 5
    · rw [if_pos h1] at hh; omega
    · rw [if_neg h1] at hh
      by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
      · rw [if_pos h2] at hh; omega
      · rw [if_neg h2] at hh; omega
  by_cases hpre : 8 ≤ src ∨ 8 ≤ base
  · by_cases hs8 : 8 ≤ src <;> by_cases hb8 : 8 ≤ base
    · -- rex 69
      have hb0 : (byteListReader (movMRZ8Bytes h src base disp) 0).toNat = 69 := by
        simp [movMRZ8Bytes, byteListReader, byte, hs8, hb8]
      have hb1 : (byteListReader (movMRZ8Bytes h src base disp) 1).toNat = 0x88 := by
        simp [movMRZ8Bytes, byteListReader, byte, hs8, hb8]
      have hpm := parseRM_rmBase_z64 (byte 69) (byte 0x88) (src % 8) base
        (Nat.mod_lt src (by norm_num)) hb disp hlo hhi
      have hdt : decide (8 ≤ base) = true := by simp [hb8]
      rw [hdt] at hpm
      have hpm' : parseRM (byteListReader (byte 69 :: byte 0x88 :: byte
          ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
              8 * (src % 8) + base % 8) ::
          ((if base % 8 = 4 then [byte 0x24] else []) ++
           (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
             [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 true =
          some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
                 regBits := src % 8, rm := .zm none (.regBase base) disp,
                 len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
        simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
      simp only [decode, decodeNoRex]
      rw [hb0]
      simp only [Nat.reduceMod, Nat.reduceLeDiff]
      simp only [decide_true, Bool.true_and, if_true]
      rw [show decide (5 ≥ 8) = false from by decide,
          show decide (5 ≥ 4) = true from by decide]
      simp only [decodeRex, hb1]
      have hpfx : (if 8 ≤ src ∨ 8 ≤ base then
          [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))]
         else if h = true then [byte 0x40] else []) = [byte 69] := by
        rw [if_pos (Or.inl hs8), if_pos hs8, if_pos hb8]
      simp only [movMRZ8Bytes, hpfx, if_true, List.cons_append, List.nil_append]
      rw [hpm']
      simp only [hmod3, if_false, baseOfRM]
      have hsrc : 8 + src % 8 = src := by
        rw [Nat.mod_eq_sub_mod hs8, Nat.mod_eq_of_lt (by omega)]
        omega
      rw [hsrc]
      have hflag : (if 8 ≤ src ∨ 8 ≤ base then true else h) = true := by
        rw [if_pos hpre]
      rw [hflag]
      have hlen : (1 + (if 8 ≤ src ∨ 8 ≤ base then 1 else if h = true then 1 else 0)) = 2 := by
        rw [if_pos hpre]
      rw [hlen]
    · -- rex 68
      have hb0 : (byteListReader (movMRZ8Bytes h src base disp) 0).toNat = 68 := by
        simp [movMRZ8Bytes, byteListReader, byte, hs8, hb8]
      have hb1 : (byteListReader (movMRZ8Bytes h src base disp) 1).toNat = 0x88 := by
        simp [movMRZ8Bytes, byteListReader, byte, hs8, hb8]
      have hpm := parseRM_rmBase_z64 (byte 68) (byte 0x88) (src % 8) base
        (Nat.mod_lt src (by norm_num)) hb disp hlo hhi
      have hdt : decide (8 ≤ base) = false := by simp; omega
      rw [hdt] at hpm
      have hpm' : parseRM (byteListReader (byte 68 :: byte 0x88 :: byte
          ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
              8 * (src % 8) + base % 8) ::
          ((if base % 8 = 4 then [byte 0x24] else []) ++
           (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
             [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 false =
          some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
                 regBits := src % 8, rm := .zm none (.regBase base) disp,
                 len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
        simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
      simp only [decode, decodeNoRex]
      rw [hb0]
      simp only [Nat.reduceMod, Nat.reduceLeDiff]
      simp only [decide_true, Bool.true_and, if_true]
      rw [show decide (4 ≥ 8) = false from by decide,
          show decide (4 ≥ 4) = true from by decide,
          show decide (0 = 1) = false from by decide]
      simp only [decodeRex, hb1]
      have hpfx : (if 8 ≤ src ∨ 8 ≤ base then
          [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))]
         else if h = true then [byte 0x40] else []) = [byte 68] := by
        rw [if_pos (Or.inl hs8), if_pos hs8, if_neg hb8]
      simp only [movMRZ8Bytes, hpfx, if_true, List.cons_append, List.nil_append]
      rw [hpm']
      simp only [hmod3, if_false, baseOfRM]
      have hsrc : 8 + src % 8 = src := by
        rw [Nat.mod_eq_sub_mod hs8, Nat.mod_eq_of_lt (by omega)]
        omega
      rw [hsrc]
      have hflag : (if 8 ≤ src ∨ 8 ≤ base then true else h) = true := by
        rw [if_pos hpre]
      rw [hflag]
      have hlen : (1 + (if 8 ≤ src ∨ 8 ≤ base then 1 else if h = true then 1 else 0)) = 2 := by
        rw [if_pos hpre]
      rw [hlen]
    · -- rex 65
      have hb0 : (byteListReader (movMRZ8Bytes h src base disp) 0).toNat = 65 := by
        simp [movMRZ8Bytes, byteListReader, byte, hs8, hb8]
      have hb1 : (byteListReader (movMRZ8Bytes h src base disp) 1).toNat = 0x88 := by
        simp [movMRZ8Bytes, byteListReader, byte, hs8, hb8]
      have hpm := parseRM_rmBase_z64 (byte 65) (byte 0x88) (src % 8) base
        (Nat.mod_lt src (by norm_num)) hb disp hlo hhi
      have hdt : decide (8 ≤ base) = true := by simp [hb8]
      rw [hdt] at hpm
      have hpm' : parseRM (byteListReader (byte 65 :: byte 0x88 :: byte
          ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
              8 * (src % 8) + base % 8) ::
          ((if base % 8 = 4 then [byte 0x24] else []) ++
           (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
             [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 true =
          some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
                 regBits := src % 8, rm := .zm none (.regBase base) disp,
                 len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
        simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
      simp only [decode, decodeNoRex]
      rw [hb0]
      simp only [Nat.reduceMod, Nat.reduceLeDiff]
      simp only [decide_true, Bool.true_and, if_true]
      rw [show decide (1 ≥ 8) = false from by decide,
          show decide (1 ≥ 4) = false from by decide]
      simp only [decodeRex, hb1]
      have hpfx : (if 8 ≤ src ∨ 8 ≤ base then
          [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))]
         else if h = true then [byte 0x40] else []) = [byte 65] := by
        rw [if_pos (Or.inr hb8), if_neg hs8, if_pos hb8]
      simp only [movMRZ8Bytes, hpfx, List.cons_append, List.nil_append]
      rw [hpm']
      simp only [hmod3, if_false, Bool.false_eq_true, baseOfRM]
      have hsrc : 0 + src % 8 = src := by
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      rw [hsrc]
      have hflag : (if 8 ≤ src ∨ 8 ≤ base then true else h) = true := by
        rw [if_pos hpre]
      rw [hflag]
      have hlen : (1 + (if 8 ≤ src ∨ 8 ≤ base then 1 else if h = true then 1 else 0)) = 2 := by
        rw [if_pos hpre]
      rw [hlen]
    · exact absurd hpre (by omega)
  · have hs8 : ¬ 8 ≤ src := by omega
    have hb8 : ¬ 8 ≤ base := by omega
    cases h
    · -- h = false: no prefix
      have hb0 : (byteListReader (movMRZ8Bytes false src base disp) 0).toNat = 0x88 := by
        simp [movMRZ8Bytes, byteListReader, byte, hs8, hb8]
      have hpm := parseRM_rmBase_noRex (byte 0x88) (src % 8) base
        (Nat.mod_lt src (by norm_num)) (by omega) disp hlo hhi
      have hpm' : parseRM (byteListReader (byte 0x88 :: byte
          ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
              8 * (src % 8) + base % 8) ::
          ((if base % 8 = 4 then [byte 0x24] else []) ++
           (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
             [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 1 false =
          some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
                 regBits := src % 8, rm := .zm none (.regBase base) disp,
                 len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
        simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
      simp only [decode, decodeNoRex]
      rw [hb0]
      have hpfx : (if 8 ≤ src ∨ 8 ≤ base then
          [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))]
         else if false = true then [byte 0x40] else []) = [] := by
        rw [if_neg hpre, if_neg (by decide : ¬ ((false = true)))]
      simp only [movMRZ8Bytes, hpfx, List.nil_append, List.cons_append]
      rw [hpm']
      simp only [hmod3, if_false, baseOfRM]
      have hsrc : src % 8 = src := Nat.mod_eq_of_lt (by omega)
      rw [hsrc]
      have hflag : (if 8 ≤ src ∨ 8 ≤ base then true else false) = false := by
        rw [if_neg hpre]
      rw [hflag]
      have hlen : (1 + (if 8 ≤ src ∨ 8 ≤ base then 1 else if false = true then 1 else 0)) = 1 := by
        rw [if_neg hpre, if_neg (by decide : ¬ ((false = true)))]
      rw [hlen]
    · -- h = true: REX 0x40
      have hb0 : (byteListReader (movMRZ8Bytes true src base disp) 0).toNat = 0x40 := by
        simp [movMRZ8Bytes, byteListReader, byte, hs8, hb8]
      have hb1 : (byteListReader (movMRZ8Bytes true src base disp) 1).toNat = 0x88 := by
        simp [movMRZ8Bytes, byteListReader, byte, hs8, hb8]
      have hpm := parseRM_rmBase_z64 (byte 0x40) (byte 0x88) (src % 8) base
        (Nat.mod_lt src (by norm_num)) hb disp hlo hhi
      have hdt : decide (8 ≤ base) = false := by simp; omega
      rw [hdt] at hpm
      have hpm' : parseRM (byteListReader (byte 0x40 :: byte 0x88 :: byte
          ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
              8 * (src % 8) + base % 8) ::
          ((if base % 8 = 4 then [byte 0x24] else []) ++
           (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
             [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 false =
          some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
                 regBits := src % 8, rm := .zm none (.regBase base) disp,
                 len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
        simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
      simp only [decode, decodeNoRex]
      rw [hb0]
      simp only [Nat.reduceMod, Nat.reduceLeDiff]
      simp only [decide_true, Bool.true_and, if_true]
      rw [show decide (0 ≥ 8) = false from by decide,
          show decide (0 ≥ 4) = false from by decide,
          show decide (0 = 1) = false from by decide]
      simp only [decodeRex, hb1]
      have hpfx : (if 8 ≤ src ∨ 8 ≤ base then
          [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))]
         else [byte 0x40]) = [byte 0x40] := by
        rw [if_neg hpre]
      simp only [movMRZ8Bytes, hpfx, if_true, List.cons_append, List.nil_append]
      rw [hpm']
      simp only [hmod3, if_false, Bool.false_eq_true, baseOfRM]
      have hsrc : 0 + src % 8 = src := by
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      rw [hsrc]
      have hflag : (if 8 ≤ src ∨ 8 ≤ base then true else true) = true := by
        rw [if_neg hpre]
      rw [hflag]
      have hlen : (1 + (if 8 ≤ src ∨ 8 ≤ base then 1 else 1)) = 2 := by
        rw [if_neg hpre]
      rw [hlen]

end Flapjack.Compiler.Encoders.X64

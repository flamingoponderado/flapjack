module

public import Mathlib.Tactic
public import Flapjack.Compiler.Encoders.X64.Machine.Bytes

@[expose] public section

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
      simp only [ite_eq_left hcond, ite_eq_left hsib]
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
        simp only [ite_eq_right hcond, ite_eq_left h8, ite_eq_left hsib]
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
        simp only [ite_eq_right hcond, ite_eq_right h8, ite_eq_left hsib]
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
    · simp only [ite_eq_left h0, ite_eq_right hsib]
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
      · simp only [ite_eq_right h0, ite_eq_left h8, ite_eq_right hsib]
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
      · simp only [ite_eq_right h0, ite_eq_right h8, ite_eq_right hsib]
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
    simp only [hd8, hb8, ite_true, ite_false] at hpm ⊢
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
      · rw [ite_eq_left h1] at h; omega
      · rw [ite_eq_right h1] at h
        by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
        · rw [ite_eq_left h2] at h; omega
        · rw [ite_eq_right h2] at h; omega
    rw [ite_eq_right hmod]
    try simp only [ite_true]
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
    simp only [hs8, hb8, ite_true, ite_false] at hpm ⊢
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
      · rw [ite_eq_left h1] at h; omega
      · rw [ite_eq_right h1] at h
        by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
        · rw [ite_eq_left h2] at h; omega
        · rw [ite_eq_right h2] at h; omega
    rw [ite_eq_right hmod]
    try simp only [ite_true]
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
    · rw [ite_eq_left h1] at h; omega
    · rw [ite_eq_right h1] at h
      by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
      · rw [ite_eq_left h2] at h; omega
      · rw [ite_eq_right h2] at h; omega
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
      rw [ite_eq_left (Or.inl hd8), ite_eq_left hd8, ite_eq_left hb8]
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    try simp only [ite_true]
    simp only [decodeRex, hb1]
    simp only [movRMZ32Bytes, hpre]
    simp only [List.singleton_append, decide_true]
    rw [hpm]
    simp only [baseOfRM]
    rw [ite_eq_right hmod3]
    try simp only [decide_true]
    rw [ite_eq_left (by rfl : (true && true) = true)]
    rw [show decide (5 ≥ 8) = false from by decide, show decide (5 ≥ 4) = true from by decide]
    simp only [ite_eq_right (by decide : ¬ false = true)]
    try simp only [ite_true]
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
      rw [ite_eq_left (Or.inl hd8), ite_eq_left hd8, ite_eq_right hb8]
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    try simp only [ite_true]
    simp only [decodeRex, hb1]
    simp only [movRMZ32Bytes, hpre]
    simp only [List.singleton_append]
    rw [show decide (0 = 1) = false from by decide]
    rw [hpm]
    simp only [baseOfRM]
    rw [ite_eq_right hmod3]
    try simp only [decide_true]
    rw [ite_eq_left (by rfl : (true && true) = true)]
    rw [show decide (4 ≥ 8) = false from by decide, show decide (4 ≥ 4) = true from by decide]
    simp only [ite_eq_right (by decide : ¬ false = true)]
    try simp only [ite_true]
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
      rw [ite_eq_left (Or.inr hb8), ite_eq_right hd8, ite_eq_left hb8]
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    try simp only [ite_true]
    simp only [decodeRex, hb1]
    simp only [movRMZ32Bytes, hpre]
    simp only [List.singleton_append, decide_true]
    rw [hpm]
    simp only [baseOfRM]
    rw [ite_eq_right hmod3]
    try simp only [decide_true]
    rw [ite_eq_left (by rfl : (true && true) = true)]
    rw [show decide (1 ≥ 8) = false from by decide, show decide (1 ≥ 4) = false from by decide]
    simp only [ite_eq_right (by decide : ¬ false = true)]
    try simp only [ite_true]
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
      rw [ite_eq_right (by omega : ¬ (8 ≤ dst ∨ 8 ≤ base))]
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [movRMZ32Bytes, hpre, List.nil_append]
    rw [hpm]
    simp only [baseOfRM]
    rw [ite_eq_right hmod3]
    try simp only [ite_true]
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
  · simp only [movMRZ32Bytes, hpre, ite_true]
    have h := parseRM_rmBase_z64
      (byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0)))
      (byte 0x89) (src % 8) base (by omega) hb disp hlo hhi
    simpa using h
  · simp only [movMRZ32Bytes, hpre, ite_false, List.nil_append]
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
    · rw [ite_eq_left h1] at h; omega
    · rw [ite_eq_right h1] at h
      by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
      · rw [ite_eq_left h2] at h; omega
      · rw [ite_eq_right h2] at h; omega
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
      rw [ite_eq_left (Or.inl hs8), ite_eq_left hs8, ite_eq_left hb8]
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    try simp only [ite_true]
    simp only [decodeRex, hb1]
    simp only [movMRZ32Bytes, hpre]
    simp only [List.singleton_append, decide_true]
    rw [hpm]
    simp only [baseOfRM]
    rw [ite_eq_right hmod3]
    try simp only [decide_true]
    rw [ite_eq_left (by rfl : (true && true) = true)]
    rw [show decide (5 ≥ 8) = false from by decide, show decide (5 ≥ 4) = true from by decide]
    simp only [ite_eq_right (by decide : ¬ false = true)]
    try simp only [ite_true]
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
      rw [ite_eq_left (Or.inl hs8), ite_eq_left hs8, ite_eq_right hb8]
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    try simp only [ite_true]
    simp only [decodeRex, hb1]
    simp only [movMRZ32Bytes, hpre]
    simp only [List.singleton_append]
    rw [show decide (0 = 1) = false from by decide]
    rw [hpm]
    simp only [baseOfRM]
    rw [ite_eq_right hmod3]
    try simp only [decide_true]
    rw [ite_eq_left (by rfl : (true && true) = true)]
    rw [show decide (4 ≥ 8) = false from by decide, show decide (4 ≥ 4) = true from by decide]
    simp only [ite_eq_right (by decide : ¬ false = true)]
    try simp only [ite_true]
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
      rw [ite_eq_left (Or.inr hb8), ite_eq_right hs8, ite_eq_left hb8]
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    try simp only [ite_true]
    simp only [decodeRex, hb1]
    simp only [movMRZ32Bytes, hpre]
    simp only [List.singleton_append, decide_true]
    rw [hpm]
    simp only [baseOfRM]
    rw [ite_eq_right hmod3]
    try simp only [decide_true]
    rw [ite_eq_left (by rfl : (true && true) = true)]
    rw [show decide (1 ≥ 8) = false from by decide, show decide (1 ≥ 4) = false from by decide]
    simp only [ite_eq_right (by decide : ¬ false = true)]
    try simp only [ite_true]
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
      rw [ite_eq_right (by omega : ¬ (8 ≤ src ∨ 8 ≤ base))]
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [movMRZ32Bytes, hpre, List.nil_append]
    rw [hpm]
    simp only [baseOfRM]
    rw [ite_eq_right hmod3]
    try simp only [ite_true]
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
    · rw [ite_eq_left h1] at h; omega
    · rw [ite_eq_right h1] at h
      by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
      · rw [ite_eq_left h2] at h; omega
      · rw [ite_eq_right h2] at h; omega
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
    simp only [decide_true, Bool.true_and, ite_true, ite_false, Nat.reduceEqDiff]
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [byte 69] := by
      rw [ite_eq_left (Or.inl hs8), ite_eq_left hs8, ite_eq_left hb8]
    simp only [movMRZ16Bytes, hpre, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [hmod3, ite_false, baseOfRM]
    have hsrc : (if (5:ℕ) ≥ 4 then 8 else 0) + src % 8 = src := by
      rw [ite_eq_left (by decide : (5:ℕ) ≥ 4), Nat.mod_eq_sub_mod hs8, Nat.mod_eq_of_lt (by omega)]
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
    simp only [decide_true, decide_false, Bool.true_and, ite_true, ite_false, Nat.reduceEqDiff]
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [byte 68] := by
      rw [ite_eq_left (Or.inl hs8), ite_eq_left hs8, ite_eq_right hb8]
    simp only [movMRZ16Bytes, hpre, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [hmod3, ite_false, baseOfRM]
    have hsrc : (if (4:ℕ) ≥ 4 then 8 else 0) + src % 8 = src := by
      rw [ite_eq_left (by decide : (4:ℕ) ≥ 4), Nat.mod_eq_sub_mod hs8, Nat.mod_eq_of_lt (by omega)]
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
    simp only [decide_true, Bool.true_and, ite_true, ite_false, Nat.reduceEqDiff]
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [byte 65] := by
      rw [ite_eq_left (Or.inr hb8), ite_eq_right hs8, ite_eq_left hb8]
    simp only [movMRZ16Bytes, hpre, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [hmod3, ite_false, baseOfRM]
    have hsrc : (if (1:ℕ) ≥ 4 then 8 else 0) + src % 8 = src := by
      rw [ite_eq_right (by decide : ¬ ((1:ℕ) ≥ 4)), Nat.mod_eq_of_lt (by omega)]
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
    simp only [decide_true, decide_false, Bool.true_and, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff]
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [] := by
      rw [ite_eq_right (by omega : ¬ (8 ≤ src ∨ 8 ≤ base))]
    simp only [movMRZ16Bytes, hpre, List.cons_append, List.nil_append]
    rw [hpm']
    simp only [hmod3, ite_false, baseOfRM]
    have hsrc : src % 8 = src := Nat.mod_eq_of_lt (by omega)
    have hlen : 2 + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) =
        (2 + (if 8 ≤ src ∨ 8 ≤ base then 1 else 0)) + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
      rw [ite_eq_right (by omega : ¬ (8 ≤ src ∨ 8 ≤ base))]
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
    · rw [ite_eq_left h1] at h; omega
    · rw [ite_eq_right h1] at h
      by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
      · rw [ite_eq_left h2] at h; omega
      · rw [ite_eq_right h2] at h; omega
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
    simp only [decide_true, Bool.true_and, ite_true, ite_false, Nat.reduceEqDiff]
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [byte 69] := by
      rw [ite_eq_left (Or.inl hs8), ite_eq_left hs8, ite_eq_left hb8]
    simp only [movRMZ16Bytes, hpre, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [hmod3, ite_false, baseOfRM]
    have hsrc : (if (5:ℕ) ≥ 4 then 8 else 0) + src % 8 = src := by
      rw [ite_eq_left (by decide : (5:ℕ) ≥ 4), Nat.mod_eq_sub_mod hs8, Nat.mod_eq_of_lt (by omega)]
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
    simp only [decide_true, decide_false, Bool.true_and, ite_true, ite_false, Nat.reduceEqDiff]
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [byte 68] := by
      rw [ite_eq_left (Or.inl hs8), ite_eq_left hs8, ite_eq_right hb8]
    simp only [movRMZ16Bytes, hpre, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [hmod3, ite_false, baseOfRM]
    have hsrc : (if (4:ℕ) ≥ 4 then 8 else 0) + src % 8 = src := by
      rw [ite_eq_left (by decide : (4:ℕ) ≥ 4), Nat.mod_eq_sub_mod hs8, Nat.mod_eq_of_lt (by omega)]
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
    simp only [decide_true, Bool.true_and, ite_true, ite_false, Nat.reduceEqDiff]
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [byte 65] := by
      rw [ite_eq_left (Or.inr hb8), ite_eq_right hs8, ite_eq_left hb8]
    simp only [movRMZ16Bytes, hpre, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [hmod3, ite_false, baseOfRM]
    have hsrc : (if (1:ℕ) ≥ 4 then 8 else 0) + src % 8 = src := by
      rw [ite_eq_right (by decide : ¬ ((1:ℕ) ≥ 4)), Nat.mod_eq_of_lt (by omega)]
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
    simp only [decide_true, decide_false, Bool.true_and, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff]
    have hpre : (if 8 ≤ src ∨ 8 ≤ base then
        [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))] else []) = [] := by
      rw [ite_eq_right (by omega : ¬ (8 ≤ src ∨ 8 ≤ base))]
    simp only [movRMZ16Bytes, hpre, List.cons_append, List.nil_append]
    rw [hpm']
    simp only [hmod3, ite_false, baseOfRM]
    have hsrc : src % 8 = src := Nat.mod_eq_of_lt (by omega)
    have hlen : 2 + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) =
        (2 + (if 8 ≤ src ∨ 8 ≤ base then 1 else 0)) + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
      rw [ite_eq_right (by omega : ¬ (8 ≤ src ∨ 8 ≤ base))]
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
    · rw [ite_eq_left h1] at hh; omega
    · rw [ite_eq_right h1] at hh
      by_cases h2 : -128 ≤ disp.toInt ∧ disp.toInt ≤ 127
      · rw [ite_eq_left h2] at hh; omega
      · rw [ite_eq_right h2] at hh; omega
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
      simp only [decide_true, Bool.true_and, ite_true]
      rw [show decide (5 ≥ 8) = false from by decide,
          show decide (5 ≥ 4) = true from by decide]
      simp only [decodeRex, hb1]
      have hpfx : (if 8 ≤ src ∨ 8 ≤ base then
          [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))]
         else if h = true then [byte 0x40] else []) = [byte 69] := by
        rw [ite_eq_left (Or.inl hs8), ite_eq_left hs8, ite_eq_left hb8]
      simp only [movMRZ8Bytes, hpfx, ite_true, List.cons_append, List.nil_append]
      rw [hpm']
      simp only [hmod3, ite_false, baseOfRM]
      have hsrc : 8 + src % 8 = src := by
        rw [Nat.mod_eq_sub_mod hs8, Nat.mod_eq_of_lt (by omega)]
        omega
      rw [hsrc]
      have hflag : (if 8 ≤ src ∨ 8 ≤ base then true else h) = true := by
        rw [ite_eq_left hpre]
      rw [hflag]
      have hlen : (1 + (if 8 ≤ src ∨ 8 ≤ base then 1 else if h = true then 1 else 0)) = 2 := by
        rw [ite_eq_left hpre]
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
      simp only [decide_true, Bool.true_and, ite_true]
      rw [show decide (4 ≥ 8) = false from by decide,
          show decide (4 ≥ 4) = true from by decide,
          show decide (0 = 1) = false from by decide]
      simp only [decodeRex, hb1]
      have hpfx : (if 8 ≤ src ∨ 8 ≤ base then
          [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))]
         else if h = true then [byte 0x40] else []) = [byte 68] := by
        rw [ite_eq_left (Or.inl hs8), ite_eq_left hs8, ite_eq_right hb8]
      simp only [movMRZ8Bytes, hpfx, ite_true, List.cons_append, List.nil_append]
      rw [hpm']
      simp only [hmod3, ite_false, baseOfRM]
      have hsrc : 8 + src % 8 = src := by
        rw [Nat.mod_eq_sub_mod hs8, Nat.mod_eq_of_lt (by omega)]
        omega
      rw [hsrc]
      have hflag : (if 8 ≤ src ∨ 8 ≤ base then true else h) = true := by
        rw [ite_eq_left hpre]
      rw [hflag]
      have hlen : (1 + (if 8 ≤ src ∨ 8 ≤ base then 1 else if h = true then 1 else 0)) = 2 := by
        rw [ite_eq_left hpre]
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
      simp only [decide_true, Bool.true_and, ite_true]
      rw [show decide (1 ≥ 8) = false from by decide,
          show decide (1 ≥ 4) = false from by decide]
      simp only [decodeRex, hb1]
      have hpfx : (if 8 ≤ src ∨ 8 ≤ base then
          [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))]
         else if h = true then [byte 0x40] else []) = [byte 65] := by
        rw [ite_eq_left (Or.inr hb8), ite_eq_right hs8, ite_eq_left hb8]
      simp only [movMRZ8Bytes, hpfx, List.cons_append, List.nil_append]
      rw [hpm']
      simp only [hmod3, ite_false, Bool.false_eq_true, baseOfRM]
      have hsrc : 0 + src % 8 = src := by
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      rw [hsrc]
      have hflag : (if 8 ≤ src ∨ 8 ≤ base then true else h) = true := by
        rw [ite_eq_left hpre]
      rw [hflag]
      have hlen : (1 + (if 8 ≤ src ∨ 8 ≤ base then 1 else if h = true then 1 else 0)) = 2 := by
        rw [ite_eq_left hpre]
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
        rw [ite_eq_right hpre, ite_eq_right (by decide : ¬ ((false = true)))]
      simp only [movMRZ8Bytes, hpfx, List.nil_append, List.cons_append]
      rw [hpm']
      simp only [hmod3, ite_false, baseOfRM]
      have hsrc : src % 8 = src := Nat.mod_eq_of_lt (by omega)
      rw [hsrc]
      have hflag : (if 8 ≤ src ∨ 8 ≤ base then true else false) = false := by
        rw [ite_eq_right hpre]
      rw [hflag]
      have hlen : (1 + (if 8 ≤ src ∨ 8 ≤ base then 1 else if false = true then 1 else 0)) = 1 := by
        rw [ite_eq_right hpre, ite_eq_right (by decide : ¬ ((false = true)))]
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
      simp only [decide_true, Bool.true_and, ite_true]
      rw [show decide (0 ≥ 8) = false from by decide,
          show decide (0 ≥ 4) = false from by decide,
          show decide (0 = 1) = false from by decide]
      simp only [decodeRex, hb1]
      have hpfx : (if 8 ≤ src ∨ 8 ≤ base then
          [byte (64 + (if 8 ≤ src then 4 else 0) + (if 8 ≤ base then 1 else 0))]
         else [byte 0x40]) = [byte 0x40] := by
        rw [ite_eq_right hpre]
      simp only [movMRZ8Bytes, hpfx, ite_true, List.cons_append, List.nil_append]
      rw [hpm']
      simp only [hmod3, ite_false, Bool.false_eq_true, baseOfRM]
      have hsrc : 0 + src % 8 = src := by
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      rw [hsrc]
      have hflag : (if 8 ≤ src ∨ 8 ≤ base then true else true) = true := by
        rw [ite_eq_right hpre]
      rw [hflag]
      have hlen : (1 + (if 8 ≤ src ∨ 8 ≤ base then 1 else 1)) = 2 := by
        rw [ite_eq_right hpre]
      rw [hlen]

/-- The encoded byte list of `movzxRM sz1 .z64` (the emitted zero-extending loads). -/
abbrev movzxBytes (opc : BitVec 8) (dst base : Nat) (disp : BitVec 64) : List (BitVec 8) :=
  [byte (72 + (if 8 ≤ dst then 4 else 0) + (if 8 ≤ base then 1 else 0)),
   byte 0x0F, opc,
   byte ((if disp = 0 ∧ base % 8 ≠ 5 then 0
          else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
         8 * (dst % 8) + base % 8)] ++
  (if base % 8 = 4 then [byte 0x24] else []) ++
  (if disp = 0 ∧ base % 8 ≠ 5 then []
   else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat]
   else [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536),
     byte (disp.toNat / 16777216)])

theorem encodeInsn_movzxRM_z16 (dst base : Nat) (hd : dst < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    encodeInsn (.movzxRM .z16 .z64 dst base disp) = movzxBytes (byte 0xB7) dst base disp := by
  simp only [encodeInsn]
  simp only [ite_true]
  rw [eGenRmReg_regBase .z64 dst base hd hb disp hlo hhi [byte 0x0F] (byte 0xB6) (some 1)]
  simp [movzxBytes]
  decide

theorem encodeInsn_movzxRM_z8 (dst base : Nat) (hd : dst < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    encodeInsn (.movzxRM (.z8 true) .z64 dst base disp) = movzxBytes (byte 0xB6) dst base disp := by
  simp only [encodeInsn]
  rw [ite_eq_right (by decide : ¬ (ZSize.z8 true = ZSize.z16))]
  rw [eGenRmReg_regBase .z64 dst base hd hb disp hlo hhi [byte 0x0F] (byte 0xB6) (some 0)]
  simp [movzxBytes]

set_option maxHeartbeats 1000000 in
theorem decode_movzxRM_z16 (dst base : Nat) (hd : dst < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    decode (byteListReader (encodeInsn (.movzxRM .z16 .z64 dst base disp))) =
      some (.movzxRM .z16 .z64 dst base disp,
        3 + ((if base % 8 = 4 then 1 else 0) +
          (if disp = 0 ∧ base % 8 ≠ 5 then 1
           else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5))) := by
  rw [encodeInsn_movzxRM_z16 dst base hd hb disp hlo hhi]
  by_cases hd8 : 8 ≤ dst <;> by_cases hb8 : 8 ≤ base
  · have hb0 : (byteListReader (movzxBytes (byte 0xB7) dst base disp) 0).toNat = 77 := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hb1 : (byteListReader (movzxBytes (byte 0xB7) dst base disp) 1).toNat = 0x0F := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hb2 : (byteListReader (movzxBytes (byte 0xB7) dst base disp) 2).toNat = 0xB7 := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 0x0F) (byte 0xB7) (dst % 8) base
      (Nat.mod_lt dst (by norm_num)) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = true := by simp [hb8]
    rw [hdt] at hpm
    have hpm' : parseRM (byteListReader (byte 0x0F :: byte 0xB7 :: byte
        ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
            8 * (dst % 8) + base % 8) ::
        ((if base % 8 = 4 then [byte 0x24] else []) ++
         (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
           [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 true =
        some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
               regBits := dst % 8, rm := .zm none (.regBase base) disp,
               len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
      simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    simp only [decide_true, Bool.true_and, ite_true]
    rw [show decide (5 ≥ 4) = true from by decide]
    simp only [decodeRex, hb1]
    rw [hb2]
    simp only [Nat.reduceLeDiff, Nat.reduceEqDiff, decide_true, decide_false,
      Bool.true_and, Bool.false_eq_true, ite_false]
    simp only [movzxBytes, ite_true, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [baseOfRM]
    have hsrc : 8 + dst % 8 = dst := by
      rw [Nat.mod_eq_sub_mod hd8, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hsrc]
  · have hb0 : (byteListReader (movzxBytes (byte 0xB7) dst base disp) 0).toNat = 76 := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hb1 : (byteListReader (movzxBytes (byte 0xB7) dst base disp) 1).toNat = 0x0F := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hb2 : (byteListReader (movzxBytes (byte 0xB7) dst base disp) 2).toNat = 0xB7 := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 0x0F) (byte 0xB7) (dst % 8) base
      (Nat.mod_lt dst (by norm_num)) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = false := by simp; omega
    rw [hdt] at hpm
    have hpm' : parseRM (byteListReader (byte 0x0F :: byte 0xB7 :: byte
        ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
            8 * (dst % 8) + base % 8) ::
        ((if base % 8 = 4 then [byte 0x24] else []) ++
         (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
           [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 false =
        some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
               regBits := dst % 8, rm := .zm none (.regBase base) disp,
               len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
      simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    simp only [decide_true, Bool.true_and, ite_true]
    rw [show decide (4 ≥ 4) = true from by decide,
        show decide (0 = 1) = false from by decide]
    simp only [decodeRex, hb1]
    rw [hb2]
    simp only [Nat.reduceLeDiff, Nat.reduceEqDiff, decide_true, decide_false,
      Bool.true_and, Bool.false_eq_true, ite_false]
    simp only [movzxBytes, ite_true, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [baseOfRM]
    have hsrc : 8 + dst % 8 = dst := by
      rw [Nat.mod_eq_sub_mod hd8, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hsrc]
  · have hb0 : (byteListReader (movzxBytes (byte 0xB7) dst base disp) 0).toNat = 73 := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hb1 : (byteListReader (movzxBytes (byte 0xB7) dst base disp) 1).toNat = 0x0F := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hb2 : (byteListReader (movzxBytes (byte 0xB7) dst base disp) 2).toNat = 0xB7 := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 0x0F) (byte 0xB7) (dst % 8) base
      (Nat.mod_lt dst (by norm_num)) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = true := by simp [hb8]
    rw [hdt] at hpm
    have hpm' : parseRM (byteListReader (byte 0x0F :: byte 0xB7 :: byte
        ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
            8 * (dst % 8) + base % 8) ::
        ((if base % 8 = 4 then [byte 0x24] else []) ++
         (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
           [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 true =
        some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
               regBits := dst % 8, rm := .zm none (.regBase base) disp,
               len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
      simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    simp only [decide_true, Bool.true_and, ite_true]
    rw [show decide (1 ≥ 4) = false from by decide]
    simp only [decodeRex, hb1]
    rw [hb2]
    simp only [Nat.reduceLeDiff, Nat.reduceEqDiff, decide_true, decide_false,
      Bool.true_and, Bool.false_eq_true, ite_false]
    simp only [movzxBytes, ite_true, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [baseOfRM]
    have hsrc : 0 + dst % 8 = dst := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hsrc]
  · have hb0 : (byteListReader (movzxBytes (byte 0xB7) dst base disp) 0).toNat = 72 := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hb1 : (byteListReader (movzxBytes (byte 0xB7) dst base disp) 1).toNat = 0x0F := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hb2 : (byteListReader (movzxBytes (byte 0xB7) dst base disp) 2).toNat = 0xB7 := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 0x0F) (byte 0xB7) (dst % 8) base
      (Nat.mod_lt dst (by norm_num)) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = false := by simp; omega
    rw [hdt] at hpm
    have hpm' : parseRM (byteListReader (byte 0x0F :: byte 0xB7 :: byte
        ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
            8 * (dst % 8) + base % 8) ::
        ((if base % 8 = 4 then [byte 0x24] else []) ++
         (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
           [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 false =
        some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
               regBits := dst % 8, rm := .zm none (.regBase base) disp,
               len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
      simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    simp only [decide_true, Bool.true_and, ite_true]
    rw [show decide (0 ≥ 4) = false from by decide,
        show decide (0 = 1) = false from by decide]
    simp only [decodeRex, hb1]
    rw [hb2]
    simp only [Nat.reduceLeDiff, Nat.reduceEqDiff, decide_true, decide_false,
      Bool.true_and, Bool.false_eq_true, ite_false]
    simp only [movzxBytes, ite_true, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [baseOfRM]
    have hsrc : 0 + dst % 8 = dst := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hsrc]

set_option maxHeartbeats 1000000 in
theorem decode_movzxRM_z8 (dst base : Nat) (hd : dst < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    decode (byteListReader (encodeInsn (.movzxRM (.z8 true) .z64 dst base disp))) =
      some (.movzxRM (.z8 true) .z64 dst base disp,
        3 + ((if base % 8 = 4 then 1 else 0) +
          (if disp = 0 ∧ base % 8 ≠ 5 then 1
           else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5))) := by
  rw [encodeInsn_movzxRM_z8 dst base hd hb disp hlo hhi]
  by_cases hd8 : 8 ≤ dst <;> by_cases hb8 : 8 ≤ base
  · have hb0 : (byteListReader (movzxBytes (byte 0xB6) dst base disp) 0).toNat = 77 := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hb1 : (byteListReader (movzxBytes (byte 0xB6) dst base disp) 1).toNat = 0x0F := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hb2 : (byteListReader (movzxBytes (byte 0xB6) dst base disp) 2).toNat = 0xB6 := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 0x0F) (byte 0xB6) (dst % 8) base
      (Nat.mod_lt dst (by norm_num)) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = true := by simp [hb8]
    rw [hdt] at hpm
    have hpm' : parseRM (byteListReader (byte 0x0F :: byte 0xB6 :: byte
        ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
            8 * (dst % 8) + base % 8) ::
        ((if base % 8 = 4 then [byte 0x24] else []) ++
         (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
           [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 true =
        some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
               regBits := dst % 8, rm := .zm none (.regBase base) disp,
               len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
      simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    simp only [decide_true, Bool.true_and, ite_true]
    rw [show decide (5 ≥ 4) = true from by decide]
    simp only [decodeRex, hb1]
    rw [hb2]
    simp only [Nat.reduceLeDiff, Nat.reduceEqDiff, decide_true, decide_false,
      Bool.true_and, Bool.false_eq_true, ite_false]
    simp only [movzxBytes, ite_true, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [baseOfRM]
    have hsrc : 8 + dst % 8 = dst := by
      rw [Nat.mod_eq_sub_mod hd8, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hsrc]
  · have hb0 : (byteListReader (movzxBytes (byte 0xB6) dst base disp) 0).toNat = 76 := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hb1 : (byteListReader (movzxBytes (byte 0xB6) dst base disp) 1).toNat = 0x0F := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hb2 : (byteListReader (movzxBytes (byte 0xB6) dst base disp) 2).toNat = 0xB6 := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 0x0F) (byte 0xB6) (dst % 8) base
      (Nat.mod_lt dst (by norm_num)) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = false := by simp; omega
    rw [hdt] at hpm
    have hpm' : parseRM (byteListReader (byte 0x0F :: byte 0xB6 :: byte
        ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
            8 * (dst % 8) + base % 8) ::
        ((if base % 8 = 4 then [byte 0x24] else []) ++
         (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
           [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 false =
        some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
               regBits := dst % 8, rm := .zm none (.regBase base) disp,
               len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
      simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    simp only [decide_true, Bool.true_and, ite_true]
    rw [show decide (4 ≥ 4) = true from by decide,
        show decide (0 = 1) = false from by decide]
    simp only [decodeRex, hb1]
    rw [hb2]
    simp only [Nat.reduceLeDiff, Nat.reduceEqDiff, decide_true, decide_false,
      Bool.true_and, Bool.false_eq_true, ite_false]
    simp only [movzxBytes, ite_true, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [baseOfRM]
    have hsrc : 8 + dst % 8 = dst := by
      rw [Nat.mod_eq_sub_mod hd8, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hsrc]
  · have hb0 : (byteListReader (movzxBytes (byte 0xB6) dst base disp) 0).toNat = 73 := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hb1 : (byteListReader (movzxBytes (byte 0xB6) dst base disp) 1).toNat = 0x0F := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hb2 : (byteListReader (movzxBytes (byte 0xB6) dst base disp) 2).toNat = 0xB6 := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 0x0F) (byte 0xB6) (dst % 8) base
      (Nat.mod_lt dst (by norm_num)) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = true := by simp [hb8]
    rw [hdt] at hpm
    have hpm' : parseRM (byteListReader (byte 0x0F :: byte 0xB6 :: byte
        ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
            8 * (dst % 8) + base % 8) ::
        ((if base % 8 = 4 then [byte 0x24] else []) ++
         (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
           [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 true =
        some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
               regBits := dst % 8, rm := .zm none (.regBase base) disp,
               len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
      simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    simp only [decide_true, Bool.true_and, ite_true]
    rw [show decide (1 ≥ 4) = false from by decide]
    simp only [decodeRex, hb1]
    rw [hb2]
    simp only [Nat.reduceLeDiff, Nat.reduceEqDiff, decide_true, decide_false,
      Bool.true_and, Bool.false_eq_true, ite_false]
    simp only [movzxBytes, ite_true, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [baseOfRM]
    have hsrc : 0 + dst % 8 = dst := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hsrc]
  · have hb0 : (byteListReader (movzxBytes (byte 0xB6) dst base disp) 0).toNat = 72 := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hb1 : (byteListReader (movzxBytes (byte 0xB6) dst base disp) 1).toNat = 0x0F := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hb2 : (byteListReader (movzxBytes (byte 0xB6) dst base disp) 2).toNat = 0xB6 := by
      simp [movzxBytes, byteListReader, byte, hd8, hb8]
    have hpm := parseRM_rmBase_z64 (byte 0x0F) (byte 0xB6) (dst % 8) base
      (Nat.mod_lt dst (by norm_num)) hb disp hlo hhi
    have hdt : decide (8 ≤ base) = false := by simp; omega
    rw [hdt] at hpm
    have hpm' : parseRM (byteListReader (byte 0x0F :: byte 0xB6 :: byte
        ((if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 64 else 128) +
            8 * (dst % 8) + base % 8) ::
        ((if base % 8 = 4 then [byte 0x24] else []) ++
         (if disp = 0 ∧ base % 8 ≠ 5 then [] else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then [byte disp.toNat] else
           [byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536), byte (disp.toNat / 16777216)])))) 2 false =
        some { modBits := (if disp = 0 ∧ base % 8 ≠ 5 then 0 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 1 else 2),
               regBits := dst % 8, rm := .zm none (.regBase base) disp,
               len := (if base % 8 = 4 then 1 else 0) + (if disp = 0 ∧ base % 8 ≠ 5 then 1 else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) } := by
      simpa only [List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using hpm
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    simp only [decide_true, Bool.true_and, ite_true]
    rw [show decide (0 ≥ 4) = false from by decide,
        show decide (0 = 1) = false from by decide]
    simp only [decodeRex, hb1]
    rw [hb2]
    simp only [Nat.reduceLeDiff, Nat.reduceEqDiff, decide_true, decide_false,
      Bool.true_and, Bool.false_eq_true, ite_false]
    simp only [movzxBytes, ite_true, List.cons_append, List.nil_append]
    rw [parseRM_shift]
    rw [hpm']
    simp only [baseOfRM]
    have hsrc : 0 + dst % 8 = dst := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hsrc]

/-- The RIP-relative ModRM byte for register `k`: `5 | (k <<< 3) = 5 + 8k`. -/
theorem modrm_rip_byte (k : Nat) (hk : k < 8) :
    5#8 ||| BitVec.ofNat 8 (k <<< 3) = BitVec.ofNat 8 (5 + 8 * k) := by
  interval_cases k <;> decide

/-- The encoded byte list of `lea .z64 dst disp` (RIP-relative). -/
abbrev leaBytes (dst : Nat) (disp : BitVec 64) : List (BitVec 8) :=
  [byte (72 + (if 8 ≤ dst then 4 else 0)), byte 0x8D,
   byte (5 + 8 * (dst % 8)),
   byte disp.toNat, byte (disp.toNat / 256), byte (disp.toNat / 65536),
   byte (disp.toNat / 16777216)]

theorem encodeInsn_lea (dst : Nat) (hd : dst < 16) (disp : BitVec 64)
    (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    encodeInsn (.lea .z64 dst disp) = leaBytes dst disp := by
  simp only [encodeInsn, eGenRmReg, eModRM, eImm32, eOpsize, rexPrefix, mkRex]
  rw [ite_eq_left ⟨hlo, by omega⟩]
  by_cases hd8 : 8 ≤ dst
  · have hd8' : dst / 8 = 1 := by omega
    simp [leaBytes, hd8, hd8', byte, Nat.mod_eq_of_lt (by omega)]
    exact modrm_rip_byte (dst % 8) (Nat.mod_lt dst (by norm_num))
  · have hd8' : dst / 8 = 0 := by omega
    simp [leaBytes, hd8, hd8', byte, Nat.mod_eq_of_lt (by omega)]
    exact modrm_rip_byte (dst % 8) (Nat.mod_lt dst (by norm_num))

set_option maxHeartbeats 1000000 in
theorem decode_lea (dst : Nat) (hd : dst < 16) (disp : BitVec 64)
    (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    decode (byteListReader (encodeInsn (.lea .z64 dst disp))) =
      some (.lea .z64 dst disp, 7) := by
  rw [encodeInsn_lea dst hd disp hlo hhi]
  have hr : ∀ j, j < 4 → byteListReader (leaBytes dst disp) (3 + j) =
      byte (disp.toNat / 2^(8*j)) := by
    intro j hj
    interval_cases j <;> simp [leaBytes, byteListReader, byte]
  by_cases hd8 : 8 ≤ dst
  · have hb0 : (byteListReader (leaBytes dst disp) 0).toNat = 76 := by
      simp [leaBytes, byteListReader, byte, hd8]
    have hb1 : (byteListReader (leaBytes dst disp) 1).toNat = 0x8D := by
      simp [leaBytes, byteListReader, byte, hd8]
    have hm : (byteListReader (leaBytes dst disp) 2).toNat = 8 * (dst % 8) + 5 := by
      simp [leaBytes, byteListReader, byte, hd8]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hpm := parseRM_rip (byteListReader (leaBytes dst disp)) 2 (dst % 8) hm
      (Nat.mod_lt dst (by norm_num))
    have himm := imm32_eImm32_at disp 3 (byteListReader (leaBytes dst disp)) hr hlo hhi
    rw [himm] at hpm
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    simp only [decide_true, Bool.true_and, ite_true]
    rw [show decide (4 ≥ 4) = true from by decide,
        show decide (0 = 1) = false from by decide]
    simp only [decodeRex, hb1]
    simp only [leaBytes, ite_true]
    rw [hpm]
    simp only [Option.some.injEq, Prod.mk.injEq, X64Insn.lea.injEq, true_and, and_true]
    have hsrc : 8 + dst % 8 = dst := by
      rw [Nat.mod_eq_sub_mod hd8, Nat.mod_eq_of_lt (by omega)]
      omega
    exact hsrc
  · have hb0 : (byteListReader (leaBytes dst disp) 0).toNat = 72 := by
      simp [leaBytes, byteListReader, byte, hd8]
    have hb1 : (byteListReader (leaBytes dst disp) 1).toNat = 0x8D := by
      simp [leaBytes, byteListReader, byte, hd8]
    have hm : (byteListReader (leaBytes dst disp) 2).toNat = 8 * (dst % 8) + 5 := by
      simp [leaBytes, byteListReader, byte, hd8]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hpm := parseRM_rip (byteListReader (leaBytes dst disp)) 2 (dst % 8) hm
      (Nat.mod_lt dst (by norm_num))
    have himm := imm32_eImm32_at disp 3 (byteListReader (leaBytes dst disp)) hr hlo hhi
    rw [himm] at hpm
    simp only [decode, decodeNoRex]
    rw [hb0]
    simp only [Nat.reduceMod, Nat.reduceLeDiff]
    simp only [decide_true, Bool.true_and, ite_true]
    rw [show decide (0 ≥ 4) = false from by decide,
        show decide (0 = 1) = false from by decide]
    simp only [decodeRex, hb1]
    simp only [leaBytes]
    rw [hpm]
    simp only [Option.some.injEq, Prod.mk.injEq, X64Insn.lea.injEq, true_and, and_true]
    have hsrc : 0 + dst % 8 = dst := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    exact hsrc

theorem eImm32_eq (imm : BitVec 64)
    (hlo : -(2^31 : Int) ≤ imm.toInt) (hhi : imm.toInt < 2^31) :
    eImm32 imm = some [byte imm.toNat, byte (imm.toNat / 256), byte (imm.toNat / 65536),
      byte (imm.toNat / 16777216)] := by
  simp only [eImm32]
  rw [ite_eq_left ⟨hlo, by omega⟩]

theorem decode_jcc_always (imm : BitVec 64)
    (hlo : -(2^31 : Int) ≤ imm.toInt) (hhi : imm.toInt < 2^31) :
    decode (byteListReader (encodeInsn (.jcc .zAlways imm))) =
      some (.jcc .zAlways imm, 5) := by
  simp only [encodeInsn]
  rw [eImm32_eq imm hlo hhi]
  simp only [ite_true]
  have hr : ∀ j, j < 4 → byteListReader [byte 0xE9, byte imm.toNat, byte (imm.toNat / 256),
      byte (imm.toNat / 65536), byte (imm.toNat / 16777216)] (1 + j) =
      byte (imm.toNat / 2^(8*j)) := by
    intro j hj
    interval_cases j <;> simp [byteListReader, byte]
  have himm := imm32_eImm32_at imm 1
    (byteListReader [byte 0xE9, byte imm.toNat, byte (imm.toNat / 256),
      byte (imm.toNat / 65536), byte (imm.toNat / 16777216)]) hr hlo hhi
  simp only [decode, decodeNoRex]
  rw [show (byteListReader [byte 0xE9, byte imm.toNat, byte (imm.toNat / 256),
      byte (imm.toNat / 65536), byte (imm.toNat / 16777216)] 0).toNat = 0xE9 from by
    simp [byteListReader, byte]]
  simp
  rw [himm]

theorem eImm8_32_eq_four (imm : BitVec 64)
    (hnos : ¬ (-128 ≤ imm.toInt ∧ imm.toInt ≤ 127))
    (hlo : -(2^31 : Int) ≤ imm.toInt) (hhi : imm.toInt < 2^31) :
    eImm8_32 imm = some (4, [byte imm.toNat, byte (imm.toNat / 256), byte (imm.toNat / 65536),
      byte (imm.toNat / 16777216)]) := by
  unfold eImm8_32
  rw [show eImm8 imm = none from by unfold eImm8; rw [ite_eq_right hnos]]
  rw [eImm32_eq imm hlo hhi]

theorem condOfCode_code (cond : ZCond) (h : cond ≠ .zAlways) : condOfCode cond.code = some cond := by
  cases cond <;> first | rfl | (exact absurd rfl h)

/-- The bytes of the long conditional-jump form. -/
theorem decode_jcc_long_other (cond : ZCond) (hne : cond ≠ .zAlways) (hneP : cond ≠ .zP)
    (imm : BitVec 64) (hlo : -(2^31 : Int) ≤ imm.toInt) (hhi : imm.toInt < 2^31) :
    decode (byteListReader (encodeInsn (.jcc cond imm))) =
      some (.jcc cond imm, 6) := by
  simp only [encodeInsn]
  rw [ite_eq_right hne, ite_eq_right hneP, eImm32_eq imm hlo hhi]
  simp only [List.cons_append, List.nil_append]
  have hcode : cond.code < 16 := by
    cases cond <;> first | decide | (exact absurd rfl hne)
  have hb0 : (byteListReader [byte 0x0F, byte (0x80 + cond.code),
      byte imm.toNat, byte (imm.toNat / 256), byte (imm.toNat / 65536),
      byte (imm.toNat / 16777216)] 0).toNat = 0x0F := by
    simp [byteListReader, byte]
  have hb1 : (byteListReader [byte 0x0F, byte (0x80 + cond.code),
      byte imm.toNat, byte (imm.toNat / 256), byte (imm.toNat / 65536),
      byte (imm.toNat / 16777216)] 1).toNat = 0x80 + cond.code := by
    simp [byteListReader, byte]
    omega
  have hb1' : 0x80 ≤ (byteListReader [byte 0x0F, byte (0x80 + cond.code),
      byte imm.toNat, byte (imm.toNat / 256), byte (imm.toNat / 65536),
      byte (imm.toNat / 16777216)] 1).toNat ∧
      (byteListReader [byte 0x0F, byte (0x80 + cond.code),
      byte imm.toNat, byte (imm.toNat / 256), byte (imm.toNat / 65536),
      byte (imm.toNat / 16777216)] 1).toNat ≤ 0x8F := by
    rw [hb1]
    constructor <;> omega
  have hr : ∀ j, j < 4 → byteListReader [byte 0x0F, byte (0x80 + cond.code),
      byte imm.toNat, byte (imm.toNat / 256), byte (imm.toNat / 65536),
      byte (imm.toNat / 16777216)] (2 + j) = byte (imm.toNat / 2^(8*j)) := by
    intro j hj
    interval_cases j <;> simp [byteListReader, byte]
  have himm := imm32_eImm32_at imm 2
    (byteListReader [byte 0x0F, byte (0x80 + cond.code),
      byte imm.toNat, byte (imm.toNat / 256), byte (imm.toNat / 65536),
      byte (imm.toNat / 16777216)]) hr hlo hhi
  simp only [decode, decodeNoRex]
  rw [hb0]
  rw [hb1]
  have h1 : 128 ≤ 128 + cond.code := by omega
  have h2 : 128 + cond.code ≤ 143 := by omega
  rw [show decide (128 ≤ 128 + cond.code) = true from by simp [h1],
      show decide (128 + cond.code ≤ 143) = true from by simp [h2]]
  simp only [Bool.true_and, ite_true]
  rw [show 128 + cond.code - 128 = cond.code from by omega]
  simp only [condOfCode_code cond hne]
  rw [himm]

/-- The short conditional-jump form for the parity condition. -/
theorem decode_jcc_zP_short (imm : BitVec 64)
    (hs : -128 ≤ imm.toInt ∧ imm.toInt ≤ 127) :
    decode (byteListReader (encodeInsn (.jcc .zP imm))) =
      some (.jcc .zP imm, 2) := by
  have h8 : eImm8_32 imm = some (1, [byte imm.toNat]) := by
    unfold eImm8_32
    rw [show eImm8 imm = some [byte imm.toNat] from by unfold eImm8; rw [ite_eq_left hs]]
  have henc : encodeInsn (.jcc .zP imm) = [byte 0x7A, byte imm.toNat] := by
    simp only [encodeInsn, h8]
    rfl
  rw [henc]
  have hb0 : (byteListReader [byte 0x7A, byte imm.toNat] 0).toNat = 0x7A := by
    simp [byteListReader, byte]
  have hb1 : byteListReader [byte 0x7A, byte imm.toNat] 1 = byte imm.toNat := by
    simp [byteListReader, byte]
  have himm := imm8_at imm 1 (byteListReader [byte 0x7A, byte imm.toNat]) hb1
    (by omega) (by omega)
  simp only [decode, decodeNoRex]
  rw [hb0]
  simp
  rw [himm]

/-- The long conditional-jump form for the parity condition. -/
theorem decode_jcc_zP_long (imm : BitVec 64)
    (hnos : ¬ (-128 ≤ imm.toInt ∧ imm.toInt ≤ 127))
    (hlo : -(2^31 : Int) ≤ imm.toInt) (hhi : imm.toInt < 2^31) :
    decode (byteListReader (encodeInsn (.jcc .zP imm))) =
      some (.jcc .zP imm, 6) := by
  have h4 := eImm8_32_eq_four imm hnos hlo hhi
  have henc : encodeInsn (.jcc .zP imm) =
      [byte 0x0F, byte 0x8A, byte imm.toNat, byte (imm.toNat / 256),
        byte (imm.toNat / 65536), byte (imm.toNat / 16777216)] := by
    simp only [encodeInsn, h4]
    rfl
  rw [henc]
  have hb0 : (byteListReader [byte 0x0F, byte 0x8A, byte imm.toNat,
      byte (imm.toNat / 256), byte (imm.toNat / 65536),
      byte (imm.toNat / 16777216)] 0).toNat = 0x0F := by
    simp [byteListReader, byte]
  have hb1 : (byteListReader [byte 0x0F, byte 0x8A, byte imm.toNat,
      byte (imm.toNat / 256), byte (imm.toNat / 65536),
      byte (imm.toNat / 16777216)] 1).toNat = 0x80 + ZCond.zP.code := by
    simp [byteListReader, byte, ZCond.code]
  have hb1' : 0x80 ≤ (byteListReader [byte 0x0F, byte 0x8A, byte imm.toNat,
      byte (imm.toNat / 256), byte (imm.toNat / 65536),
      byte (imm.toNat / 16777216)] 1).toNat ∧
      (byteListReader [byte 0x0F, byte 0x8A, byte imm.toNat,
      byte (imm.toNat / 256), byte (imm.toNat / 65536),
      byte (imm.toNat / 16777216)] 1).toNat ≤ 0x8F := by
    rw [hb1]
    decide
  have hr : ∀ j, j < 4 → byteListReader [byte 0x0F, byte 0x8A, byte imm.toNat,
      byte (imm.toNat / 256), byte (imm.toNat / 65536),
      byte (imm.toNat / 16777216)] (2 + j) = byte (imm.toNat / 2^(8*j)) := by
    intro j hj
    interval_cases j <;> simp [byteListReader, byte]
  have himm := imm32_eImm32_at imm 2
    (byteListReader [byte 0x0F, byte 0x8A, byte imm.toNat,
      byte (imm.toNat / 256), byte (imm.toNat / 65536),
      byte (imm.toNat / 16777216)]) hr hlo hhi
  simp only [decode, decodeNoRex]
  rw [hb0]
  rw [hb1]
  have h1 : 128 ≤ 128 + ZCond.zP.code := by omega
  have h2 : 128 + ZCond.zP.code ≤ 143 := by omega
  rw [show decide (128 ≤ 128 + ZCond.zP.code) = true from by simp [h1],
      show decide (128 + ZCond.zP.code ≤ 143) = true from by simp [h2]]
  simp only [Bool.true_and, ite_true]
  rw [show 128 + ZCond.zP.code - 128 = ZCond.zP.code from by omega]
  simp only [condOfCode_code ZCond.zP (by decide)]
  rw [himm]

/-! ## Register-immediate binary operations -/

/-- The encoded byte list of the one-byte-immediate `0x83` form on a register. -/
abbrev binopRI83Bytes (opc dst : Nat) (imm : BitVec 64) : List (BitVec 8) :=
  [byte (0x48 + (if 8 ≤ dst then 1 else 0)), byte 0x83,
   byte (0xC0 + 8 * (opc % 8) + dst % 8), byte imm.toNat]

theorem encodeInsn_binopRI_83 (op : ZBinopName) (dst : Nat) (hd : dst < 16) (imm : BitVec 64)
    (hns : op ≠ .ztest) (hnsh : op.code / 8 ≠ 1)
    (hs : -128 ≤ imm.toInt ∧ imm.toInt ≤ 127) :
    encodeInsn (.binopRI op .z64 dst imm) = binopRI83Bytes op.code dst imm := by
  have hop : op = .zadd ∨ op = .zor ∨ op = .zadc ∨ op = .zsbb ∨ op = .zand ∨
      op = .zsub ∨ op = .zxor ∨ op = .zcmp := by
    cases op <;> simp_all [ZBinopName.code]
  have h8 : eImm8 imm = some [byte imm.toNat] := by unfold eImm8; rw [ite_eq_left hs]
  rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> interval_cases dst <;>
    simp only [encodeInsn, h8, Option.isSome_some, Bool.true_and, ite_true,
      ZBinopName.code, notByte, isRax, eRmImm8, eModRM, eOpsize, rexPrefix, mkRex, byte,
      binopRI83Bytes] <;>
    rfl

theorem binopOfExt_code (op : ZBinopName)
    (hop : op = .zadd ∨ op = .zor ∨ op = .zadc ∨ op = .zsbb ∨ op = .zand ∨
      op = .zsub ∨ op = .zxor ∨ op = .zcmp) :
    binopOfExt (op.code % 8) = some op := by
  rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem decode_binopRI_83 (op : ZBinopName) (dst : Nat) (hd : dst < 16) (imm : BitVec 64)
    (hns : op ≠ .ztest) (hnsh : op.code / 8 ≠ 1)
    (hs : -128 ≤ imm.toInt ∧ imm.toInt ≤ 127) :
    decode (byteListReader (encodeInsn (.binopRI op .z64 dst imm))) =
      some (.binopRI op .z64 dst imm, 4) := by
  have hop : op = .zadd ∨ op = .zor ∨ op = .zadc ∨ op = .zsbb ∨ op = .zand ∨
      op = .zsub ∨ op = .zxor ∨ op = .zcmp := by
    cases op <;> simp_all [ZBinopName.code]
  rw [encodeInsn_binopRI_83 op dst hd imm hns hnsh hs]
  have hb3 : byteListReader (binopRI83Bytes op.code dst imm) 3 = byte imm.toNat := by
    simp [binopRI83Bytes]
  rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> interval_cases dst
  all_goals
    have himm := imm8_at imm 3 (byteListReader (binopRI83Bytes _ _ imm)) hb3
      (by omega) (by omega)
    simp [binopRI83Bytes, ZBinopName.code] at himm
    simp [decode, decodeNoRex, decodeRex, parseRM, binopRI83Bytes, binopOfExt,
      ZBinopName.code, byte_toNat]
    rw [himm]
    simp [ZRM.regOf]




/-! ## Byte layouts -/

abbrev binopRIC1Bytes (opc dst : Nat) (imm : BitVec 64) : List (BitVec 8) :=
  [byte (0x48 + (if 8 ≤ dst then 1 else 0)), byte 0xC1,
   byte (0xC0 + 8 * (opc % 8) + dst % 8), byte imm.toNat]

abbrev binopRID1Bytes (opc dst : Nat) : List (BitVec 8) :=
  [byte (0x48 + (if 8 ≤ dst then 1 else 0)), byte 0xD1,
   byte (0xC0 + 8 * (opc % 8) + dst % 8)]

abbrev binopRI81Bytes (opc dst : Nat) (imm : BitVec 64) : List (BitVec 8) :=
  [byte (0x48 + (if 8 ≤ dst then 1 else 0)), byte 0x81,
   byte (0xC0 + 8 * (opc % 8) + dst % 8),
   byte imm.toNat, byte (imm.toNat / 256), byte (imm.toNat / 65536),
   byte (imm.toNat / 16777216)]

abbrev binopRIRaxBytes (opc : Nat) (imm : BitVec 64) : List (BitVec 8) :=
  [byte 0x48, byte (opc * 8 + 5),
   byte imm.toNat, byte (imm.toNat / 256), byte (imm.toNat / 65536),
   byte (imm.toNat / 16777216)]

abbrev binopRITestRaxBytes (imm : BitVec 64) : List (BitVec 8) :=
  [byte 0x48, byte 0xA9,
   byte imm.toNat, byte (imm.toNat / 256), byte (imm.toNat / 65536),
   byte (imm.toNat / 16777216)]

abbrev binopRITestBytes (dst : Nat) (imm : BitVec 64) : List (BitVec 8) :=
  [byte (0x48 + (if 8 ≤ dst then 1 else 0)), byte 0xF7, byte (0xC0 + dst % 8),
   byte imm.toNat, byte (imm.toNat / 256), byte (imm.toNat / 65536),
   byte (imm.toNat / 16777216)]

theorem shiftOp (op : ZBinopName)
    (hop : op = .zror ∨ op = .zshl ∨ op = .zshr ∨ op = .zsar) :
    op.code / 8 = 1 ∧ op ≠ .ztest := by
  rcases hop with rfl|rfl|rfl|rfl <;> exact ⟨by decide, by decide⟩

theorem binopOp (op : ZBinopName)
    (hop : op = .zadd ∨ op = .zor ∨ op = .zadc ∨ op = .zsbb ∨ op = .zand ∨
      op = .zsub ∨ op = .zxor ∨ op = .zcmp) :
    op.code / 8 ≠ 1 ∧ op ≠ .ztest := by
  rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨by decide, by decide⟩

theorem shiftOfExt_code (op : ZBinopName)
    (hop : op = .zror ∨ op = .zshl ∨ op = .zshr ∨ op = .zsar) :
    shiftOfExt (op.code % 8) = some op := by
  rcases hop with rfl|rfl|rfl|rfl <;> rfl

/-! ## The shift `0xC1` form -/

theorem encodeInsn_binopRI_C1 (op : ZBinopName) (dst : Nat) (hd : dst < 16) (imm : BitVec 64)
    (hop : op = .zror ∨ op = .zshl ∨ op = .zshr ∨ op = .zsar) (hne : imm ≠ 1)
    (hs : -128 ≤ imm.toInt ∧ imm.toInt ≤ 127) :
    encodeInsn (.binopRI op .z64 dst imm) = binopRIC1Bytes op.code dst imm := by
  have h8 : eImm8 imm = some [byte imm.toNat] := by unfold eImm8; rw [ite_eq_left hs]
  rcases hop with rfl|rfl|rfl|rfl <;> interval_cases dst <;>
    simp only [encodeInsn, h8, ite_eq_right hne, ZBinopName.code, notByte,
      eRmImm8, eModRM, eOpsize, rexPrefix, mkRex, byte, binopRIC1Bytes] <;>
    rfl

theorem decode_binopRI_C1 (op : ZBinopName) (dst : Nat) (hd : dst < 16) (imm : BitVec 64)
    (hop : op = .zror ∨ op = .zshl ∨ op = .zshr ∨ op = .zsar) (hne : imm ≠ 1)
    (hs : -128 ≤ imm.toInt ∧ imm.toInt ≤ 127) :
    decode (byteListReader (encodeInsn (.binopRI op .z64 dst imm))) =
      some (.binopRI op .z64 dst imm, 4) := by
  rw [encodeInsn_binopRI_C1 op dst hd imm hop hne hs]
  have hb3 : byteListReader (binopRIC1Bytes op.code dst imm) 3 = byte imm.toNat := by
    simp [binopRIC1Bytes]
  rcases hop with rfl|rfl|rfl|rfl <;> interval_cases dst
  all_goals
    have himm := imm8_at imm 3 (byteListReader (binopRIC1Bytes _ _ imm)) hb3
      (by omega) (by omega)
    simp [binopRIC1Bytes, ZBinopName.code] at himm
    simp [decode, decodeNoRex, decodeRex, parseRM, binopRIC1Bytes, shiftOfExt,
      ZBinopName.code, byte_toNat]
    rw [himm]
    simp [ZRM.regOf]

/-! ## The shift-by-one `0xD1` form -/

theorem encodeInsn_binopRI_D1 (op : ZBinopName) (dst : Nat) (hd : dst < 16)
    (hop : op = .zror ∨ op = .zshl ∨ op = .zshr ∨ op = .zsar) :
    encodeInsn (.binopRI op .z64 dst 1) = binopRID1Bytes op.code dst := by
  rcases hop with rfl|rfl|rfl|rfl <;> interval_cases dst <;>
    simp only [encodeInsn, ZBinopName.code, eGenRmReg, eModRM, eOpsize, rexPrefix,
      mkRex, byte, binopRID1Bytes] <;>
    rfl

theorem decode_binopRI_D1 (op : ZBinopName) (dst : Nat) (hd : dst < 16)
    (hop : op = .zror ∨ op = .zshl ∨ op = .zshr ∨ op = .zsar) :
    decode (byteListReader (encodeInsn (.binopRI op .z64 dst 1))) =
      some (.binopRI op .z64 dst 1, 3) := by
  rw [encodeInsn_binopRI_D1 op dst hd hop]
  rcases hop with rfl|rfl|rfl|rfl <;> interval_cases dst <;>
    simp [decode, decodeNoRex, decodeRex, parseRM, binopRID1Bytes, shiftOfExt,
      ZBinopName.code, byte_toNat, ZRM.regOf]




theorem binopOp_ne_test (op : ZBinopName)
    (hop : op = .zadd ∨ op = .zor ∨ op = .zadc ∨ op = .zsbb ∨ op = .zand ∨
      op = .zsub ∨ op = .zxor ∨ op = .zcmp) : op ≠ .ztest := by
  rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem binopOp_ne_shift (op : ZBinopName)
    (hop : op = .zadd ∨ op = .zor ∨ op = .zadc ∨ op = .zsbb ∨ op = .zand ∨
      op = .zsub ∨ op = .zxor ∨ op = .zcmp) : op.code / 8 ≠ 1 := by
  rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem encodeInsn_binopRI_81 (op : ZBinopName) (dst : Nat) (hd : dst < 16) (imm : BitVec 64)
    (hop : op = .zadd ∨ op = .zor ∨ op = .zadc ∨ op = .zsbb ∨ op = .zand ∨
      op = .zsub ∨ op = .zxor ∨ op = .zcmp)
    (hns : ¬ (-128 ≤ imm.toInt ∧ imm.toInt ≤ 127)) (hne : dst ≠ 0)
    (hlo : -(2^31 : Int) ≤ imm.toInt) (hhi : imm.toInt < 2^31) :
    encodeInsn (.binopRI op .z64 dst imm) = binopRI81Bytes op.code dst imm := by
  have h8 : eImm8 imm = none := by unfold eImm8; rw [ite_eq_right hns]
  have h32 := eImm32_eq imm hlo hhi
  have his : (eImm8 imm).isSome = false := by rw [h8]; rfl
  have hnt := binopOp_ne_test op hop
  have hnsh := binopOp_ne_shift op hop
  simp only [encodeInsn]
  rw [ite_eq_right hnt, ite_eq_right hnsh]
  rw [his]
  simp only [Bool.and_false, Bool.false_eq_true, ite_false]
  rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> interval_cases dst
  all_goals
    first
    | exact absurd rfl hne
    | simp [h32, eRmImm, eModRM, eOpsizeImm, eOpsize, rexPrefix, mkRex, byte,
        binopRI81Bytes, isRax, ZBinopName.code]

theorem encodeInsn_binopRI_rax (op : ZBinopName) (imm : BitVec 64)
    (hop : op = .zadd ∨ op = .zor ∨ op = .zadc ∨ op = .zsbb ∨ op = .zand ∨
      op = .zsub ∨ op = .zxor ∨ op = .zcmp)
    (hns : ¬ (-128 ≤ imm.toInt ∧ imm.toInt ≤ 127))
    (hlo : -(2^31 : Int) ≤ imm.toInt) (hhi : imm.toInt < 2^31) :
    encodeInsn (.binopRI op .z64 0 imm) = binopRIRaxBytes op.code imm := by
  have h8 : eImm8 imm = none := by unfold eImm8; rw [ite_eq_right hns]
  have h32 := eImm32_eq imm hlo hhi
  have his : (eImm8 imm).isSome = false := by rw [h8]; rfl
  have hnt := binopOp_ne_test op hop
  have hnsh := binopOp_ne_shift op hop
  simp only [encodeInsn]
  rw [ite_eq_right hnt, ite_eq_right hnsh]
  rw [his]
  simp only [Bool.and_false, Bool.false_eq_true, ite_false]
  rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [h32, eRaxImm, eOpsizeImm, eOpsize, rexPrefix, byte,
      binopRIRaxBytes, isRax, ZBinopName.code]

theorem encodeInsn_binopRI_test_rax (imm : BitVec 64)
    (hlo : -(2^31 : Int) ≤ imm.toInt) (hhi : imm.toInt < 2^31) :
    encodeInsn (.binopRI .ztest .z64 0 imm) = binopRITestRaxBytes imm := by
  have h32 := eImm32_eq imm hlo hhi
  simp [encodeInsn, h32, eRaxImm, eOpsizeImm, eOpsize, rexPrefix, byte,
    binopRITestRaxBytes, isRax]

theorem encodeInsn_binopRI_test (dst : Nat) (hd : dst < 16) (hne : dst ≠ 0) (imm : BitVec 64)
    (hlo : -(2^31 : Int) ≤ imm.toInt) (hhi : imm.toInt < 2^31) :
    encodeInsn (.binopRI .ztest .z64 dst imm) = binopRITestBytes dst imm := by
  have h32 := eImm32_eq imm hlo hhi
  interval_cases dst
  all_goals
    first
    | exact absurd rfl hne
    | simp [encodeInsn, h32, eRmImm, eModRM, eOpsizeImm, eOpsize, rexPrefix, mkRex,
        byte, binopRITestBytes, isRax]




theorem decode_binopRI_81 (op : ZBinopName) (dst : Nat) (hd : dst < 16) (imm : BitVec 64)
    (hop : op = .zadd ∨ op = .zor ∨ op = .zadc ∨ op = .zsbb ∨ op = .zand ∨
      op = .zsub ∨ op = .zxor ∨ op = .zcmp)
    (hns : ¬ (-128 ≤ imm.toInt ∧ imm.toInt ≤ 127)) (hne : dst ≠ 0)
    (hlo : -(2^31 : Int) ≤ imm.toInt) (hhi : imm.toInt < 2^31) :
    decode (byteListReader (encodeInsn (.binopRI op .z64 dst imm))) =
      some (.binopRI op .z64 dst imm, 7) := by
  rw [encodeInsn_binopRI_81 op dst hd imm hop hns hne hlo hhi]
  have hbo := binopOfExt_code op hop
  have hr : ∀ j, j < 4 → byteListReader (binopRI81Bytes op.code dst imm) (3 + j) =
      byte (imm.toNat / 2^(8*j)) := by
    intro j hj
    interval_cases j <;> simp [binopRI81Bytes]
  have himm := imm32_eImm32_at imm 3 (byteListReader (binopRI81Bytes op.code dst imm)) hr hlo hhi
  rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> interval_cases dst
  all_goals
    first
    | exact absurd rfl hne
    | (simp [binopRI81Bytes, ZBinopName.code] at himm
       simp [decode, decodeNoRex, decodeRex, parseRM, binopRI81Bytes, binopOfExt,
         ZBinopName.code, byte_toNat]
       rw [himm]
       simp [ZRM.regOf])

theorem decode_binopRI_rax (op : ZBinopName) (imm : BitVec 64)
    (hop : op = .zadd ∨ op = .zor ∨ op = .zadc ∨ op = .zsbb ∨ op = .zand ∨
      op = .zsub ∨ op = .zxor ∨ op = .zcmp)
    (hns : ¬ (-128 ≤ imm.toInt ∧ imm.toInt ≤ 127))
    (hlo : -(2^31 : Int) ≤ imm.toInt) (hhi : imm.toInt < 2^31) :
    decode (byteListReader (encodeInsn (.binopRI op .z64 0 imm))) =
      some (.binopRI op .z64 0 imm, 6) := by
  rw [encodeInsn_binopRI_rax op imm hop hns hlo hhi]
  have hr : ∀ j, j < 4 → byteListReader (binopRIRaxBytes op.code imm) (2 + j) =
      byte (imm.toNat / 2^(8*j)) := by
    intro j hj
    interval_cases j <;> simp [binopRIRaxBytes]
  have himm := imm32_eImm32_at imm 2 (byteListReader (binopRIRaxBytes op.code imm)) hr hlo hhi
  rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    simp [binopRIRaxBytes, ZBinopName.code] at himm
    simp [decode, decodeNoRex, decodeRex, binopRIRaxBytes, ZBinopName.code,
      byte_toNat]
    rw [himm]

theorem decode_binopRI_test_rax (imm : BitVec 64)
    (hlo : -(2^31 : Int) ≤ imm.toInt) (hhi : imm.toInt < 2^31) :
    decode (byteListReader (encodeInsn (.binopRI .ztest .z64 0 imm))) =
      some (.binopRI .ztest .z64 0 imm, 6) := by
  rw [encodeInsn_binopRI_test_rax imm hlo hhi]
  have hr : ∀ j, j < 4 → byteListReader (binopRITestRaxBytes imm) (2 + j) =
      byte (imm.toNat / 2^(8*j)) := by
    intro j hj
    interval_cases j <;> simp [binopRITestRaxBytes]
  have himm := imm32_eImm32_at imm 2 (byteListReader (binopRITestRaxBytes imm)) hr hlo hhi
  simp [decode, decodeNoRex, decodeRex, binopRITestRaxBytes, byte_toNat]
  rw [himm]

theorem decode_binopRI_test (dst : Nat) (hd : dst < 16) (hne : dst ≠ 0) (imm : BitVec 64)
    (hlo : -(2^31 : Int) ≤ imm.toInt) (hhi : imm.toInt < 2^31) :
    decode (byteListReader (encodeInsn (.binopRI .ztest .z64 dst imm))) =
      some (.binopRI .ztest .z64 dst imm, 7) := by
  rw [encodeInsn_binopRI_test dst hd hne imm hlo hhi]
  have hr : ∀ j, j < 4 → byteListReader (binopRITestBytes dst imm) (3 + j) =
      byte (imm.toNat / 2^(8*j)) := by
    intro j hj
    interval_cases j <;> simp [binopRITestBytes]
  have himm := imm32_eImm32_at imm 3 (byteListReader (binopRITestBytes dst imm)) hr hlo hhi
  interval_cases dst
  all_goals
    first
    | exact absurd rfl hne
    | (simp [binopRITestBytes] at himm
       simp [decode, decodeNoRex, decodeRex, parseRM, binopRITestBytes, byte_toNat]
       rw [himm]
       simp [ZRM.regOf])



/-! ## SSE forms -/

/-- The encoded byte list of `comisd`. -/



theorem eGenRmReg_xmm (reg src : Nat) (hr : reg < 16) (hs : src < 16)
    (p : List (BitVec 8)) (opc : BitVec 8) (mo : Option (BitVec 8)) :
    eGenRmReg .z32 (.zr src) (BitVec.ofNat 4 reg) p opc mo =
      (if 8 ≤ reg ∨ 8 ≤ src then
        [byte (64 + (if 8 ≤ reg then 4 else 0) + (if 8 ≤ src then 1 else 0))] else []) ++
      p ++ [opc ||| mo.getD 1] ++ [byte (192 + 8 * (reg % 8) + src % 8)] := by
  interval_cases reg <;> interval_cases src <;> cases mo with
  | none => simp [eGenRmReg, eModRM, eOpsize, rexPrefix, mkRex, byte]
  | some m => simp [eGenRmReg, eModRM, eOpsize, rexPrefix, mkRex, byte]

abbrev sseRex (reg src : Nat) : List (BitVec 8) :=
  if 8 ≤ reg ∨ 8 ≤ src then
    [byte (64 + (if 8 ≤ reg then 4 else 0) + (if 8 ≤ src then 1 else 0))] else []

abbrev modrmB (reg src : Nat) : BitVec 8 := byte (192 + 8 * (reg % 8) + src % 8)

abbrev comisdBytes (dst src : Nat) : List (BitVec 8) :=
  [byte 0x66] ++ sseRex dst src ++ [byte 0x0F, byte 0x2F, modrmB dst src]

abbrev movsdBytes (dst src : Nat) : List (BitVec 8) :=
  [byte 0xF2] ++ sseRex dst src ++ [byte 0x0F, byte 0x10, modrmB dst src]

abbrev pcmpeqqBytes (dst src : Nat) : List (BitVec 8) :=
  [byte 0x66] ++ sseRex dst src ++ [byte 0x0F, byte 0x38, byte 0x29, modrmB dst src]

abbrev sqrtsdBytes (dst src : Nat) : List (BitVec 8) :=
  [byte 0xF2] ++ sseRex dst src ++ [byte 0x0F, byte 0x51, modrmB dst src]

abbrev cvtdq2pdBytes (dst src : Nat) : List (BitVec 8) :=
  [byte 0xF3] ++ sseRex dst src ++ [byte 0x0F, byte 0xE6, modrmB dst src]

abbrev cvtpd2dqBytes (dst src : Nat) : List (BitVec 8) :=
  [byte 0xF2] ++ sseRex dst src ++ [byte 0x0F, byte 0xE6, modrmB dst src]

abbrev logicPDBytes (code dst src : Nat) : List (BitVec 8) :=
  [byte 0x66] ++ sseRex dst src ++ [byte 0x0F, byte (0x54 + code), modrmB dst src]

abbrev binSDBytes (code dst src : Nat) : List (BitVec 8) :=
  [byte 0xF2] ++ sseRex dst src ++ [byte 0x0F, byte (0x58 + code), modrmB dst src]

abbrev psrlqBytes (dst : Nat) (imm : BitVec 8) : List (BitVec 8) :=
  [byte 0x66] ++ sseRex 2 dst ++ [byte 0x0F, byte 0x73, modrmB 2 dst] ++ [imm]

abbrev psllqBytes (dst : Nat) (imm : BitVec 8) : List (BitVec 8) :=
  [byte 0x66] ++ sseRex 6 dst ++ [byte 0x0F, byte 0x73, modrmB 6 dst] ++ [imm]

abbrev pslldqBytes (dst : Nat) (imm : BitVec 8) : List (BitVec 8) :=
  [byte 0x66] ++ sseRex 7 dst ++ [byte 0x0F, byte 0x73, modrmB 7 dst] ++ [imm]

abbrev psrldqBytes (dst : Nat) (imm : BitVec 8) : List (BitVec 8) :=
  [byte 0x66] ++ sseRex 3 dst ++ [byte 0x0F, byte 0x73, modrmB 3 dst] ++ [imm]

abbrev movDQBytes (toXmm quad : Bool) (xmm gpr : Nat) : List (BitVec 8) :=
  [byte 0x66] ++
    (if quad then [byte (72 + (if 8 ≤ xmm then 4 else 0) + (if 8 ≤ gpr then 1 else 0))]
     else sseRex xmm gpr) ++
    [byte 0x0F, byte (if toXmm then 0x6E else 0x7E), modrmB xmm gpr]

theorem encodeInsn_comisd (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    encodeInsn (.sse (.comisd dst src)) = comisdBytes dst src := by
  simp only [encodeInsn, encodeSSE, xmmToRM, comisdBytes, sseRex, modrmB]
  rw [eGenRmReg_xmm dst src hd hs [byte 0x0F] (byte 0x2F) none]
  simp [byte]

theorem decode_comisd (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    decode (byteListReader (encodeInsn (.sse (.comisd dst src)))) =
      some (.sse (.comisd dst src), 4 + (if 8 ≤ dst ∨ 8 ≤ src then 1 else 0)) := by
  rw [encodeInsn_comisd dst src hd hs]
  interval_cases dst <;> interval_cases src <;> decide

theorem encodeInsn_movsd (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    encodeInsn (.sse (.movsd dst src)) = movsdBytes dst src := by
  simp only [encodeInsn, encodeSSE, xmmToRM, movsdBytes, sseRex, modrmB]
  rw [eGenRmReg_xmm dst src hd hs [byte 0x0F] (byte 0x10) (some 0)]
  simp [byte]

theorem decode_movsd (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    decode (byteListReader (encodeInsn (.sse (.movsd dst src)))) =
      some (.sse (.movsd dst src), 4 + (if 8 ≤ dst ∨ 8 ≤ src then 1 else 0)) := by
  rw [encodeInsn_movsd dst src hd hs]
  interval_cases dst <;> interval_cases src <;> decide

theorem encodeInsn_pcmpeqq (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    encodeInsn (.sse (.pcmpeqq dst src)) = pcmpeqqBytes dst src := by
  simp only [encodeInsn, encodeSSE, xmmToRM, pcmpeqqBytes, sseRex, modrmB]
  rw [eGenRmReg_xmm dst src hd hs [byte 0x0F, byte 0x38] (byte 0x29) (some 0)]
  simp [byte]

theorem decode_pcmpeqq (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    decode (byteListReader (encodeInsn (.sse (.pcmpeqq dst src)))) =
      some (.sse (.pcmpeqq dst src), 5 + (if 8 ≤ dst ∨ 8 ≤ src then 1 else 0)) := by
  rw [encodeInsn_pcmpeqq dst src hd hs]
  interval_cases dst <;> interval_cases src <;> decide

theorem encodeInsn_sqrtsd (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    encodeInsn (.sse (.sqrtsd dst src)) = sqrtsdBytes dst src := by
  simp only [encodeInsn, encodeSSE, xmmToRM, sqrtsdBytes, sseRex, modrmB]
  rw [eGenRmReg_xmm dst src hd hs [byte 0x0F] (byte 0x51) (some 0)]
  simp [byte]

theorem decode_sqrtsd (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    decode (byteListReader (encodeInsn (.sse (.sqrtsd dst src)))) =
      some (.sse (.sqrtsd dst src), 4 + (if 8 ≤ dst ∨ 8 ≤ src then 1 else 0)) := by
  rw [encodeInsn_sqrtsd dst src hd hs]
  interval_cases dst <;> interval_cases src <;> decide

theorem encodeInsn_cvtdq2pd (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    encodeInsn (.sse (.cvtdq2pd dst src)) = cvtdq2pdBytes dst src := by
  simp only [encodeInsn, encodeSSE, xmmToRM, cvtdq2pdBytes, sseRex, modrmB]
  rw [eGenRmReg_xmm dst src hd hs [byte 0x0F] (byte 0xE6) (some 0)]
  simp [byte]

theorem decode_cvtdq2pd (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    decode (byteListReader (encodeInsn (.sse (.cvtdq2pd dst src)))) =
      some (.sse (.cvtdq2pd dst src), 4 + (if 8 ≤ dst ∨ 8 ≤ src then 1 else 0)) := by
  rw [encodeInsn_cvtdq2pd dst src hd hs]
  interval_cases dst <;> interval_cases src <;> decide

theorem encodeInsn_cvtpd2dq (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    encodeInsn (.sse (.cvtpd2dq false dst src)) = cvtpd2dqBytes dst src := by
  simp only [encodeInsn, encodeSSE, xmmToRM, cvtpd2dqBytes, sseRex, modrmB]
  rw [eGenRmReg_xmm dst src hd hs [byte 0x0F] (byte 0xE6) (some 0)]
  simp [byte]

theorem decode_cvtpd2dq (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    decode (byteListReader (encodeInsn (.sse (.cvtpd2dq false dst src)))) =
      some (.sse (.cvtpd2dq false dst src), 4 + (if 8 ≤ dst ∨ 8 ≤ src then 1 else 0)) := by
  rw [encodeInsn_cvtpd2dq dst src hd hs]
  interval_cases dst <;> interval_cases src <;> decide

theorem encodeInsn_logicPD (logic : SSELogic) (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    encodeInsn (.sse (.logicPD logic dst src)) =
      logicPDBytes (sseLogicCode logic).toNat dst src := by
  simp only [encodeInsn, encodeSSE, xmmToRM, logicPDBytes, sseRex, modrmB]
  rw [eGenRmReg_xmm dst src hd hs [byte 0x0F] (byte 0x54) (some (BitVec.ofNat 8 (sseLogicCode logic).toNat))]
  cases logic <;> interval_cases dst <;> interval_cases src <;> decide

theorem decode_logicPD (logic : SSELogic) (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    decode (byteListReader (encodeInsn (.sse (.logicPD logic dst src)))) =
      some (.sse (.logicPD logic dst src), 4 + (if 8 ≤ dst ∨ 8 ≤ src then 1 else 0)) := by
  rw [encodeInsn_logicPD logic dst src hd hs]
  cases logic <;> interval_cases dst <;> interval_cases src <;> decide

theorem encodeInsn_binSD (bop : SSEBinop) (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    encodeInsn (.sse (.binSD bop dst src)) =
      binSDBytes (sseBinopCode bop).toNat dst src := by
  simp only [encodeInsn, encodeSSE, xmmToRM, binSDBytes, sseRex, modrmB]
  rw [eGenRmReg_xmm dst src hd hs [byte 0x0F] (byte 0x58) (some (BitVec.ofNat 8 (sseBinopCode bop).toNat))]
  cases bop <;> interval_cases dst <;> interval_cases src <;> decide

theorem decode_binSD (bop : SSEBinop) (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    decode (byteListReader (encodeInsn (.sse (.binSD bop dst src)))) =
      some (.sse (.binSD bop dst src), 4 + (if 8 ≤ dst ∨ 8 ≤ src then 1 else 0)) := by
  rw [encodeInsn_binSD bop dst src hd hs]
  cases bop <;> interval_cases dst <;> interval_cases src <;> decide





theorem eGenRmReg_xmm64 (reg src : Nat) (hr : reg < 16) (hs : src < 16)
    (p : List (BitVec 8)) (opc : BitVec 8) (mo : Option (BitVec 8)) :
    eGenRmReg .z64 (.zr src) (BitVec.ofNat 4 reg) p opc mo =
      [byte (72 + (if 8 ≤ reg then 4 else 0) + (if 8 ≤ src then 1 else 0))] ++
      p ++ [opc ||| mo.getD 1] ++ [byte (192 + 8 * (reg % 8) + src % 8)] := by
  interval_cases reg <;> interval_cases src <;> cases mo with
  | none => simp [eGenRmReg, eModRM, eOpsize, rexPrefix, mkRex, byte]
  | some m => simp [eGenRmReg, eModRM, eOpsize, rexPrefix, mkRex, byte]

theorem encodeInsn_psrlqImm (dst : Nat) (hd : dst < 16) (imm : BitVec 8) :
    encodeInsn (.sse (.psrlqImm dst imm)) = psrlqBytes dst imm := by
  simp only [encodeInsn, encodeSSE, psrlqBytes, sseRex, modrmB]
  rw [eGenRmReg_xmm 2 dst (by decide) hd [byte 0x0F] (byte 0x73) (some 0)]
  interval_cases dst <;> rfl

theorem decode_psrlqImm (dst : Nat) (hd : dst < 16) (imm : BitVec 8) :
    decode (byteListReader (encodeInsn (.sse (.psrlqImm dst imm)))) =
      some (.sse (.psrlqImm dst imm), 5 + (if 8 ≤ dst then 1 else 0)) := by
  rw [encodeInsn_psrlqImm dst hd imm]
  interval_cases dst <;>
    simp [decode, decodeNoRex, decodeSSE, parseRM, psrlqBytes, sseRex, modrmB, ZRM.regOf]

theorem encodeInsn_psllqImm (dst : Nat) (hd : dst < 16) (imm : BitVec 8) :
    encodeInsn (.sse (.psllqImm dst imm)) = psllqBytes dst imm := by
  simp only [encodeInsn, encodeSSE, psllqBytes, sseRex, modrmB]
  rw [eGenRmReg_xmm 6 dst (by decide) hd [byte 0x0F] (byte 0x73) (some 0)]
  interval_cases dst <;> rfl

theorem decode_psllqImm (dst : Nat) (hd : dst < 16) (imm : BitVec 8) :
    decode (byteListReader (encodeInsn (.sse (.psllqImm dst imm)))) =
      some (.sse (.psllqImm dst imm), 5 + (if 8 ≤ dst then 1 else 0)) := by
  rw [encodeInsn_psllqImm dst hd imm]
  interval_cases dst <;>
    simp [decode, decodeNoRex, decodeSSE, parseRM, psllqBytes, sseRex, modrmB, ZRM.regOf]

theorem encodeInsn_pslldq (dst : Nat) (hd : dst < 16) (imm : BitVec 8) :
    encodeInsn (.sse (.pslldq dst imm)) = pslldqBytes dst imm := by
  simp only [encodeInsn, encodeSSE, pslldqBytes, sseRex, modrmB]
  rw [eGenRmReg_xmm 7 dst (by decide) hd [byte 0x0F] (byte 0x73) (some 0)]
  interval_cases dst <;> rfl

theorem decode_pslldq (dst : Nat) (hd : dst < 16) (imm : BitVec 8) :
    decode (byteListReader (encodeInsn (.sse (.pslldq dst imm)))) =
      some (.sse (.pslldq dst imm), 5 + (if 8 ≤ dst then 1 else 0)) := by
  rw [encodeInsn_pslldq dst hd imm]
  interval_cases dst <;>
    simp [decode, decodeNoRex, decodeSSE, parseRM, pslldqBytes, sseRex, modrmB, ZRM.regOf]

theorem encodeInsn_psrldq (dst : Nat) (hd : dst < 16) (imm : BitVec 8) :
    encodeInsn (.sse (.psrldq dst imm)) = psrldqBytes dst imm := by
  simp only [encodeInsn, encodeSSE, psrldqBytes, sseRex, modrmB]
  rw [eGenRmReg_xmm 3 dst (by decide) hd [byte 0x0F] (byte 0x73) (some 0)]
  interval_cases dst <;> rfl

theorem decode_psrldq (dst : Nat) (hd : dst < 16) (imm : BitVec 8) :
    decode (byteListReader (encodeInsn (.sse (.psrldq dst imm)))) =
      some (.sse (.psrldq dst imm), 5 + (if 8 ≤ dst then 1 else 0)) := by
  rw [encodeInsn_psrldq dst hd imm]
  interval_cases dst <;>
    simp [decode, decodeNoRex, decodeSSE, parseRM, psrldqBytes, sseRex, modrmB, ZRM.regOf]

theorem encodeInsn_movDQ (toXmm quad : Bool) (xmm gpr : Nat) (hx : xmm < 16) (hg : gpr < 16) :
    encodeInsn (.sse (.movDQ toXmm quad xmm (.zr gpr))) = movDQBytes toXmm quad xmm gpr := by
  cases quad
  case false =>
    cases toXmm
    case false =>
      simp only [encodeInsn, encodeSSE, movDQBytes, sseRex, modrmB,
        Bool.false_eq_true, ite_false]
      rw [eGenRmReg_xmm xmm gpr hx hg [byte 0x0F] (byte 0x7E) (some 0)]
      interval_cases xmm <;> interval_cases gpr <;> rfl
    case true =>
      simp only [encodeInsn, encodeSSE, movDQBytes, sseRex, modrmB, reduceIte,
        Bool.false_eq_true, ite_false]
      rw [eGenRmReg_xmm xmm gpr hx hg [byte 0x0F] (byte 0x6E) (some 0)]
      interval_cases xmm <;> interval_cases gpr <;> rfl
  case true =>
    cases toXmm
    case false =>
      simp only [encodeInsn, encodeSSE, movDQBytes, sseRex, modrmB, reduceIte,
        Bool.false_eq_true, ite_false]
      rw [eGenRmReg_xmm64 xmm gpr hx hg [byte 0x0F] (byte 0x7E) (some 0)]
      interval_cases xmm <;> interval_cases gpr <;> rfl
    case true =>
      simp only [encodeInsn, encodeSSE, movDQBytes, sseRex, modrmB, reduceIte]
      rw [eGenRmReg_xmm64 xmm gpr hx hg [byte 0x0F] (byte 0x6E) (some 0)]
      interval_cases xmm <;> interval_cases gpr <;> rfl

theorem decode_movDQ (toXmm quad : Bool) (xmm gpr : Nat) (hx : xmm < 16) (hg : gpr < 16) :
    decode (byteListReader (encodeInsn (.sse (.movDQ toXmm quad xmm (.zr gpr))))) =
      some (.sse (.movDQ toXmm quad xmm (.zr gpr)),
        (encodeInsn (.sse (.movDQ toXmm quad xmm (.zr gpr)))).length) := by
  rw [encodeInsn_movDQ toXmm quad xmm gpr hx hg]
  cases quad <;> cases toXmm <;> interval_cases xmm <;> interval_cases gpr <;> decide


end Flapjack.Compiler.Encoders.X64

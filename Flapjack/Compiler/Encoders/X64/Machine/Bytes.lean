module

public import Mathlib.Tactic
public import Flapjack.Compiler.Encoders.X64.Machine.Decode

@[expose] public section

/-!
# Byte-level facts for the x86-64 decoder

This module collects the reusable facts behind the decoder inverse proofs: how
`byteListReader` reads a concrete byte list, how `parseRM` recovers the fields
of the `ModRM`/SIB/displacement layouts that `e_ModRM` writes, and how the
little-endian immediate readers recover `e_imm8`/`e_imm16`/`e_imm32`/`e_imm64`
outputs.  None of these declarations is a HOL port; they are Flapjack
infrastructure for the closed machine model.
-/

namespace Flapjack.Compiler.Encoders.X64

/-! ## Reading a byte list -/

@[simp] theorem byteListReader_cons_zero (a : BitVec 8) (as : List (BitVec 8)) :
    byteListReader (a :: as) 0 = a := rfl

@[simp] theorem byteListReader_cons_succ (a : BitVec 8) (as : List (BitVec 8)) (n : Nat) :
    byteListReader (a :: as) (n + 1) = byteListReader as n := rfl

@[simp] theorem byteListReader_nil (n : Nat) : byteListReader [] n = 0 := rfl

@[simp] theorem byte_toNat (n : Nat) : (byte n).toNat = n % 256 := by
  simp [byte]

/-! ## Byte bounds -/

theorem byte_toNat_of_lt {n : Nat} (h : n < 256) : (byte n).toNat = n := by
  rw [byte_toNat, Nat.mod_eq_of_lt h]

/-! ## `ModRM` arithmetic -/

/-- The register-form `ModRM` byte is the arithmetic sum of its fields. -/
theorem modRM_reg_byte (r20 rmBits : Nat) (h1 : r20 < 8) (h2 : rmBits < 8) :
    192 ||| (r20 <<< 3) ||| rmBits = 192 + 8 * r20 + rmBits := by
  interval_cases r20 <;> interval_cases rmBits <;> decide

/-- The base-register `ModRM` byte is the arithmetic sum of its fields. -/
theorem modRM_mem_byte (modBits r20 rmBits : Nat)
    (h1 : modBits < 4) (h2 : r20 < 8) (h3 : rmBits < 8) :
    (if modBits = 1 then 1 else if modBits = 4 then 2 else 0) * 64 |||
        (r20 <<< 3 ||| rmBits) =
      (if modBits = 1 then 1 else if modBits = 4 then 2 else 0) * 64 + 8 * r20 + rmBits := by
  interval_cases modBits <;> interval_cases r20 <;> interval_cases rmBits <;> decide

/-- The `SIB` byte written by `e_ModRM` for the base-register forms
(`index = 4`, no index, base `b20`) is `0x24` when `b20 = 4`. -/
theorem sibByte_fields : (0x24 : Nat) / 8 % 8 = 4 ∧ (0x24 : Nat) % 8 = 4 := by decide

/-! ## `parseRM` on register operands -/

/-- `parseRM` recovers a register operand from the `ModRM` byte `192 + 8a + b`. -/
theorem parseRM_reg (r : Nat → BitVec 8) (off a b : Nat) (rexB : Bool)
    (hm : (r off).toNat = 192 + 8 * a + b) (ha : a < 8) (hb : b < 8) :
    parseRM r off rexB =
      some { modBits := 3, regBits := a, rm := .zr ((if rexB then 8 else 0) + b), len := 1 } := by
  simp only [parseRM]
  have h1 : (192 + 8 * a + b) / 64 = 3 := by omega
  have h2 : ((192 + 8 * a + b) / 8) % 8 = a := by omega
  have h3 : (192 + 8 * a + b) % 8 = b := by omega
  simp only [hm, h1, h2, h3, if_true]

/-! ## `parseRM` on base-register memory operands -/

/-- `parseRM` recovers a `[base + disp]` memory operand when `mod = 0` and the
`rm` field is neither `4` (a SIB byte follows) nor `5` (RIP-relative). -/
theorem parseRM_base0 (r : Nat → BitVec 8) (off a b hi : Nat) (rexB : Bool)
    (hm : (r off).toNat = 8 * a + b) (ha : a < 8) (hb : b < 8) (hb4 : b ≠ 4)
    (hb5 : b ≠ 5) (hhi : hi = if rexB then 8 else 0) :
    parseRM r off rexB =
      some { modBits := 0, regBits := a, rm := .zm none (.regBase (hi + b)) 0, len := 1 } := by
  simp only [parseRM]
  have h1 : (8 * a + b) / 64 = 0 := by omega
  have h2 : ((8 * a + b) / 8) % 8 = a := by omega
  have h3 : (8 * a + b) % 8 = b := by omega
  simp [hm, h1, h2, h3, hb4, hb5, hhi]

/-- `parseRM` recovers a `[base + disp8]` memory operand when `mod = 1`. -/
theorem parseRM_base1 (r : Nat → BitVec 8) (off a b hi : Nat) (rexB : Bool)
    (hm : (r off).toNat = 64 + 8 * a + b) (ha : a < 8) (hb : b < 8) (hb4 : b ≠ 4)
    (hhi : hi = if rexB then 8 else 0) :
    parseRM r off rexB =
      some ({ modBits := 1, regBits := a, rm := .zm none (.regBase (hi + b)) (imm8 r (off + 1)), len := 2 } : ParsedRM) := by
  simp only [parseRM]
  have h1 : (64 + 8 * a + b) / 64 = 1 := by omega
  have h2 : ((64 + 8 * a + b) / 8) % 8 = a := by omega
  have h3 : (64 + 8 * a + b) % 8 = b := by omega
  simp [hm, h1, h2, h3, hb4, hhi]

/-- `parseRM` recovers a `[base + disp32]` memory operand when `mod = 2`. -/
theorem parseRM_base2 (r : Nat → BitVec 8) (off a b hi : Nat) (rexB : Bool)
    (hm : (r off).toNat = 128 + 8 * a + b) (ha : a < 8) (hb : b < 8) (hb4 : b ≠ 4)
    (hhi : hi = if rexB then 8 else 0) :
    parseRM r off rexB =
      some ({ modBits := 2, regBits := a, rm := .zm none (.regBase (hi + b)) (imm32 r (off + 1)), len := 5 } : ParsedRM) := by
  simp only [parseRM]
  have h1 : (128 + 8 * a + b) / 64 = 2 := by omega
  have h2 : ((128 + 8 * a + b) / 8) % 8 = a := by omega
  have h3 : (128 + 8 * a + b) % 8 = b := by omega
  simp [hm, h1, h2, h3, hb4, hhi]

/-- `parseRM` recovers a `[base + disp8]` memory operand with a SIB byte when
`mod = 1` and `rm = 4`. -/
theorem parseRM_sib1 (r : Nat → BitVec 8) (off a hi : Nat) (rexB : Bool)
    (hm : (r off).toNat = 64 + 8 * a + 4) (ha : a < 8)
    (hsib : (r (off + 1)).toNat = 36) (hhi : hi = if rexB then 8 else 0) :
    parseRM r off rexB =
      some ({ modBits := 1, regBits := a, rm := .zm none (.regBase (hi + 4)) (imm8 r (off + 2)), len := 3 } : ParsedRM) := by
  simp only [parseRM]
  have h1 : (64 + 8 * a + 4) / 64 = 1 := by omega
  have h2 : ((64 + 8 * a + 4) / 8) % 8 = a := by omega
  have h3 : (64 + 8 * a + 4) % 8 = 4 := by omega
  have hsib' : (36 : Nat) / 8 % 8 = 4 ∧ (36 : Nat) % 8 = 4 := by decide
  simp [hm, h1, h2, h3, hsib, hsib', hhi]

/-- `parseRM` recovers a `[base + disp32]` memory operand with a SIB byte when
`mod = 2` and `rm = 4`. -/
theorem parseRM_sib2 (r : Nat → BitVec 8) (off a hi : Nat) (rexB : Bool)
    (hm : (r off).toNat = 128 + 8 * a + 4) (ha : a < 8)
    (hsib : (r (off + 1)).toNat = 36) (hhi : hi = if rexB then 8 else 0) :
    parseRM r off rexB =
      some ({ modBits := 2, regBits := a, rm := .zm none (.regBase (hi + 4)) (imm32 r (off + 2)), len := 6 } : ParsedRM) := by
  simp only [parseRM]
  have h1 : (128 + 8 * a + 4) / 64 = 2 := by omega
  have h2 : ((128 + 8 * a + 4) / 8) % 8 = a := by omega
  have h3 : (128 + 8 * a + 4) % 8 = 4 := by omega
  have hsib' : (36 : Nat) / 8 % 8 = 4 ∧ (36 : Nat) % 8 = 4 := by decide
  simp [hm, h1, h2, h3, hsib, hsib', hhi]

/-- `parseRM` recovers a `[base]` memory operand with a SIB byte when `mod = 0`,
`rm = 4` and the base field is not `5`. -/
theorem parseRM_sib0 (r : Nat → BitVec 8) (off a hi : Nat) (rexB : Bool)
    (hm : (r off).toNat = 8 * a + 4) (ha : a < 8)
    (hsib : (r (off + 1)).toNat = 36) (hhi : hi = if rexB then 8 else 0) :
    parseRM r off rexB =
      some ({ modBits := 0, regBits := a, rm := .zm none (.regBase (hi + 4)) 0, len := 2 } : ParsedRM) := by
  simp only [parseRM]
  have h1 : (8 * a + 4) / 64 = 0 := by omega
  have h2 : ((8 * a + 4) / 8) % 8 = a := by omega
  have h3 : (8 * a + 4) % 8 = 4 := by omega
  have hsib' : (36 : Nat) / 8 % 8 = 4 ∧ (36 : Nat) % 8 = 4 := by decide
  simp [hm, h1, h2, h3, hsib, hsib', hhi]

/-- `parseRM` recovers a RIP-relative memory operand when `mod = 0` and `rm = 5`. -/
theorem parseRM_rip (r : Nat → BitVec 8) (off a : Nat)
    (hm : (r off).toNat = 8 * a + 5) (ha : a < 8) :
    parseRM r off false =
      some { modBits := 0, regBits := a, rm := .zm none .ripBase (imm32 r (off + 1)), len := 5 } := by
  simp only [parseRM]
  have h1 : (8 * a + 5) / 64 = 0 := by omega
  have h2 : ((8 * a + 5) / 8) % 8 = a := by omega
  have h3 : (8 * a + 5) % 8 = 5 := by omega
  simp [hm, h1, h2, h3]

/-! ## Immediate read-back -/

/-- A 64-bit word whose `toInt` lies in the signed 32-bit range has its low 32
bits sign-extend back to itself. -/
theorem setWidth32_toInt (imm : BitVec 64)
    (h1 : -(2^31 : Int) ≤ imm.toInt) (h2 : imm.toInt < 2^31) :
    (BitVec.setWidth 32 imm).toInt = imm.toInt := by
  rw [BitVec.toInt_setWidth, BitVec.toInt_eq_toNat_bmod]
  by_cases hpos : 0 ≤ imm.toInt
  · have hlt : 2 * imm.toNat < 2 ^ 64 := (BitVec.toInt_pos_iff).1 hpos
    have heq : (imm.toNat : Int) = imm.toInt := (BitVec.toInt_eq_toNat_of_lt hlt).symm
    rw [heq, Int.bmod_def, Int.bmod_def]
    norm_num
    omega
  · have hge : ¬ (2 * imm.toNat < 2^64) := by
      intro hc
      have h : (0:Int) ≤ imm.toInt := by
        rw [BitVec.toInt_eq_toNat_of_lt hc]; exact Int.natCast_nonneg _
      omega
    have hcond := BitVec.toInt_eq_toNat_cond imm
    simp only [hge, if_false] at hcond
    have heq : (imm.toNat : Int) = imm.toInt + 2^64 := by
      have h : (↑(2^64) : Int) = 18446744073709551616 := by norm_num
      omega
    rw [heq, Int.bmod_def, Int.bmod_def]
    norm_num
    omega

/-- A 64-bit word whose `toInt` lies in the signed 16-bit range has its low 16
bits sign-extend back to itself. -/
theorem setWidth16_toInt (imm : BitVec 64)
    (h1 : -(2^15 : Int) ≤ imm.toInt) (h2 : imm.toInt < 2^15) :
    (BitVec.setWidth 16 imm).toInt = imm.toInt := by
  rw [BitVec.toInt_setWidth, BitVec.toInt_eq_toNat_bmod]
  by_cases hpos : 0 ≤ imm.toInt
  · have hlt : 2 * imm.toNat < 2 ^ 64 := (BitVec.toInt_pos_iff).1 hpos
    have heq : (imm.toNat : Int) = imm.toInt := (BitVec.toInt_eq_toNat_of_lt hlt).symm
    rw [heq, Int.bmod_def, Int.bmod_def]
    norm_num
    omega
  · have hge : ¬ (2 * imm.toNat < 2^64) := by
      intro hc
      have h : (0:Int) ≤ imm.toInt := by
        rw [BitVec.toInt_eq_toNat_of_lt hc]; exact Int.natCast_nonneg _
      omega
    have hcond := BitVec.toInt_eq_toNat_cond imm
    simp only [hge, if_false] at hcond
    have heq : (imm.toNat : Int) = imm.toInt + 2^64 := by
      have h : (↑(2^64) : Int) = 18446744073709551616 := by norm_num
      omega
    rw [heq, Int.bmod_def, Int.bmod_def]
    norm_num
    omega

/-- A 64-bit word whose `toInt` lies in the signed 8-bit range has its low 8
bits sign-extend back to itself. -/
theorem setWidth8_toInt (imm : BitVec 64)
    (h1 : -(2^7 : Int) ≤ imm.toInt) (h2 : imm.toInt < 2^7) :
    (BitVec.setWidth 8 imm).toInt = imm.toInt := by
  rw [BitVec.toInt_setWidth, BitVec.toInt_eq_toNat_bmod]
  by_cases hpos : 0 ≤ imm.toInt
  · have hlt : 2 * imm.toNat < 2 ^ 64 := (BitVec.toInt_pos_iff).1 hpos
    have heq : (imm.toNat : Int) = imm.toInt := (BitVec.toInt_eq_toNat_of_lt hlt).symm
    rw [heq, Int.bmod_def, Int.bmod_def]
    norm_num
    omega
  · have hge : ¬ (2 * imm.toNat < 2^64) := by
      intro hc
      have h : (0:Int) ≤ imm.toInt := by
        rw [BitVec.toInt_eq_toNat_of_lt hc]; exact Int.natCast_nonneg _
      omega
    have hcond := BitVec.toInt_eq_toNat_cond imm
    simp only [hge, if_false] at hcond
    have heq : (imm.toNat : Int) = imm.toInt + 2^64 := by
      have h : (↑(2^64) : Int) = 18446744073709551616 := by norm_num
      omega
    rw [heq, Int.bmod_def, Int.bmod_def]
    norm_num
    omega

/-- A byte literal of a word's low eight bits is the word truncated to eight bits. -/
theorem byte_eq_setWidth8 (disp : BitVec 64) :
    byte disp.toNat = BitVec.setWidth 8 disp := by
  apply BitVec.toNat_eq.mpr
  simp [byte, BitVec.toNat_setWidth]

/-- The `k`-th little-endian byte of a 64-bit word. -/
theorem byte_extract (imm : BitVec 64) (k : Nat) :
    byte (imm.toNat / 2^(8*k)) = (imm >>> (8*k)).setWidth 8 := by
  apply BitVec.toNat_eq.mpr
  simp [byte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- `le32` of the four little-endian bytes of `imm` is `imm` truncated to 32 bits.
Proved bit by bit: each bit index lies in exactly one of the four bytes. -/
theorem le32_bytes (imm : BitVec 64) :
    le32 (fun k => byte (imm.toNat / 2^(8*k))) 0 = BitVec.setWidth 32 imm := by
  have hb : ∀ k, byte (imm.toNat / 2^(8*k)) = (imm >>> (8*k)).setWidth 8 := byte_extract imm
  simp only [hb, le32]
  ext i
  simp
  by_cases h8 : i < 8
  · have h16 : i < 16 := by omega
    have h24 : i < 24 := by omega
    simp [h8, h16, h24]
  · by_cases h16 : i < 16
    · have h24 : i < 24 := by omega
      have e8 : i - 8 < 8 := by omega
      have e : 8 + (i - 8) = i := by omega
      simp [h8, h16, h24, e8, e]
    · by_cases h24 : i < 24
      · have e16 : i - 16 < 8 := by omega
        have ne8 : ¬ (i - 8 < 8) := by omega
        have e : 16 + (i - 16) = i := by omega
        simp [h8, h16, h24, e16, ne8, e]
      · have e24 : i - 24 < 8 := by omega
        have ne8 : ¬ (i - 8 < 8) := by omega
        have ne16 : ¬ (i - 16 < 8) := by omega
        have e : 24 + (i - 24) = i := by omega
        simp [h8, h16, h24, e24, ne8, ne16, e]

/-- `le64` of the eight little-endian bytes of `imm` is `imm`.  Proved bit by
bit: each bit index lies in exactly one of the eight bytes. -/
theorem le64_bytes (imm : BitVec 64) :
    le64 (fun k => byte (imm.toNat / 2^(8*k))) 0 = imm := by
  have hb : ∀ k, byte (imm.toNat / 2^(8*k)) = (imm >>> (8*k)).setWidth 8 := byte_extract imm
  simp only [hb, le64]
  ext i
  simp
  by_cases h8 : i < 8
  · have h16 : i < 16 := by omega
    have h24 : i < 24 := by omega
    have h32 : i < 32 := by omega
    have h40 : i < 40 := by omega
    have h48 : i < 48 := by omega
    have h56 : i < 56 := by omega
    simp [h8, h16, h24, h32, h40, h48, h56]; rfl
  · by_cases h16 : i < 16
    · have h24 : i < 24 := by omega
      have h32 : i < 32 := by omega
      have h40 : i < 40 := by omega
      have h48 : i < 48 := by omega
      have h56 : i < 56 := by omega
      have e1 : i - 8 < 8 := by omega
      have a1 : 8 + (i - 8) = i := by omega
      simp [h8, h16, h24, h32, h40, h48, h56, e1, a1]; rfl
    · by_cases h24 : i < 24
      · have h32 : i < 32 := by omega
        have h40 : i < 40 := by omega
        have h48 : i < 48 := by omega
        have h56 : i < 56 := by omega
        have e2 : i - 16 < 8 := by omega
        have a2 : 16 + (i - 16) = i := by omega
        have d8 : ¬ (i - 8 < 8) := by omega
        simp [h8, h16, h24, h32, h40, h48, h56, e2, a2, d8]; rfl
      · by_cases h32 : i < 32
        · have h40 : i < 40 := by omega
          have h48 : i < 48 := by omega
          have h56 : i < 56 := by omega
          have e3 : i - 24 < 8 := by omega
          have a3 : 24 + (i - 24) = i := by omega
          have d8 : ¬ (i - 8 < 8) := by omega
          have d16 : ¬ (i - 16 < 8) := by omega
          simp [h8, h16, h24, h32, h40, h48, h56, e3, a3, d8, d16]; rfl
        · by_cases h40 : i < 40
          · have h48 : i < 48 := by omega
            have h56 : i < 56 := by omega
            have e4 : i - 32 < 8 := by omega
            have a4 : 32 + (i - 32) = i := by omega
            have d8 : ¬ (i - 8 < 8) := by omega
            have d16 : ¬ (i - 16 < 8) := by omega
            have d24 : ¬ (i - 24 < 8) := by omega
            simp [h8, h16, h24, h32, h40, h48, h56, e4, a4, d8, d16, d24]; rfl
          · by_cases h48 : i < 48
            · have h56 : i < 56 := by omega
              have e5 : i - 40 < 8 := by omega
              have a5 : 40 + (i - 40) = i := by omega
              have d8 : ¬ (i - 8 < 8) := by omega
              have d16 : ¬ (i - 16 < 8) := by omega
              have d24 : ¬ (i - 24 < 8) := by omega
              have d32 : ¬ (i - 32 < 8) := by omega
              simp [h8, h16, h24, h32, h40, h48, h56, e5, a5, d8, d16, d24, d32]; rfl
            · by_cases h56 : i < 56
              · have e6 : i - 48 < 8 := by omega
                have a6 : 48 + (i - 48) = i := by omega
                have d8 : ¬ (i - 8 < 8) := by omega
                have d16 : ¬ (i - 16 < 8) := by omega
                have d24 : ¬ (i - 24 < 8) := by omega
                have d32 : ¬ (i - 32 < 8) := by omega
                have d40 : ¬ (i - 40 < 8) := by omega
                simp [h8, h16, h24, h32, h40, h48, h56, e6, a6, d8, d16, d24, d32, d40]; rfl
              · have e7 : i - 56 < 8 := by omega
                have a7 : 56 + (i - 56) = i := by omega
                have d8 : ¬ (i - 8 < 8) := by omega
                have d16 : ¬ (i - 16 < 8) := by omega
                have d24 : ¬ (i - 24 < 8) := by omega
                have d32 : ¬ (i - 32 < 8) := by omega
                have d40 : ¬ (i - 40 < 8) := by omega
                have d48 : ¬ (i - 48 < 8) := by omega
                simp [h8, h16, h24, h32, h40, h48, h56, e7, a7, d8, d16, d24, d32, d40, d48]; rfl

/-- `le64` reads back eight `e_imm64` bytes at any offset. -/
theorem le64_at (imm : BitVec 64) (off : Nat) (r : Nat → BitVec 8)
    (hr : ∀ j, j < 8 → r (off + j) = byte (imm.toNat / 2^(8*j))) :
    le64 r off = imm := by
  have e0 : r off = byte (imm.toNat / 2^(8*0)) := by simpa using hr 0 (by omega)
  have e1 := hr 1 (by omega)
  have e2 := hr 2 (by omega)
  have e3 := hr 3 (by omega)
  have e4 := hr 4 (by omega)
  have e5 := hr 5 (by omega)
  have e6 := hr 6 (by omega)
  have e7 := hr 7 (by omega)
  simp only [le64, e0, e1, e2, e3, e4, e5, e6, e7]
  exact le64_bytes imm

/-- `imm32` reads back an `e_imm32` immediate in the signed 32-bit range. -/
theorem imm32_eImm32 (imm : BitVec 64)
    (h1 : -(2^31 : Int) ≤ imm.toInt) (h2 : imm.toInt < 2^31) :
    imm32 (fun k => byte (imm.toNat / 2^(8*k))) 0 = imm := by
  rw [imm32, le32_bytes]
  have := setWidth32_toInt imm h1 h2
  rw [this, BitVec.ofInt_toInt]

/-- `imm32` reads back an `e_imm32` immediate from any offset. -/
theorem imm32_eImm32_at (imm : BitVec 64) (off : Nat) (r : Nat → BitVec 8)
    (hr : ∀ j, j < 4 → r (off + j) = byte (imm.toNat / 2^(8*j)))
    (h1 : -(2^31 : Int) ≤ imm.toInt) (h2 : imm.toInt < 2^31) :
    imm32 r off = imm := by
  rw [imm32]
  have e0 : r off = byte (imm.toNat / 2^(8*0)) := by simpa using hr 0 (by omega)
  have e1 := hr 1 (by omega)
  have e2 := hr 2 (by omega)
  have e3 := hr 3 (by omega)
  simp only [le32, e0, e1, e2, e3]
  exact imm32_eImm32 imm h1 h2

/-- `imm8` reads back an `e_imm8` byte at any offset. -/
theorem imm8_at (imm : BitVec 64) (off : Nat) (r : Nat → BitVec 8)
    (hr : r off = byte imm.toNat)
    (h1 : -(2^7 : Int) ≤ imm.toInt) (h2 : imm.toInt < 2^7) :
    imm8 r off = imm := by
  rw [imm8, hr]
  have hb : byte imm.toNat = BitVec.setWidth 8 imm := by
    simpa using byte_extract imm 0
  rw [hb]
  have := setWidth8_toInt imm h1 h2
  rw [this, BitVec.ofInt_toInt]

/-- `imm8` reads back an `e_imm8` immediate in the signed 8-bit range. -/
theorem imm8_eImm8 (imm : BitVec 64)
    (h1 : -(2^7 : Int) ≤ imm.toInt) (h2 : imm.toInt < 2^7) :
    imm8 (fun k => byte (imm.toNat / 2^(8*k))) 0 = imm := by
  rw [imm8]
  have hb : byte (imm.toNat / 2^(8*0)) = BitVec.setWidth 8 imm := by
    rw [byte_extract]; simp
  rw [hb]
  have := setWidth8_toInt imm h1 h2
  rw [this, BitVec.ofInt_toInt]

end Flapjack.Compiler.Encoders.X64

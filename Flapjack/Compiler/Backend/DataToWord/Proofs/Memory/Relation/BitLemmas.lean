module

public import Flapjack.HolRef

@[expose] public section

/-! Kernel-checked bit-vector facts used by the data-to-word memory proofs. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Clearing bit zero is a no-op when that bit is already clear. -/
theorem bitAndNotOneEq {w : Nat} (x : BitVec w) (h : x.getLsbD 0 = false) :
    x &&& ~~~(1 : BitVec w) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (1 : BitVec w) = BitVec.ofNat w 1 from rfl]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
  match i with
  | 0 => simp [h]
  | j + 1 => simp [hi, Nat.testBit_succ]

/-- The low bit is the remainder modulo two. -/
theorem bitLowToNat {w : Nat} (x : BitVec w) : x.getLsbD 0 = decide (x.toNat % 2 = 1) := by
  rw [← BitVec.testBit_toNat, Nat.testBit_zero]

/-- A bit-4 mask is zero precisely when bit 4 is clear. -/
theorem bitAnd16EqZero {w : Nat} (hw : 4 < w) (x : BitVec w) :
    (x &&& 16 = 0) ↔ x.getLsbD 4 = false := by
  have lt : (16 : Nat) < 2 ^ w := by
    have : (2 : Nat)^4 < 2^w := Nat.pow_lt_pow_right (by decide) hw
    simpa using this
  have h16 : (16 : BitVec w) = BitVec.twoPow w 4 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_twoPow, Nat.mod_eq_of_lt lt]
  rw [h16, BitVec.and_twoPow]
  by_cases hb : x.getLsbD 4 <;> simp [hb]
  intro hz
  have := congrArg BitVec.toNat hz
  simp [BitVec.toNat_twoPow, Nat.mod_eq_of_lt lt] at this

/-- Bits 2 and 3 both clear imply that the corresponding mask is zero. -/
theorem bitAnd12EqZero {w : Nat} (x : BitVec w)
    (h2 : x.getLsbD 2 = false) (h3 : x.getLsbD 3 = false) : x &&& 12 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (12 : BitVec w) = BitVec.ofNat w 12 from rfl]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat]
  match i with
  | 0 | 1 => simp [show Nat.testBit 12 1 = false by decide, show Nat.testBit 12 0 = false by decide]
  | 2 => simp [h2]
  | 3 => simp [h3]
  | j + 4 =>
    have : Nat.testBit 12 (j + 4) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : (12 : Nat) < 2^4)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [this]

/-- Bit 3 set implies that the corresponding mask is nonzero. -/
theorem bitAnd12NeZero {w : Nat} (hw : 3 < w) (x : BitVec w)
    (h3 : x.getLsbD 3 = true) : x &&& 12 ≠ 0 := by
  intro hz
  have bit := congrArg (fun y => y.getLsbD 3) hz
  have hb : (12 : BitVec w).getLsbD 3 = true := by
    rw [show (12 : BitVec w) = BitVec.ofNat w 12 from rfl, BitVec.getLsbD_ofNat]
    simp [hw, show Nat.testBit 12 3 = true by decide]
  simp only [BitVec.getLsbD_and, h3, hb, Bool.true_and] at bit
  simp [BitVec.getLsbD] at bit

/-- Multiplication by four is a two-bit shift. -/
theorem bitFourMulEqShift {w : Nat} (x : BitVec w) : (4 : BitVec w) * x = x <<< 2 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.shiftLeft_eq, Nat.mul_comm]

/-- A 64-bit word is determined by its upper and lower 32-bit halves. -/
theorem bitWord64Split (v1 v2 : BitVec 64) :
    ((v1 >>> 32).setWidth 32 = (v2 >>> 32).setWidth 32 ∧
      v1.setWidth 32 = v2.setWidth 32) ↔ v1 = v2 := by
  constructor
  · rintro ⟨hi, lo⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i indexBound
    by_cases h : i < 32
    · have := congrArg (fun y => y.getLsbD i) lo
      simpa [BitVec.getLsbD_setWidth, h] using this
    · have := congrArg (fun y => y.getLsbD (i - 32)) hi
      have e : 32 + (i - 32) = i := by omega
      simp [BitVec.getLsbD_ushiftRight, e, show i - 32 < 32 by omega] at this
      exact this
  · rintro rfl
    simp

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

import Flapjack.Compiler.Backend.StackRemove.Proofs.StackPointer
namespace Flapjack.Compiler.Backend.StackRemove.AllocationArithmetic
open Flapjack.Compiler.Backend.StackRemove
open Flapjack
/-- Flapjack proof factoring of the local unsigned comparison argument in
stack_removeProofScript.sml:440-506. There is no separately named HOL theorem,
so this declaration deliberately has no HOL tag. Every premise comes from the
original full state relation or the original single-chunk count bound; the
allocation simulation must discharge them before using this result. The reserve
prevents subtraction underflow and the stack bound prevents addition overflow,
so the complete native comparison is derived without a guard-result premise. -/
theorem allocationGuard {width : Nat} [NeZero width]
    (base : BitVec width) (space length count : Nat)
    (good : goodDimindex width)
    (reserve : width / 8 * maxStackAlloc ≤ base.toNat)
    (upper : base.toNat + (bytesInWord width).toNat * length < 2 ^ width)
    (spaceBound : space ≤ length) (countBound : count ≤ maxStackAlloc) :
    (base + bytesInWord width * BitVec.ofNat width space - wordOffset count) < base ↔ space < count := by
  have bytesNat : (bytesInWord width).toNat = width / 8 := by
    rcases good with rfl | rfl <;> decide
  have positive : 0 < width / 8 := by
    rcases good with rfl | rfl <;> decide
  rw [bytesNat] at upper
  have countReserve : width / 8 * count ≤ base.toNat :=
    Nat.le_trans (Nat.mul_le_mul_left (width / 8) countBound) reserve
  have spaceProduct : width / 8 * space ≤ width / 8 * length :=
    Nat.mul_le_mul_left (width / 8) spaceBound
  have totalBound : base.toNat + width / 8 * space < 2 ^ width := by omega
  have productBound : width / 8 * space < 2 ^ width := by omega
  have countProductBound : width / 8 * count < 2 ^ width := by
    exact Nat.lt_of_le_of_lt countReserve base.isLt
  have pointerNat : (base + bytesInWord width * BitVec.ofNat width space).toNat =
      base.toNat + width / 8 * space := by
    rw [bytesInWord, ← BitVec.ofNat_mul, BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt productBound, Nat.mod_eq_of_lt totalBound]
  have offsetNat : (wordOffset (width := width) count).toNat = width / 8 * count := by
    simp only [wordOffset, BitVec.toNat_ofNat, Nat.mod_eq_of_lt countProductBound]
  rw [BitVec.lt_def, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, offsetNat, pointerNat]; omega), pointerNat, offsetNat]
  have productLt : width / 8 * space < width / 8 * count ↔ space < count := Nat.mul_lt_mul_left positive
  omega
end Flapjack.Compiler.Backend.StackRemove.AllocationArithmetic

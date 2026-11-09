module

public import Flapjack.Compiler.Backend.DataToWord.Header

@[expose] public section

/-! Agreement between pointer-tag extraction and the executable mask. -/
namespace Flapjack.Compiler.Backend.DataToWord
open Flapjack

/-- The inlined word mask used by the production compiler implements the
source-shaped low-bit extraction at every positive word width. -/
theorem getLowerBits_word_eq_mask {width : Nat} [NeZero width] (conf : Config) (value : BitVec width) :
    getLowerBits conf (.word value) =
      (value &&& BitVec.ofNat width (2 ^ smallShiftLength conf - 1)) ||| 1 := by
  unfold getLowerBits
  apply congrArg (fun x : BitVec width => x ||| 1)
  calc
    (value.extractLsb' 0 (smallShiftLength conf)).setWidth width =
        BitVec.ofNat width (value.toNat % 2 ^ smallShiftLength conf) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat]
    _ = BitVec.ofNat width (value.toNat &&& (2 ^ smallShiftLength conf - 1)) := by
      rw [Nat.and_two_pow_sub_one_eq_mod]
    _ = value &&& BitVec.ofNat width (2 ^ smallShiftLength conf - 1) := by
      rw [BitVec.ofNat_and]
      simp

end Flapjack.Compiler.Backend.DataToWord

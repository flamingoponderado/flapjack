module

public import Flapjack.Misc.MachineIeee

@[expose] public section

/-!
# Sign-bit computation lemmas for the `fp64` encoding

`fp64_abs` and `fp64_negate` are the codecs composed with `float_abs` and
`float_negate`; those touch only the one-bit sign, so on the 64-bit encoding
they are the masks `2^63 - 1` and `2^63`.  These are Flapjack-specific
computation lemmas: HOL states the operations compositionally
(`machine_ieeeScript.sml:431-432` with `binary_ieeeScript.sml:153-159`) rather
than as bit masks, so there is no HOL declaration to port.  They live beside
the definitions in a submodule so that the reviewed real-free source forms of
`Flapjack.Misc.MachineIeee` stay byte-for-byte recognizable to
`scripts/check-hol-refs.py`.

Both proofs read the two sides bit by bit: the codec is a concatenation, so
each bit index falls either in the significand, the exponent, or the sign.
-/

namespace Flapjack

/-- `fp64_abs` clears the sign bit: the codecs round-trip the payload and
`float_abs` only zeroes the sign, so the result is `a` masked to 63 bits. -/
theorem holFp64Abs_eq_and (a : BitVec 64) :
    holFp64Abs a = a &&& BitVec.ofNat 64 (2 ^ 63 - 1) := by
  simp only [holFp64Abs, holFloatAbs, holFp64ToFloat, holFloatToFp64]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_cast]
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  have hmask : (BitVec.ofNat 64 (2 ^ 63 - 1)).getLsbD i = decide (i < 63) := by
    rw [BitVec.getLsbD_ofNat]
    simp only [Nat.testBit_two_pow_sub_one]
    simp [hi]
  simp only [BitVec.getLsbD_and, hmask, BitVec.getLsbD_extractLsb']
  by_cases h52 : i < 52
  · have h63 : i < 63 := by omega
    simp [h52, h63]
  · by_cases h63 : i < 63
    · have e : 52 + (i - 52) = i := by omega
      have e2 : i - 52 < 11 := by omega
      simp [h52, h63, e, e2]
    · have e3 : ¬ (i - 52 < 11) := by omega
      simp [h52, h63, e3]

/-- `fp64_negate` complements the sign bit: the codecs round-trip the payload
and `float_negate` only flips the sign, so the result is `a` with bit 63
toggled. -/
theorem holFp64Negate_eq_xor (a : BitVec 64) :
    holFp64Negate a = a ^^^ BitVec.ofNat 64 (2 ^ 63) := by
  simp only [holFp64Negate, holFloatNegate, holFp64ToFloat, holFloatToFp64]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_cast]
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  have hmask : (BitVec.ofNat 64 (2 ^ 63)).getLsbD i = decide (i = 63) := by
    rw [BitVec.getLsbD_ofNat]
    simp only [Nat.testBit_two_pow, eq_comm]
    simp [hi]
  simp only [BitVec.getLsbD_xor, hmask, BitVec.getLsbD_extractLsb', BitVec.getLsbD_not]
  by_cases h52 : i < 52
  · have h63 : i ≠ 63 := by omega
    simp [h52, h63]
  · by_cases h63 : i < 63
    · have e : 52 + (i - 52) = i := by omega
      have e2 : i - 52 < 11 := by omega
      have hne : i ≠ 63 := by omega
      simp [h52, e, e2, hne]
    · have h63' : i = 63 := by omega
      subst h63'
      simp [h52]

end Flapjack

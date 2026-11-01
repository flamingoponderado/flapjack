import Flapjack.Misc.MachineIeee

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
-/

namespace Flapjack

/-- `fp64_abs` clears the sign bit: the codecs round-trip the payload and
`float_abs` only zeroes the sign, so the result is `a` masked to 63 bits. -/
theorem holFp64Abs_eq_and (a : BitVec 64) :
    holFp64Abs a = a &&& BitVec.ofNat 64 (2 ^ 63 - 1) := by
  simp only [holFp64Abs, holFloatAbs, holFp64ToFloat, holFloatToFp64]
  bv_decide

/-- `fp64_negate` complements the sign bit: the codecs round-trip the payload
and `float_negate` only flips the sign, so the result is `a` with bit 63
toggled. -/
theorem holFp64Negate_eq_xor (a : BitVec 64) :
    holFp64Negate a = a ^^^ BitVec.ofNat 64 (2 ^ 63) := by
  simp only [holFp64Negate, holFloatNegate, holFp64ToFloat, holFloatToFp64]
  bv_decide

end Flapjack

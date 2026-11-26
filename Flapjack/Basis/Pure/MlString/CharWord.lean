module

public import Flapjack.Basis.Pure.MlString

@[expose] public section

/-! Conversions between HOL byte characters and words. -/
namespace Flapjack.Basis.Pure.MlString

/-- Convert a HOL byte character to its word representation. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "char_to_word8_def"]
def charToWord8 (c : HolChar) : BitVec 8 := BitVec.ofNat 8 c.toNat

/-- Convert a byte word to its HOL character representation. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "word8_to_char_def"]
def word8ToChar (w : BitVec 8) : HolChar := BitVec.ofNat 8 w.toNat

/-- Original `char_lt_total`: the byte order on characters is total. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "char_lt_total"]
theorem charLt_total (c1 c2 : HolChar) (h : ¬(c1 < c2) ∧ ¬(c2 < c1)) : c1 = c2 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.lt_def] at h
  omega

end Flapjack.Basis.Pure.MlString

module

public import Flapjack.HolRef
public import Mathlib.Data.BitVec

@[expose] public section

namespace Flapjack

/-- Original `n2w_lt`: unsigned `<` on `n2w`-embedded naturals agrees with `<`
on the naturals, given both embedded values are nonzero and fit the word.
HOL's `dimword (:'a)` is `2 ^ width` and `n2w` is `BitVec.ofNat`. -/
@[hol "cakeml/misc/miscScript.sml" "n2w_lt" (words_as_type_indexed_bitvec)]
theorem n2w_lt {width : Nat} [NeZero width] (a b : Nat)
    (h : (0 : BitVec width) < BitVec.ofNat width a ∧
      (0 : BitVec width) < BitVec.ofNat width b ∧
      a < 2 ^ width ∧ b < 2 ^ width) :
    BitVec.ofNat width a < BitVec.ofNat width b ↔ a < b := by
  obtain ⟨_, _, ha, hb⟩ := h
  simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- Original `n2w_le`: unsigned `≤` on `n2w`-embedded naturals agrees with `≤`
on the naturals, under the same fitting hypotheses as `n2w_lt`. -/
@[hol "cakeml/misc/miscScript.sml" "n2w_le" (words_as_type_indexed_bitvec)]
theorem n2w_le {width : Nat} [NeZero width] (a b : Nat)
    (h : (0 : BitVec width) < BitVec.ofNat width a ∧
      (0 : BitVec width) < BitVec.ofNat width b ∧
      a < 2 ^ width ∧ b < 2 ^ width) :
    BitVec.ofNat width a ≤ BitVec.ofNat width b ↔ a ≤ b := by
  obtain ⟨_, _, ha, hb⟩ := h
  simp only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

end Flapjack

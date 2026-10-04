import Flapjack.HolRef

/-!
# HOL machine-code `address` lemmas

Counterpart of the pinned `HOL/examples/machine-code/hoare-triple/addressScript.sml`
declarations used by the Pancake top-level proof. HOL `'a word` is
`BitVec width` (`words_as_type_indexed_bitvec`) and `n2w` is `BitVec.ofNat`.
-/

namespace Flapjack.Misc.Address

/-- Full original `word_arith_lemma2` (`addressScript.sml:413-422`):
`n2w n - n2w m = if n < m then -(n2w (m - n)) else n2w (n - m)`. -/
@[hol "HOL/examples/machine-code/hoare-triple/addressScript.sml" "word_arith_lemma2"
  (words_as_type_indexed_bitvec)]
theorem wordArithLemma2 {width : Nat} [NeZero width] :
    ∀ n m : Nat, (BitVec.ofNat width n : BitVec width) - BitVec.ofNat width m =
      if n < m then -BitVec.ofNat width (m - n) else BitVec.ofNat width (n - m) := by
  intro n m
  split
  · rename_i h
    have e : BitVec.ofNat width m = BitVec.ofNat width n + BitVec.ofNat width (m - n) := by
      rw [BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' (Nat.le_of_lt h)]
    simp only [e, BitVec.sub_eq_add_neg, BitVec.neg_add, ← BitVec.add_assoc, BitVec.add_right_neg,
      BitVec.zero_add]
  · rename_i h
    have e : BitVec.ofNat width n = BitVec.ofNat width (n - m) + BitVec.ofNat width m := by
      rw [BitVec.ofNat_add_ofNat, Nat.sub_add_cancel (Nat.le_of_not_lt h)]
    rw [e, BitVec.add_sub_cancel]

end Flapjack.Misc.Address

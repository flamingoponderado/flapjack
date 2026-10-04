import Flapjack.HolRef

/-! `miscScript.sml` `WORD_LS_IMP`. HOL's unsigned word orders `<=+`/`<+` are
Lean's `BitVec` `≤`/`<` (comparison of `toNat`), `n2w` is `BitVec.ofNat`, and
`w2n` is `toNat`. The `Abbrev` marker around the first conjunct is HOL's
logical identity `Abbrev x = x` and is rendered as the bare equation. -/
namespace Flapjack.Misc.WordLsImp

/-- Full original `WORD_LS_IMP`:
`a <=+ b ==> ?k. Abbrev (b = a + n2w k) /\ w2n (b - a) = k /\
(!w. a <=+ w /\ w <+ b <=> ?i. w = a + n2w i /\ i < k)`. -/
@[hol "cakeml/misc/miscScript.sml" "WORD_LS_IMP" (words_as_type_indexed_bitvec)]
theorem wordLsImp {width : Nat} [NeZero width] {a b : BitVec width} (h : a ≤ b) :
    ∃ k : Nat, b = a + BitVec.ofNat width k ∧ (b - a).toNat = k ∧
      ∀ w : BitVec width, (a ≤ w ∧ w < b ↔ ∃ i, w = a + BitVec.ofNat width i ∧ i < k) := by
  have hab : a.toNat ≤ b.toNat := h
  have ha := a.isLt
  have hb := b.isLt
  refine ⟨b.toNat - a.toNat, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : b.toNat - a.toNat < 2 ^ width),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [BitVec.toNat_sub_of_le h]
  · intro w
    have hw := w.isLt
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : a.toNat ≤ w.toNat := h1
      have h2' : w.toNat < b.toNat := h2
      refine ⟨w.toNat - a.toNat, ?_, by omega⟩
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : w.toNat - a.toNat < 2 ^ width), Nat.mod_eq_of_lt (by omega)]
      omega
    · rintro ⟨i, rfl, hi⟩
      have e : (a + BitVec.ofNat width i).toNat = a.toNat + i := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ width),
          Nat.mod_eq_of_lt (by omega)]
      constructor
      · show a.toNat ≤ (a + BitVec.ofNat width i).toNat
        omega
      · show (a + BitVec.ofNat width i).toNat < b.toNat
        omega

end Flapjack.Misc.WordLsImp

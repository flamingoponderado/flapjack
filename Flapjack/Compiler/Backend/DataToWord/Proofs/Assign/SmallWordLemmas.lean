module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Address
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.PointerBits
public import Flapjack.Compiler.Backend.BackendCommon.UpperW2w
public import Flapjack.Misc.GoodDimindex
public import Flapjack.Misc.Multiword

@[expose] public section

/-!
# Small word lemmas of `data_to_word_assignProofScript.sml`

HOL `w2w` is `BitVec.setWidth`, `n2w` is `BitVec.ofNat`, `dimword (:'a)` is
`2 ^ width`, `≪`/`⋙` are `<<<`/`>>>`, `&&`/`‖` are `&&&`/`|||`,
`integer$Num` is `Int.natAbs` (HOL specifies `Num (-a) = Num a`), and HOL
`BIT i n` is `Nat.testBit n i`. The word extraction `(63 >< 32) w` of a
64-bit word is `(w >>> 32).setWidth width`, as in the reviewed `word64Rep`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Misc.Multiword

/-- The 64-bit word representation is injective on a good word size. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "Word64Rep_inj"
  (words_as_type_indexed_bitvec)]
theorem word64Rep_inj {width : Nat} [NeZero width] {β : Type} (w1 w2 : BitVec 64)
    (good : goodDimindex width) :
    ((word64Rep w1 : HeapElement β (HeapTag × List (WordLocW width))) = word64Rep w2 ↔ w1 = w2) := by
  constructor
  · intro h
    rcases good with rfl | rfl
    · simp only [word64Rep, show (32 : Nat) < 64 by decide, if_true,
        HeapElement.dataElement.injEq, true_and, Prod.mk.injEq, List.cons.injEq,
        WordLocW.word.injEq, and_true] at h
      obtain ⟨hhi, hlo⟩ := h
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      by_cases hs : i < 32
      · have := congrArg (·.getLsbD i) hlo
        simpa [BitVec.getLsbD_setWidth, hs] using this
      · have := congrArg (·.getLsbD (i - 32)) hhi
        have e : 32 + (i - 32) = i := by omega
        have h2 : i - 32 < 32 := by omega
        simpa [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, e, h2] using this
    · simpa [word64Rep] using h
  · rintro rfl; rfl

/-- Pointer encodings of zero-annotated words are injective in bounded
heap indices. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "get_addr_inj"
  (words_as_type_indexed_bitvec)]
theorem getAddr_inj {width : Nat} [NeZero width] (p1 p2 : Nat) (c : Config)
    (h : p1 * 2 ^ shiftLength c < 2 ^ width ∧ p2 * 2 ^ shiftLength c < 2 ^ width ∧
      getAddr c p1 (.word (0 : BitVec width)) = getAddr c p2 (.word 0)) : p1 = p2 := by
  obtain ⟨boundI, boundJ, same⟩ := h
  have shifted := congrArg (fun w : BitVec width => w >>> shiftLength c) same
  simp only [getAddr, BitVec.ushiftRight_or_distrib, getLowerBits_shiftLength,
    bounded_shift_roundtrip p1 (shiftLength c) boundI,
    bounded_shift_roundtrip p2 (shiftLength c) boundJ] at shifted
  have factor : 0 < 2 ^ shiftLength c := Nat.two_pow_pos _
  have iSmall : p1 < 2 ^ width := by
    have h := Nat.le_mul_of_pos_right p1 factor
    omega
  have jSmall : p2 < 2 ^ width := by
    have h := Nat.le_mul_of_pos_right p2 factor
    omega
  have values := congrArg BitVec.toNat shifted
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt iSmall, Nat.mod_eq_of_lt jSmall] using values

/-- Shifting a widened byte left and back by two is the identity. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "w2w_shift_shift"
  (words_as_type_indexed_bitvec)]
theorem w2w_shift_shift {width : Nat} [NeZero width] (w : BitVec 8) (good : goodDimindex width) :
    ((w.setWidth width : BitVec width) <<< (2 : Nat)) >>> (2 : Nat) = w.setWidth width := by
  rcases good with rfl | rfl <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    intro _ hb; have := BitVec.lt_of_getLsbD hb; omega

/-- Narrowing a widened byte gives the byte back. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "good_dimindex_w2w_byte"
  (words_as_type_indexed_bitvec)]
theorem goodDimindex_w2w_byte {width : Nat} [NeZero width] (w : BitVec 8)
    (good : goodDimindex width) : (w.setWidth width : BitVec width).setWidth 8 = w := by
  rcases good with rfl | rfl <;> simp

/-- The upper half of a 64-bit word on a 32-bit target, otherwise the word. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "w2w_upper_def"
  (words_as_type_indexed_bitvec)]
def w2wUpper {width : Nat} [NeZero width] (w : BitVec 64) : BitVec width :=
  if width = 32 then (w >>> (32 : Nat)).setWidth width else w.setWidth width

/-- `w2w_upper` inverts `upper_w2w` on a good word size. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "w2w_upper_upper_w2w"
  (words_as_type_indexed_bitvec)]
theorem w2wUpper_upperW2w {width : Nat} [NeZero width] (z1 : List (BitVec width))
    (good : goodDimindex width) : (z1.map upperW2w).map w2wUpper = z1 := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id z1]
  apply List.map_congr_left
  intro w _
  rcases good with rfl | rfl
  · simp only [Function.comp_apply, w2wUpper, upperW2w, if_true, id]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    have : 32 + i < 64 := by omega
    have : i < 64 := by omega
    simp [*]
  · simp [w2wUpper, upperW2w]

/-- The small-number encoding as a shifted signed magnitude. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "Smallnum_alt"
  (words_as_type_indexed_bitvec)]
theorem smallnum_alt {width : Nat} [NeZero width] (i : Int) :
    (smallnum i : BitVec width) =
      if i < 0 then (0 - BitVec.ofNat width (-i).natAbs) <<< (2 : Nat)
      else BitVec.ofNat width i.natAbs <<< (2 : Nat) := by
  have shl2 : ∀ x : BitVec width, x <<< (2 : Nat) = x * BitVec.ofNat width 4 := by
    intro x
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, BitVec.toNat_mul, Nat.shiftLeft_eq, Nat.mul_mod]
  have of4 : ∀ a : Nat, BitVec.ofNat width (4 * a) = BitVec.ofNat width a <<< (2 : Nat) := by
    intro a
    rw [shl2]; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, Nat.mul_mod, Nat.mul_comm]
  unfold smallnum
  split
  · have e : (4 * (0 - i)).toNat = 4 * (-i).natAbs := by omega
    rw [e, of4, shl2, shl2]; simp [BitVec.neg_mul]
  · have e : (4 * i).toNat = 4 * i.natAbs := by omega
    rw [e, of4]

/-- A bounded field shifted into a large enough word fits. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "MULT_TWO_EXP_LESS_dimword"
  (word_dimension_as_width := width)]
theorem mult_two_exp_less_dimword (width : Nat) [NeZero width] (b l n : Nat)
    (h : b + l ≤ width ∧ n < 2 ^ b) : n * 2 ^ l < 2 ^ width := by
  obtain ⟨hbl, hn⟩ := h
  calc n * 2 ^ l < 2 ^ b * 2 ^ l := Nat.mul_lt_mul_of_pos_right hn (Nat.two_pow_pos l)
    _ = 2 ^ (b + l) := (Nat.pow_add 2 b l).symm
    _ ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) hbl

/-- A number below `2 ^ k` has bit `k` clear. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "LESS_IMP_NOT_BIT"]
theorem less_imp_not_bit (k n : Nat) (h : n < 2 ^ k) : ¬ Nat.testBit n k = true := by
  simp [Nat.testBit_lt_two_pow h]

/-- A one-word multiword encoding is exactly a nonzero number below the word
size. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "LENGTH_n2mw_1"
  (words_as_type_indexed_bitvec)]
theorem length_n2mw_1 {width : Nat} [NeZero width] (n : Nat) :
    (n2mw n : List (BitVec width)).length = 1 ↔ n ≠ 0 ∧ n < 2 ^ width := by
  have pos : 0 < 2 ^ width := Nat.two_pow_pos width
  rw [n2mw]
  by_cases h0 : n = 0
  · simp [h0]
  · simp only [h0, if_false, List.length_cons, Nat.add_eq_right, ne_eq, not_false_eq_true,
      true_and]
    rw [n2mw]
    by_cases hq : n / 2 ^ width = 0
    · simp [hq]
      exact (Nat.div_eq_zero_iff_lt pos).mp hq
    · simp [hq]
      by_contra hlt
      exact hq ((Nat.div_eq_zero_iff_lt pos).mpr (by omega))

/-- The zero field is zero. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "maxout_bits_0"
  (words_as_type_indexed_bitvec)]
theorem maxoutBits_0 {width : Nat} [NeZero width] (b e : Nat) :
    (maxoutBits 0 b e : BitVec width) = 0 := by
  unfold maxoutBits
  split
  · simp
  · rename_i h
    have : b = 0 := by
      by_contra hb
      have : 2 ≤ 2 ^ b := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    subst this
    simp [allOnes]

/-- A nonempty low mask keeps the least significant bit. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "all_ones_and_1"
  (words_as_type_indexed_bitvec)]
theorem allOnes_and_1 {width : Nat} [NeZero width] (k : Nat) (h : k ≠ 0) :
    (allOnes k 0 : BitVec width) &&& 1 = 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have bit := allOnes_bit (width := width) k 0 i hi
  by_cases i0 : i = 0
  · subst i0
    have : (allOnes k 0 : BitVec width).getLsbD 0 = true := bit.mpr ⟨le_rfl, by omega⟩
    simp [this]
  · simp [i0]

/-- Splitting an equation of disjoint disjunctions. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "word_or_eq_word_or_split"
  (words_as_type_indexed_bitvec)]
theorem word_or_eq_word_or_split {width : Nat} [NeZero width] (w1 w2 v1 v2 : BitVec width)
    (h : w1 &&& w2 = 0 ∧ v1 &&& v2 = 0 ∧ w1 &&& v2 = 0 ∧ v1 &&& w2 = 0) :
    (w1 ||| w2 = v1 ||| v2 ↔ w1 = v1 ∧ w2 = v2) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  constructor
  · intro e
    have bits : ∀ i, w1.getLsbD i = v1.getLsbD i ∧ w2.getLsbD i = v2.getLsbD i := by
      intro i
      have b1 := congrArg (fun x => x.getLsbD i) h1
      have b2 := congrArg (fun x => x.getLsbD i) h2
      have b3 := congrArg (fun x => x.getLsbD i) h3
      have b4 := congrArg (fun x => x.getLsbD i) h4
      have be := congrArg (fun x => x.getLsbD i) e
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] at b1 b2 b3 b4 be
      generalize w1.getLsbD i = a1 at *
      generalize w2.getLsbD i = a2 at *
      generalize v1.getLsbD i = c1 at *
      generalize v2.getLsbD i = c2 at *
      cases a1 <;> cases a2 <;> cases c1 <;> cases c2 <;> simp_all
    exact ⟨BitVec.eq_of_getLsbD_eq fun i _ => (bits i).1,
      BitVec.eq_of_getLsbD_eq fun i _ => (bits i).2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- Bits `l ..< l + b` of an in-range field hold the encoded number.
Flapjack bit-vector infrastructure for the pointer-bit lemmas. -/
theorem maxoutBits_getLsbD_small {width : Nat} [NeZero width] (n b l i : Nat)
    (hn : n < 2 ^ b - 1) (hi : i < width) :
    (maxoutBits n b l : BitVec width).getLsbD i = (decide (l ≤ i) && n.testBit (i - l)) := by
  simp only [maxoutBits, hn, if_true, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, hi,
    decide_true, Bool.true_and]
  by_cases hl : l ≤ i
  · have : i - l < width := by omega
    simp [hl, this, show ¬ i < l by omega]
  · simp [hl, show i < l by omega]

/-- Disjoint set bits give a zero conjunction. Flapjack infrastructure. -/
theorem and_eq_zero_of_disjoint {width : Nat} (x y : BitVec width)
    (h : ∀ i, i < width → x.getLsbD i = true → y.getLsbD i = true → False) : x &&& y = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp
  exact h i hi hx hy

/-- Two saturating fields agree exactly when their numbers do, provided one
is in range. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "maxout_bits_eq"
  (words_as_type_indexed_bitvec)]
theorem maxoutBits_eq {width : Nat} [NeZero width] (n n' b l : Nat)
    (h : b + l ≤ width ∧ n' < 2 ^ b - 1) :
    ((maxoutBits n b l : BitVec width) = maxoutBits n' b l ↔ n = n') := by
  obtain ⟨hbl, hn'⟩ := h
  constructor
  · intro e
    have bitAt : ∀ j, j < b →
        (maxoutBits n b l : BitVec width).getLsbD (l + j) = n'.testBit j := by
      intro j hj
      rw [e, maxoutBits_getLsbD_small n' b l (l + j) hn' (by omega)]
      simp
    by_cases hn : n < 2 ^ b - 1
    · apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < b
      · have := bitAt j hj
        rw [maxoutBits_getLsbD_small n b l (l + j) hn (by omega)] at this
        simpa using this
      · have p : 2 ^ b ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
        rw [Nat.testBit_lt_two_pow (show n < 2 ^ j by omega),
          Nat.testBit_lt_two_pow (show n' < 2 ^ j by omega)]
    · exfalso
      have ones : ∀ j, j < b → n'.testBit j = true := by
        intro j hj
        rw [← bitAt j hj]
        simp only [maxoutBits, hn, if_false]
        exact (allOnes_bit (l + b) l (l + j) (by omega)).mpr ⟨by omega, by omega⟩
      have : n' = 2 ^ b - 1 := by
        apply Nat.eq_of_testBit_eq
        intro j
        rw [Nat.testBit_two_pow_sub_one]
        by_cases hj : j < b
        · simp [ones j hj, hj]
        · have p : 2 ^ b ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
          rw [Nat.testBit_lt_two_pow (show n' < 2 ^ j by omega)]
          simp [hj]
      omega
  · rintro rfl; rfl

/-- The low mask of the annotation keeps the pointer bits and marker of a
pointer encoding. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "all_ones_get_addr"
  (words_as_type_indexed_bitvec)]
theorem allOnes_getAddr {width : Nat} [NeZero width] (c : Config) (ptr tag2 len2 : Nat) :
    (allOnes (c.lenBits + (c.tagBits + 1)) 0 : BitVec width) &&&
        getAddr c ptr (.word (ptrBits c tag2 len2 : BitVec width)) =
      ptrBits c tag2 len2 ||| 1 := by
  rw [getAddr, getLowerBits_ptrBits]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have ones := allOnes_bit (width := width) (c.lenBits + (c.tagBits + 1)) 0 i hi
  have tagRange := fun hb => maxoutBits_bit (width := width) tag2 c.tagBits (1 + c.lenBits) i hb hi
  have lenRange := fun hb => maxoutBits_bit (width := width) len2 c.lenBits 1 i hb hi
  by_cases low : i < c.lenBits + (c.tagBits + 1)
  · have hshift : shiftLength c > i := by simp only [shiftLength]; omega
    simp [BitVec.getLsbD_and, BitVec.getLsbD_or, ones.mpr ⟨Nat.zero_le _, low⟩,
      BitVec.getLsbD_shiftLeft, hshift]
  · have hoff : (allOnes (c.lenBits + (c.tagBits + 1)) 0 : BitVec width).getLsbD i = false := by
      cases h : (allOnes (c.lenBits + (c.tagBits + 1)) 0 : BitVec width).getLsbD i
      · rfl
      · exact absurd (ones.mp h).2 low
    have ht : (maxoutBits tag2 c.tagBits (1 + c.lenBits) : BitVec width).getLsbD i = false := by
      cases h : (maxoutBits tag2 c.tagBits (1 + c.lenBits) : BitVec width).getLsbD i
      · rfl
      · have := tagRange h; omega
    have hl : (maxoutBits len2 c.lenBits 1 : BitVec width).getLsbD i = false := by
      cases h : (maxoutBits len2 c.lenBits 1 : BitVec width).getLsbD i
      · rfl
      · have := lenRange h; omega
    have h0 : i ≠ 0 := by omega
    simp [BitVec.getLsbD_and, BitVec.getLsbD_or, hoff, ptrBits, ht, hl, h0]

/-- The low mask of the length field and marker clears the tag field. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "all_ones_and_ptr_bits_tag_0"
  (words_as_type_indexed_bitvec)]
theorem allOnes_and_ptrBits_tag_0 {width : Nat} [NeZero width] (c : Config) (tag len : Nat) :
    (allOnes (c.lenBits + 1) 0 : BitVec width) &&& ptrBits c tag len = ptrBits c 0 len := by
  rw [ptrBits, ptrBits, maxoutBits_0]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have ones := allOnes_bit (width := width) (c.lenBits + 1) 0 i hi
  have tagRange := fun hb => maxoutBits_bit (width := width) tag c.tagBits (1 + c.lenBits) i hb hi
  have lenRange := fun hb => maxoutBits_bit (width := width) len c.lenBits 1 i hb hi
  by_cases low : i < c.lenBits + 1
  · have ht : (maxoutBits tag c.tagBits (1 + c.lenBits) : BitVec width).getLsbD i = false := by
      cases h : (maxoutBits tag c.tagBits (1 + c.lenBits) : BitVec width).getLsbD i
      · rfl
      · have := tagRange h; omega
    simp [BitVec.getLsbD_and, BitVec.getLsbD_or, ones.mpr ⟨Nat.zero_le _, low⟩, ht]
  · have hoff : (allOnes (c.lenBits + 1) 0 : BitVec width).getLsbD i = false := by
      cases h : (allOnes (c.lenBits + 1) 0 : BitVec width).getLsbD i
      · rfl
      · exact absurd (ones.mp h).2 low
    have hl : (maxoutBits len c.lenBits 1 : BitVec width).getLsbD i = false := by
      cases h : (maxoutBits len c.lenBits 1 : BitVec width).getLsbD i
      · rfl
      · have := lenRange h; omega
    simp [BitVec.getLsbD_and, BitVec.getLsbD_or, hoff, hl]

/-- Pointer annotations with in-range fields are determined by their fields. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "ptr_bits_eq_ptr_bits"
  (words_as_type_indexed_bitvec)]
theorem ptrBits_eq_ptrBits {width : Nat} [NeZero width] (c : Config) (tag len tag2 len2 : Nat)
    (h : tag < 2 ^ c.tagBits - 1 ∧ len < 2 ^ c.lenBits - 1 ∧ c.lenBits + c.tagBits < width) :
    ((ptrBits c tag2 len2 : BitVec width) ||| 1 = ptrBits c tag len ||| 1 ↔
      tag2 = tag ∧ len2 = len) := by
  obtain ⟨htag, hlen, hw⟩ := h
  have tagR := fun (t : Nat) i (hi : i < width) hb =>
    maxoutBits_bit (width := width) t c.tagBits (1 + c.lenBits) i hb hi
  have lenR := fun (t : Nat) i (hi : i < width) hb =>
    maxoutBits_bit (width := width) t c.lenBits 1 i hb hi
  have oneBit : ∀ i, i < width → (1 : BitVec width).getLsbD i = true → i = 0 := by
    intro i hi hb
    by_contra h0
    simp [h0] at hb
  have tl : ∀ t u : Nat, (maxoutBits t c.tagBits (1 + c.lenBits) : BitVec width) &&&
      maxoutBits u c.lenBits 1 = 0 := by
    intro t u
    apply and_eq_zero_of_disjoint
    intro i hi h1 h2
    have := tagR t i hi h1; have := lenR u i hi h2; omega
  have p1 : ∀ t u : Nat, (ptrBits c t u : BitVec width) &&& 1 = 0 := by
    intro t u
    apply and_eq_zero_of_disjoint
    intro i hi h1 h2
    have := oneBit i hi h2
    subst this
    simp only [ptrBits, BitVec.getLsbD_or] at h1
    rcases Bool.or_eq_true_iff.mp h1 with h | h
    · have := tagR t 0 hi h; omega
    · have := lenR u 0 hi h; omega
  rw [word_or_eq_word_or_split _ _ _ _ ⟨p1 _ _, p1 _ _, p1 _ _, p1 _ _⟩]
  simp only [and_true]
  unfold ptrBits
  rw [word_or_eq_word_or_split _ _ _ _ ⟨tl _ _, tl _ _, tl _ _, tl _ _⟩,
    maxoutBits_eq tag2 tag c.tagBits (1 + c.lenBits) ⟨by omega, htag⟩,
    maxoutBits_eq len2 len c.lenBits 1 ⟨by omega, hlen⟩]

/-- With a zero tag, pointer annotations are determined by the length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "ptr_bits_eq_ptr_bits_len_only"
  (words_as_type_indexed_bitvec)]
theorem ptrBits_eq_ptrBits_len_only {width : Nat} [NeZero width] (c : Config) (len len2 : Nat)
    (h : len < 2 ^ c.lenBits - 1 ∧ c.lenBits < width) :
    ((ptrBits c 0 len2 : BitVec width) ||| 1 = ptrBits c 0 len ||| 1 ↔ len2 = len) := by
  obtain ⟨hlen, hw⟩ := h
  have lenR := fun (t : Nat) i (hi : i < width) hb =>
    maxoutBits_bit (width := width) t c.lenBits 1 i hb hi
  have p1 : ∀ u : Nat, (maxoutBits u c.lenBits 1 : BitVec width) &&& 1 = 0 := by
    intro u
    apply and_eq_zero_of_disjoint
    intro i hi h1 h2
    have := lenR u i hi h1
    have : i = 0 := by
      by_contra h0
      simp [h0] at h2
    omega
  have z : ∀ x : BitVec width, 0 ||| x = x := fun x => by
    apply BitVec.eq_of_getLsbD_eq; intro i _; simp
  simp only [ptrBits, maxoutBits_0, z]
  rw [word_or_eq_word_or_split _ _ _ _ ⟨p1 _, p1 _, p1 _, p1 _⟩, and_iff_left rfl,
    maxoutBits_eq len2 len c.lenBits 1 ⟨by omega, hlen⟩]

/-- Below bit `a`, `2 ^ b - i` and `2 ^ a - i` agree when `i ≤ 2 ^ a ≤ 2 ^ b`.
Flapjack arithmetic infrastructure for the two `BIT` lemmas. -/
theorem testBit_two_pow_sub_eq (a b n i : Nat) (ha : n < a) (hab : a ≤ b) (hi : i ≤ 2 ^ a) :
    Nat.testBit (2 ^ b - i) n = Nat.testBit (2 ^ a - i) n := by
  have hP : 2 ^ b = 2 ^ a * 2 ^ (b - a) := by rw [← Nat.pow_add]; congr 1; omega
  have hc : 1 ≤ 2 ^ (b - a) := Nat.one_le_two_pow
  have e : 2 ^ b - i = 2 ^ a * (2 ^ (b - a) - 1) + (2 ^ a - i) := by
    rw [hP, Nat.mul_sub_one]
    have : 2 ^ a ≤ 2 ^ a * 2 ^ (b - a) := Nat.le_mul_of_pos_right _ hc
    omega
  have m : (2 ^ b - i) % 2 ^ a = (2 ^ a - i) % 2 ^ a := by
    rw [e, Nat.mul_add_mod]
  have h1 := Nat.testBit_mod_two_pow (2 ^ b - i) a n
  have h2 := Nat.testBit_mod_two_pow (2 ^ a - i) a n
  rw [m] at h1
  have := h1.symm.trans h2
  simpa [ha] using this

/-- A bit of `2 ^ k - i` below `k` can be read at the smaller exponent
`MAX n i + 1`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "BIT_lemma"]
theorem bit_lemma (n k i : Nat) :
    Nat.testBit (2 ^ k - i) n = true ↔
      (if n < k ∧ i < 2 ^ k ∧ i ≠ 0 then Nat.testBit (2 ^ (max n i + 1) - i) n = true
       else Nat.testBit (2 ^ k - i) n = true) := by
  split
  · rename_i h
    obtain ⟨h1, h2, h3⟩ := h
    have hiK : i ≤ 2 ^ (max n i + 1) := by
      have : i < 2 ^ i := Nat.lt_two_pow_self
      have : 2 ^ i ≤ 2 ^ (max n i + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rcases Nat.le_total k (max n i + 1) with hk | hk
    · rw [testBit_two_pow_sub_eq k (max n i + 1) n i h1 hk (by omega)]
    · rw [testBit_two_pow_sub_eq (max n i + 1) k n i (by omega) hk hiK]
  · exact Iff.rfl

/-- Bit `m` of `2 ^ k - n` is set when `0 < n ≤ 2 ^ m` and `m < k`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "BIT_Lemma2"]
theorem bit_lemma2 (m k n : Nat) :
    Nat.testBit (2 ^ k - n) m = true ↔
      (if n ≠ 0 ∧ n ≤ 2 ^ m ∧ m < k then True else Nat.testBit (2 ^ k - n) m = true) := by
  split
  · rename_i h
    obtain ⟨h1, h2, h3⟩ := h
    simp only [iff_true]
    have hle : n ≤ 2 ^ (m + 1) := le_trans h2 (Nat.pow_le_pow_right (by decide) (by omega))
    rw [testBit_two_pow_sub_eq (m + 1) k m n (by omega) (by omega) hle]
    have hp : 2 ^ (m + 1) = 2 ^ m * 2 := by rw [Nat.pow_succ]
    have e : 2 ^ (m + 1) - n = 2 ^ m + (2 ^ m - n) := by omega
    have hr : 2 ^ m - n < 2 ^ m := by omega
    rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr]
    rfl
  · exact Iff.rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

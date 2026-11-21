module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StoreList
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.PointerBits
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberCompare
public import Flapjack.Compiler.Backend.GcShared.Reachability
public import Flapjack.Misc.Multiword
public import Flapjack.Misc.GoodDimindex
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Arithmetic, word and `store_list` lemmas of `data_to_word_memoryProof`

Counterparts of `b2w_def`, `LENGTH_EQ_1/2/3`, `encode_header_NEQ_0`,
`ADD_DIV_EQ`, `LESS_DIV_16_IMP`, `MIN_ADD`, `MIN_SUB`, `MAX_ADD`, `MAX_SUB`,
`small_int_w2n`, the `store_list_*` lemmas, `ptr_bits_or_1_add_1`,
`all_ones_n2w`, `minus_lemma`, `n2w_lsr_eq_0` and `IN_reachable_addresses` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`. HOL
`n2w` is `BitVec.ofNat`, `w2n` is `BitVec.toNat`, `>>>` (`word_lsr`) is
`>>>`, `x ∈ dm` for the Boolean domain predicate is `dm x = true`, and
`(a =+ v) m` is `fun k => if k = a then v else m k`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

/-- HOL `b2w_def` (the restated theorem); its two conjuncts have independent
word types. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "b2w_def"
  (words_as_type_indexed_bitvec)]
theorem b2w_eq {wa : Nat} {wb : Nat} [NeZero wa] [NeZero wb] :
    (Misc.Multiword.b2w true : BitVec wa) = 1 ∧ (Misc.Multiword.b2w false : BitVec wb) = 0 := by
  constructor <;> rfl

/-- HOL `LENGTH_EQ_1`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "LENGTH_EQ_1"]
theorem length_eq_one {α : Type} (xs : List α) :
    (xs.length = 1 ↔ ∃ a1, xs = [a1]) ∧ (1 = xs.length ↔ ∃ a1, xs = [a1]) := by
  have h : xs.length = 1 ↔ ∃ a1, xs = [a1] := List.length_eq_one_iff
  exact ⟨h, eq_comm.trans h⟩

/-- HOL `LENGTH_EQ_2`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "LENGTH_EQ_2"]
theorem length_eq_two {α : Type} (xs : List α) :
    (xs.length = 2 ↔ ∃ a1 a2, xs = [a1, a2]) ∧ (2 = xs.length ↔ ∃ a1 a2, xs = [a1, a2]) := by
  have h : xs.length = 2 ↔ ∃ a1 a2, xs = [a1, a2] := List.length_eq_two
  exact ⟨h, eq_comm.trans h⟩

/-- HOL `LENGTH_EQ_3`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "LENGTH_EQ_3"]
theorem length_eq_three {α : Type} (xs : List α) :
    (xs.length = 3 ↔ ∃ a1 a2 a3, xs = [a1, a2, a3]) ∧
      (3 = xs.length ↔ ∃ a1 a2 a3, xs = [a1, a2, a3]) := by
  have h : xs.length = 3 ↔ ∃ a1 a2 a3, xs = [a1, a2, a3] := List.length_eq_three
  exact ⟨h, eq_comm.trans h⟩

/-- HOL `encode_header_NEQ_0`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "encode_header_NEQ_0"
  (words_as_type_indexed_bitvec)]
theorem encodeHeader_ne_zero {width : Nat} [NeZero width] (c : Config) (n k : Nat) (w : BitVec width) :
    encodeHeader c n k = some w → w ≠ 0 := by
  intro h
  unfold encodeHeader at h
  split at h
  · cases h
    intro zero
    have pos : 0 < width := NeZero.pos width
    have h3 : (3 : BitVec width).getLsbD 0 = true := by
      simp [BitVec.getLsbD_ofNat, pos]
    have bit : (makeHeader c (BitVec.ofNat width n) k).getLsbD 0 = true := by
      simp only [makeHeader, BitVec.getLsbD_or, h3, Bool.or_true]
    rw [zero] at bit
    simp at bit
  · cases h

/-- HOL `ADD_DIV_EQ`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "ADD_DIV_EQ"]
theorem add_div_eq :
    (∀ n : Nat, 0 < n → ∀ x r : Nat, x + r / n = (x * n + r) / n) ∧
      ∀ n : Nat, 0 < n → ∀ x r : Nat, r / n + x = (r + x * n) / n := by
  constructor
  · intro n pos x r
    rw [Nat.add_comm (x * n), Nat.add_mul_div_right r x pos, Nat.add_comm]
  · intro n pos x r
    rw [Nat.add_mul_div_right r x pos]

/-- HOL `LESS_DIV_16_IMP`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "LESS_DIV_16_IMP"]
theorem less_div_16_imp (n k : Nat) : n < k / 16 → 16 * n + 2 < k := by
  intro h
  omega

/-- HOL `MIN_ADD`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MIN_ADD"]
theorem min_add' (a b c : Nat) : min a b + c = min (a + c) (b + c) := by omega

/-- HOL `MIN_SUB`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MIN_SUB"]
theorem min_sub' (a b c : Nat) : min a b - c = min (a - c) (b - c) := by omega

/-- HOL `MAX_ADD`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MAX_ADD"]
theorem max_add' (a b c : Nat) : max a b + c = max (a + c) (b + c) := by omega

/-- HOL `MAX_SUB`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MAX_SUB"]
theorem max_sub' (a b c : Nat) : max a b - c = max (a - c) (b - c) := by omega

/-- Statement of HOL `small_int_w2n` (`good_dimindex (:α) ⇒ small_int (:α)
(&w2n (w : word8))`). Untagged: its HOL dimension `(:α)` is used only
numerically while the byte is the fixed-width `word8`, and neither
`word_dimension_as_width` (word-free signatures only) nor
`words_as_type_indexed_bitvec` (type-indexed words only) admits that
combination yet. Tag it once a qualifier route exists. -/
theorem smallInt_w2n (width : Nat) [NeZero width] (w : BitVec 8) :
    goodDimindex width → smallInt width (w.toNat : Int) := by
  intro good
  have lt := w.isLt
  rcases good with rfl | rfl <;> simp [smallInt] <;> omega

/-- HOL `store_list_domain`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "store_list_domain"
  (words_as_type_indexed_bitvec)]
theorem storeList_domain {width : Nat} [NeZero width] :
    ∀ (a : BitVec width) (xs : List (WordLocW width)) (m : BitVec width → WordLocW width)
      (dm : BitVec width → Bool) (m1 : BitVec width → WordLocW width),
      storeList a xs m dm = some m1 →
      ∀ n, n < xs.length → dm (a + BitVec.ofNat width n * wordSemBytesInWord) = true := by
  intro a xs
  induction xs generalizing a with
  | nil => intro m dm m1 _ n h; simp at h
  | cons x xs ih =>
    intro m dm m1 store n h
    simp only [storeList] at store
    split at store
    · rename_i inDomain
      cases n with
      | zero => simpa using inDomain
      | succ n =>
        have := ih _ _ dm m1 store n (by simpa using h)
        rw [show a + BitVec.ofNat width (n + 1) * wordSemBytesInWord =
          a + wordSemBytesInWord + BitVec.ofNat width n * wordSemBytesInWord by
            rw [BitVec.ofNat_add, BitVec.add_mul]; simp; ring]
        exact this
    · cases store

/-- HOL `store_list_append`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "store_list_append"
  (words_as_type_indexed_bitvec)]
theorem storeList_append {width : Nat} [NeZero width] :
    ∀ (xs ys : List (WordLocW width)) (a : BitVec width) (dm : BitVec width → Bool)
      (m m1 : BitVec width → WordLocW width),
      storeList a (xs ++ ys) m dm = some m1 ↔
        ∃ m0, storeList a xs m dm = some m0 ∧
          storeList (a + wordSemBytesInWord * BitVec.ofNat width xs.length) ys m0 dm = some m1 := by
  intro xs
  induction xs with
  | nil => intro ys a dm m m1; simp [storeList]
  | cons x xs ih =>
    intro ys a dm m m1
    simp only [List.cons_append, storeList]
    split
    · rw [ih]
      have succ : BitVec.ofNat width (xs.length + 1) = BitVec.ofNat width xs.length + 1 := by
        rw [BitVec.ofNat_add]; rfl
      have addr : a + wordSemBytesInWord + wordSemBytesInWord * BitVec.ofNat width xs.length =
          a + wordSemBytesInWord * BitVec.ofNat width (xs.length + 1) := by
        rw [succ]; ring
      simp [addr]
    · simp

/-- HOL `store_list_append_imp`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "store_list_append_imp"
  (words_as_type_indexed_bitvec)]
theorem storeList_append_imp {width : Nat} [NeZero width] :
    ∀ (w1 : List (WordLocW width)) (a : BitVec width) (m : BitVec width → WordLocW width)
      (dm : BitVec width → Bool) (m' : BitVec width → WordLocW width) (w2 : List (WordLocW width)),
      storeList a (w1 ++ w2) m dm = some m' →
      ∃ m'', storeList a w1 m dm = some m'' ∧
        storeList (a + BitVec.ofNat width w1.length * wordSemBytesInWord) w2 m'' dm = some m' := by
  intro w1 a m dm m' w2 h
  obtain ⟨m0, h1, h2⟩ := (storeList_append w1 w2 a dm m m').mp h
  exact ⟨m0, h1, by rw [BitVec.mul_comm]; exact h2⟩

/-- HOL `store_list_update_m_outside`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "store_list_update_m_outside"
  (words_as_type_indexed_bitvec)]
theorem storeList_update_outside {width : Nat} [NeZero width] (a' : BitVec width) (v : WordLocW width) :
    ∀ (ws : List (WordLocW width)) (a : BitVec width) (m : BitVec width → WordLocW width)
      (dm : BitVec width → Bool) (m' : BitVec width → WordLocW width),
      storeList a ws m dm = some m' ∧
          (∀ i, i < ws.length → a + BitVec.ofNat width i * wordSemBytesInWord ≠ a') →
        storeList a ws (fun k => if k = a' then v else m k) dm =
          some (fun k => if k = a' then v else m' k) := by
  intro ws
  induction ws with
  | nil => rintro a m dm m' ⟨h, _⟩; simp [storeList] at h ⊢; subst h; rfl
  | cons x xs ih =>
    rintro a m dm m' ⟨store, outside⟩
    simp only [storeList] at store ⊢
    split at store
    · rename_i inDomain
      simp only [inDomain, if_true]
      have ne : a ≠ a' := by simpa using outside 0 (by simp)
      have step := ih (a + wordSemBytesInWord) (fun key => if key = a then x else m key) dm m' ⟨store, ?_⟩
      · rw [← step]
        congr 1
        funext k
        by_cases ka : k = a <;> by_cases ka' : k = a' <;> simp_all
      · intro i hi
        have := outside (i + 1) (by simpa using hi)
        rwa [show a + BitVec.ofNat width (i + 1) * wordSemBytesInWord =
          a + wordSemBytesInWord + BitVec.ofNat width i * wordSemBytesInWord by
            rw [BitVec.ofNat_add, BitVec.add_mul]; simp; ring] at this
    · cases store

/-- The lowest bit of every `maxout_bits` field shifted by at least one is clear. -/
theorem maxoutBits_bit0 {width : Nat} [NeZero width] (n l b : Nat) (pos : 1 ≤ b) :
    (maxoutBits n l b : BitVec width).getLsbD 0 = false := by
  cases h : (maxoutBits n l b : BitVec width).getLsbD 0
  · rfl
  · have := (maxoutBits_bit n l b 0 h (NeZero.pos width)).1
    omega

/-- HOL `ptr_bits_or_1_add_1`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "ptr_bits_or_1_add_1"
  (words_as_type_indexed_bitvec)]
theorem ptrBits_or_one_add_one {width : Nat} [NeZero width] (c : Config) (tag len : Nat) :
    (ptrBits c tag len : BitVec width) ||| 1 = ptrBits c tag len + 1 := by
  have bit0 : (ptrBits c tag len : BitVec width).getLsbD 0 = false := by
    simp only [ptrBits, BitVec.getLsbD_or, maxoutBits_bit0 _ _ _ (by omega : 1 ≤ 1 + c.lenBits),
      maxoutBits_bit0 _ _ _ (le_refl 1), Bool.false_or]
  rw [BitVec.add_eq_or_of_and_eq_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero]
  by_cases z : i = 0
  · subst z; simp [bit0]
  · simp [z]

/-- HOL `all_ones_n2w`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_ones_n2w"
  (words_as_type_indexed_bitvec)]
theorem allOnes_n2w {width : Nat} [NeZero width] (l b : Nat) :
    (allOnes (l + b) b : BitVec width) = BitVec.ofNat width (2 ^ l - 1) <<< b := by
  rw [Nat.add_comm, Flapjack.Compiler.Backend.DataToWord.allOnes_eq_inlined]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_mul_mod]

/-- HOL `minus_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "minus_lemma"
  (words_as_type_indexed_bitvec)]
theorem minus_lemma {width : Nat} [NeZero width] (w : BitVec width) :
    -1 * (wordSemBytesInWord * w) = wordSemBytesInWord * -w := by
  rw [neg_one_mul, mul_neg]

/-- HOL `n2w_lsr_eq_0`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "n2w_lsr_eq_0"
  (words_as_type_indexed_bitvec)]
theorem n2w_lsr_eq_zero {width : Nat} [NeZero width] (n k : Nat) :
    n / 2 ^ k = 0 ∧ n < 2 ^ width → (BitVec.ofNat width n : BitVec width) >>> k = 0 := by
  rintro ⟨d, lt⟩
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt lt, Nat.shiftRight_eq_div_pow, d]

/-- HOL `IN_reachable_addresses` (a `[local]` theorem derived by
`SIMP_CONV`; the typed statement is a replay of that derivation). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "IN_reachable_addresses"]
theorem in_reachableAddresses {α β γ : Type} (x : Nat) (roots : List (HeapAddress α))
    (heap : List (HeapElement β γ)) :
    reachableAddresses roots heap x ↔
      ∃ (t : α) (x' : Nat), HeapAddress.pointer x' t ∈ roots ∧ Relation.ReflTransGen (gcEdge heap) x' x :=
  Iff.rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

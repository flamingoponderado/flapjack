module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ConsInvariant

@[expose] public section

/-!
# Timestamp binding lemmas

Counterparts of the `bind_each_*` lemmas and `FDOM_bind_each_lemma` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`. As in
`ConsInvariant.lean`, `x ∈ FDOM m` is `m.lookup x ≠ none`, `m ' x` is
`holFapply m x`, `|+` is `HolFiniteMapExact.update`, and a set
`{x | P x}` is its membership predicate; a set equality is an equality of
membership predicates and `s ⊆ t` is `∀ x, s x → t x`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendCommon

/-- Closed form of `bindEach` lookups. Flapjack proof infrastructure. -/
theorem lookup_bindEach_closed (tf : HolFiniteMapExact Nat Nat) (i x : Nat) :
    ∀ (n ts k : Nat), (bindEach tf ts k i n).lookup x =
      if ts ≤ x ∧ x < ts + n then some (k + i * (x - ts)) else tf.lookup x := by
  intro n
  induction n with
  | zero => intro ts k; simp [bindEach]
  | succ n ih =>
    intro ts k
    rw [lookup_bindEach, ih]
    by_cases h : ts = x
    · subst h; simp
    · rw [if_neg h]
      by_cases r : ts + 1 ≤ x ∧ x < ts + 1 + n
      · rw [if_pos r, if_pos (by omega)]
        congr 1
        have : x - ts = (x - (ts + 1)) + 1 := by omega
        rw [this, Nat.mul_succ]; omega
      · rw [if_neg r, if_neg (by omega)]

/-- Extensionality for the canonical finite map. Flapjack proof infrastructure. -/
theorem bindEach_mapExt {left right : HolFiniteMapExact Nat Nat}
    (h : ∀ k, left.lookup k = right.lookup k) : left = right := by
  cases left; cases right; congr; funext k; exact h k

theorem holFapply_bindEach_closed (tf : HolFiniteMapExact Nat Nat) (ts k i n x : Nat) :
    holFapply (bindEach tf ts k i n) x =
      if ts ≤ x ∧ x < ts + n then k + i * (x - ts) else holFapply tf x := by
  unfold holFapply
  rw [lookup_bindEach_closed]
  by_cases h : ts ≤ x ∧ x < ts + n
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- HOL `bind_each_eq_tf`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bind_each_eq_tf"
  (fmap_as_finite_support_relation := [tf])]
theorem bindEach_eq_tf :
    ∀ (k : Nat) (tf : HolFiniteMapExact Nat Nat) (ts n i x : Nat),
      (∀ t, tf.lookup t ≠ none → t < ts) ∧ x < ts →
        holFapply (bindEach tf ts n i k) x = holFapply tf x := by
  rintro k tf ts n i x ⟨_, lt⟩
  rw [holFapply_bindEach_closed, if_neg (by omega)]

/-- HOL `bind_each_FDOM`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bind_each_FDOM"
  (fmap_as_finite_support_relation := [tf])]
theorem bindEach_fdom :
    ∀ (n : Nat) (tf : HolFiniteMapExact Nat Nat) (ts k i : Nat),
      (fun x => (bindEach tf ts k i n).lookup x ≠ none) =
        fun x => tf.lookup x ≠ none ∨ (ts ≤ x ∧ x < ts + n) := by
  intro n tf ts k i
  funext x
  rw [lookup_bindEach_closed]
  by_cases h : ts ≤ x ∧ x < ts + n <;> simp [h]

/-- HOL `bind_each_eq_tf_FDOM`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bind_each_eq_tf_FDOM"
  (fmap_as_finite_support_relation := [tf])]
theorem bindEach_eq_tf_fdom :
    ∀ (k : Nat) (tf : HolFiniteMapExact Nat Nat) (ts n i x : Nat),
      (∀ t, tf.lookup t ≠ none → t < ts) ∧ x < ts ∧ (bindEach tf ts n i k).lookup x ≠ none →
        tf.lookup x ≠ none := by
  rintro k tf ts n i x ⟨_, lt, dom⟩
  rwa [lookup_bindEach_closed, if_neg (by omega)] at dom

/-- HOL `bind_each_eq_lt_FAPPLY`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bind_each_eq_lt_FAPPLY"
  (fmap_as_finite_support_relation := [tf])]
theorem bindEach_eq_lt_fapply :
    ∀ (n : Nat) (tf : HolFiniteMapExact Nat Nat) (ts k i x : Nat),
      holFapply (bindEach tf ts k i n) x < k →
        holFapply (bindEach tf ts k i n) x = holFapply tf x := by
  intro n tf ts k i x lt
  rw [holFapply_bindEach_closed] at lt ⊢
  split at lt
  · omega
  · rename_i h; rw [if_neg h]

/-- HOL `bind_each_eq_lt_FDOM`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bind_each_eq_lt_FDOM"
  (fmap_as_finite_support_relation := [tf])]
theorem bindEach_eq_lt_fdom :
    ∀ (n : Nat) (tf : HolFiniteMapExact Nat Nat) (ts k i x : Nat),
      (bindEach tf ts k i n).lookup x ≠ none ∧ holFapply (bindEach tf ts k i n) x < k →
        tf.lookup x ≠ none := by
  rintro n tf ts k i x ⟨dom, lt⟩
  rw [holFapply_bindEach_closed] at lt
  rw [lookup_bindEach_closed] at dom
  split at lt
  · omega
  · rwa [if_neg (by assumption)] at dom

/-- HOL `bind_each_eq_gt_FAPPLY`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bind_each_eq_gt_FAPPLY"
  (fmap_as_finite_support_relation := [tf])]
theorem bindEach_eq_gt_fapply :
    ∀ (n : Nat) (tf : HolFiniteMapExact Nat Nat) (ts k i x : Nat),
      i * n + k < holFapply (bindEach tf ts k i n) x →
        holFapply (bindEach tf ts k i n) x = holFapply tf x := by
  intro n tf ts k i x lt
  rw [holFapply_bindEach_closed] at lt ⊢
  split at lt
  · rename_i h
    have : i * (x - ts) ≤ i * n := Nat.mul_le_mul_left i (by omega)
    omega
  · rename_i h; rw [if_neg h]

/-- HOL `bind_each_eq_gt_FDOM`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bind_each_eq_gt_FDOM"
  (fmap_as_finite_support_relation := [tf])]
theorem bindEach_eq_gt_fdom :
    ∀ (n : Nat) (tf : HolFiniteMapExact Nat Nat) (ts k i x : Nat),
      (bindEach tf ts k i n).lookup x ≠ none ∧ i * n + k < holFapply (bindEach tf ts k i n) x →
        tf.lookup x ≠ none := by
  rintro n tf ts k i x ⟨dom, lt⟩
  rw [holFapply_bindEach_closed] at lt
  rw [lookup_bindEach_closed] at dom
  split at lt
  · rename_i h
    have : i * (x - ts) ≤ i * n := Nat.mul_le_mul_left i (by omega)
    omega
  · rwa [if_neg (by assumption)] at dom

/-- HOL `bind_each_eq_ge_FDOM`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bind_each_eq_ge_FDOM"
  (fmap_as_finite_support_relation := [tf])]
theorem bindEach_eq_ge_fdom :
    ∀ (n : Nat) (tf : HolFiniteMapExact Nat Nat) (ts k i x : Nat),
      (bindEach tf ts k i n).lookup x ≠ none ∧ i * n + k ≤ holFapply (bindEach tf ts k i n) x ∧ i ≠ 0 →
        tf.lookup x ≠ none := by
  rintro n tf ts k i x ⟨dom, le, nz⟩
  rw [holFapply_bindEach_closed] at le
  rw [lookup_bindEach_closed] at dom
  split at le
  · rename_i h
    have : i * (x - ts) < i * n := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    omega
  · rwa [if_neg (by assumption)] at dom

/-- HOL `bind_each_fdom_limit`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bind_each_fdom_limit"
  (fmap_as_finite_support_relation := [tf])]
theorem bindEach_fdom_limit :
    ∀ (k : Nat) (tf : HolFiniteMapExact Nat Nat) (ts n i x : Nat),
      (∀ t, tf.lookup t ≠ none → t < ts) ∧ ts + k < x →
        ¬ (bindEach tf ts n i k).lookup x ≠ none := by
  rintro k tf ts n i x ⟨bound, lt⟩ dom
  rw [lookup_bindEach_closed, if_neg (by omega)] at dom
  have := bound x dom
  omega

/-- HOL `bind_each_FUPDATE`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bind_each_FUPDATE"
  (fmap_as_finite_support_relation := [tf])]
theorem bindEach_fupdate :
    ∀ (n i : Nat) (tf : HolFiniteMapExact Nat Nat) (ts1 ts2 k1 k2 : Nat),
      ts1 < ts2 ∧ k1 < k2 →
        bindEach (tf.update (ts1, k1)) ts2 k2 i n = (bindEach tf ts2 k2 i n).update (ts1, k1) := by
  rintro n i tf ts1 ts2 k1 k2 ⟨lt, _⟩
  apply bindEach_mapExt
  intro x
  rw [lookup_bindEach_closed]
  simp only [HolFiniteMapExact.update, FUPDATE, beq_iff_eq]
  rw [lookup_bindEach_closed]
  by_cases h : ts2 ≤ x ∧ x < ts2 + n
  · rw [if_pos h, if_neg (by omega), if_pos h]
  · rw [if_neg h, if_neg h]

/-- HOL `bind_each_MINUS`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bind_each_MINUS"
  (fmap_as_finite_support_relation := [tf])]
theorem bindEach_minus :
    ∀ (n : Nat) (tf : HolFiniteMapExact Nat Nat) (ts x k1 k2 i : Nat),
      (∀ t, tf.lookup t ≠ none → t < ts) ∧ (ts ≤ x ∧ x < ts + n) ∧ k2 ≤ k1 →
        holFapply (bindEach tf ts k1 i n) x - k2 = holFapply (bindEach tf ts (k1 - k2) i n) x := by
  rintro n tf ts x k1 k2 i ⟨_, mem, le⟩
  rw [holFapply_bindEach_closed, holFapply_bindEach_closed, if_pos mem, if_pos mem]
  omega

/-- HOL `bind_each_eq_INJ`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bind_each_eq_INJ"
  (fmap_as_finite_support_relation := [tf])]
theorem bindEach_eq_inj :
    ∀ (n x y : Nat) (tf : HolFiniteMapExact Nat Nat) (ts k i : Nat),
      holFapply (bindEach tf ts k i n) x = holFapply (bindEach tf ts k i n) y ∧ i ≠ 0 ∧
        (ts ≤ x ∧ x < ts + n) ∧ ¬ tf.lookup x ≠ none ∧ (ts ≤ y ∧ y < ts + n) ∧ ¬ tf.lookup y ≠ none →
        x = y := by
  rintro n x y tf ts k i ⟨eq, nz, mx, _, my, _⟩
  rw [holFapply_bindEach_closed, holFapply_bindEach_closed, if_pos mx, if_pos my] at eq
  have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero nz) (Nat.add_left_cancel eq)
  omega

/-- HOL `FDOM_bind_each_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "FDOM_bind_each_lemma"
  (fmap_as_finite_support_relation := [tf])]
theorem fdom_bindEach_lemma (n : Nat) :
    ∀ (tf : HolFiniteMapExact Nat Nat) (k ts h : Nat),
      (∀ x, tf.lookup x ≠ none → x < ts) →
        ∀ x, (bindEach tf ts h n k).lookup x ≠ none → x < ts + k := by
  intro tf k ts h bound x dom
  rw [lookup_bindEach_closed] at dom
  split at dom
  · omega
  · have := bound x dom; omega


/-- HOL `isSomeDataElement_heap_lookup` (the rebound declaration at line
16578). The capture types the `Unused sp` inside `el_length` at its own
independent element types `γ δ`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "isSomeDataElement_heap_lookup" 16578]
theorem isSomeDataElement_heapLookup_unused {α β γ δ : Type} :
    ∀ (n : Nat) (a : List (HeapElement α β)) (sp : Nat) (b : List (HeapElement α β)),
      isSomeDataElement (heapLookup n (a ++ [.unused sp] ++ b)) →
        n < heapLength a ∨ elLength (.unused sp : HeapElement γ δ) + heapLength a ≤ n := by
  intro n a sp b some
  by_cases lt : n < heapLength a
  · exact .inl lt
  · right
    rw [List.append_assoc, heapLookup_append1 a n _ (by omega)] at some
    simp only [elLength]
    by_contra ge
    obtain ⟨_, _, _, h⟩ := some
    by_cases z : n - heapLength a = 0
    · simp [heapLookup, z] at h
    · simp [heapLookup, z, elLength, show n - heapLength a < sp + 1 by omega] at h

/-- Data-element positions of a cons-block chain. Flapjack proof
infrastructure. -/
theorem isSomeDataElement_listToBlockReps {width : Nat} [NeZero width] {β : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (p : HeapAddress (WordLocW width)) :
    ∀ (ls : List (HeapAddress (WordLocW width))) (k n : Nat), ls ≠ [] →
      (isSomeDataElement (heapLookup n (listToBlockReps conf p k ls : List (HeapElement _ (HeapTag × List β)))) ↔
        n % 3 = 0 ∧ n / 3 < ls.length) := by
  intro ls
  induction ls with
  | nil => intro k n h; exact absurd rfl h
  | cons h l ih =>
    intro k n _
    cases l with
    | nil =>
      rw [listToBlockReps_single]
      by_cases z : n = 0
      · subst z; simp [heapLookup, isSomeDataElement, blockRep]
      · constructor
        · rintro ⟨_, _, _, e⟩
          by_cases lt : n < 3
          · simp [heapLookup, z, blockRep, elLength, lt] at e
          · simp [heapLookup, z, blockRep, elLength, lt] at e
        · intro c; simp at c; omega
    | cons h' l' =>
      rw [listToBlockReps_cons]
      by_cases z : n = 0
      · subst z; simp [heapLookup, isSomeDataElement, blockRep]
      · by_cases lt : n < 3
        · constructor
          · rintro ⟨_, _, _, e⟩
            simp [heapLookup, z, blockRep, elLength, lt] at e
          · intro c; omega
        · have step : heapLookup n (blockRep consTag [h, .pointer (k + 3) (.word (ptrBits conf consTag 2))] ::
              listToBlockReps conf p (k + 3) (h' :: l') : List (HeapElement _ (HeapTag × List β))) =
              heapLookup (n - 3) (listToBlockReps conf p (k + 3) (h' :: l')) := by
            simp [heapLookup, z, blockRep, elLength, lt]
          rw [step, ih (k + 3) (n - 3) (by simp)]
          simp only [List.length_cons]
          omega

/-- HOL `isSomeDataElement_heap_lookup_eq`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "isSomeDataElement_heap_lookup_eq"
  (words_as_type_indexed_bitvec)]
theorem isSomeDataElement_heapLookup_eq {width : Nat} [NeZero width] {β : Type} :
    ∀ (ls : List (HeapAddress (WordLocW width))) (n : Nat) (p : HeapAddress (WordLocW width)) (k1 k2 : Nat)
      (conf : Flapjack.Compiler.Backend.DataToWord.Config),
      isSomeDataElement (heapLookup n
        (listToBlockReps conf p k2 ls : List (HeapElement (WordLocW width) (HeapTag × List β)))) →
      isSomeDataElement (heapLookup n
        (listToBlockReps conf p k1 ls : List (HeapElement (WordLocW width) (HeapTag × List β)))) := by
  intro ls n p k1 k2 conf hs
  cases ls with
  | nil => simpa [listToBlockReps] using hs
  | cons h l =>
    rw [isSomeDataElement_listToBlockReps conf p _ k2 n (by simp)] at hs
    rwa [isSomeDataElement_listToBlockReps conf p _ k1 n (by simp)]

/-- HOL `bind_each_isSomeDataElement`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bind_each_isSomeDataElement"
  (fmap_as_finite_support_relation := [tf]) (words_as_type_indexed_bitvec)]
theorem bindEach_isSomeDataElement {width : Nat} [NeZero width] {β : Type} :
    ∀ (l : List (HeapAddress (WordLocW width))) (tf : HolFiniteMapExact Nat Nat) (ts x : Nat)
      (p : HeapAddress (WordLocW width)) (k : Nat) (conf : Flapjack.Compiler.Backend.DataToWord.Config),
      l ≠ [] ∧ (ts ≤ x ∧ x < ts + l.length) ∧ (∀ t, tf.lookup t ≠ none → t < ts) →
        isSomeDataElement (heapLookup (holFapply (bindEach tf ts 0 3 l.length) x)
          (listToBlockReps conf p k l : List (HeapElement (WordLocW width) (HeapTag × List β)))) := by
  rintro l tf ts x p k conf ⟨ne, mem, _⟩
  rw [holFapply_bindEach_closed, if_pos mem, isSomeDataElement_listToBlockReps conf p l k _ ne]
  omega
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values.AllValues
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values.TimestampSets
public import Flapjack.Compiler.Backend.Semantics.DataSem.Build
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.BindEach

@[expose] public section

/-!
# Timestamps and nested values of an allocated list

Counterparts of `all_ts_list_to_v_SUBSET`, `all_ts_SUBSET_list_to_v`,
`new_all_ts_SUBSET_list_to_v`, `v_all_vs_list_to_v1`, `blocks_unique_GT_ts`,
`Block_NOT_IN_all_vs`, `v_all_vs_list_to_v2` and `blocks_unique_cons_multi` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`.
`list_to_v` is dataSem's `listToValue`, `v_all_vs` is `valueListValues`,
`all_vs` and `all_ts` are the predicates `allValues` and `allTimestamps`
(`x ∈ s` is `s x`), `s ⊆ t` is `∀ x, s x → t x`, a set `{x | P x}` is its
membership predicate and `MEM` is list membership.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem
open Flapjack.Compiler.Backend.BackendCommon

/-- Membership in `v_all_vs` is membership in the traversal of some element.
Flapjack proof infrastructure. -/
theorem mem_valueListValues_iff (z : Value) :
    ∀ (l : List Value), z ∈ valueListValues l ↔ ∃ v ∈ l, z ∈ valueListValues [v] := by
  intro l
  induction l with
  | nil => simp [valueListValues]
  | cons a l ih =>
    rw [valueListValues_cons, List.mem_append, ih]
    simp

/-- Nested values of an allocated list: its spine blocks, plus the nested
values of the tail and the elements. Flapjack proof infrastructure. -/
theorem mem_valueListValues_listToValue (t z : Value) :
    ∀ (xs : List Value) (ts : Nat) (stack : List Value),
      z ∈ valueListValues (listToValue ts t xs :: stack) ↔
        (∃ j, j < xs.length ∧ z = listToValue (ts + j) t (xs.drop j)) ∨
          z ∈ valueListValues (t :: (xs ++ stack)) := by
  have consIff : ∀ (a : Value) (l : List Value), z ∈ valueListValues (a :: l) ↔
      z ∈ valueListValues [a] ∨ z ∈ valueListValues l := by
    intro a l; rw [valueListValues_cons, List.mem_append]
  have appIff : ∀ (l1 l2 : List Value), z ∈ valueListValues (l1 ++ l2) ↔
      z ∈ valueListValues l1 ∨ z ∈ valueListValues l2 := by
    intro l1 l2; rw [valueListValues_append, List.mem_append]
  intro xs
  induction xs with
  | nil => intro ts stack; simp [listToValue]
  | cons x xs ih =>
    intro ts stack
    have blockIff : z ∈ valueListValues [listToValue ts t (x :: xs)] ↔
        z = listToValue ts t (x :: xs) ∨ z ∈ valueListValues [x] ∨
          z ∈ valueListValues [listToValue (ts + 1) t xs] := by
      have e : valueListValues [listToValue ts t (x :: xs)] =
          listToValue ts t (x :: xs) :: valueListValues [x, listToValue (ts + 1) t xs] := by
        simp [listToValue, valueListValues]
      rw [e, List.mem_cons, consIff x]
    have spineIff : (∃ j, j < (x :: xs).length ∧ z = listToValue (ts + j) t ((x :: xs).drop j)) ↔
        z = listToValue ts t (x :: xs) ∨
          ∃ j, j < xs.length ∧ z = listToValue (ts + 1 + j) t (xs.drop j) := by
      constructor
      · rintro ⟨j, lt, eq⟩
        cases j with
        | zero => exact .inl (by simpa using eq)
        | succ j =>
          refine .inr ⟨j, by simpa using lt, ?_⟩
          rw [eq]; simp [Nat.add_assoc, Nat.add_comm 1 j]
      · rintro (eq | ⟨j, lt, eq⟩)
        · exact ⟨0, by simp, by simpa using eq⟩
        · refine ⟨j + 1, by simpa using lt, ?_⟩
          rw [eq]; simp [Nat.add_assoc, Nat.add_comm 1 j]
    have recur := ih (ts + 1) []
    simp only [List.append_nil] at recur
    rw [consIff (listToValue ts t (x :: xs)) stack, blockIff, recur, spineIff, List.cons_append,
      consIff t (x :: (xs ++ stack)), consIff x (xs ++ stack), appIff, consIff t xs]
    simp only [or_assoc, or_comm, or_left_comm]

/-- A spine block of an allocated list. Flapjack proof infrastructure. -/
theorem listToValue_drop_block (t : Value) (xs : List Value) (ts j : Nat) (lt : j < xs.length) :
    ∃ x, listToValue (ts + j) t (xs.drop j) =
      .block (ts + j) consTag [x, listToValue (ts + j + 1) t (xs.drop (j + 1))] := by
  obtain ⟨x, rest, eq⟩ : ∃ x rest, xs.drop j = x :: rest := by
    cases h : xs.drop j with
    | nil => simp at h; omega
    | cons x rest => exact ⟨x, rest, rfl⟩
  have tail : xs.drop (j + 1) = rest := by
    rw [← List.drop_drop, eq]; rfl
  exact ⟨x, by rw [eq, tail]; rfl⟩

/-- `all_vs` of an allocated list. Flapjack proof infrastructure. -/
theorem allValues_listToValue (refs : Spt (BvlSem.Ref Value)) (t : Value) (xs : List Value) (ts : Nat)
    (stack : List Value) (z : Value) :
    allValues refs (listToValue ts t xs :: stack) z ↔
      (∃ j, j < xs.length ∧ z = listToValue (ts + j) t (xs.drop j)) ∨ allValues refs (t :: (xs ++ stack)) z := by
  simp only [allValues, mem_valueListValues_listToValue]
  constructor
  · rintro (h | h | h | h | h)
    exacts [.inr (.inl h), .inr (.inr (.inl h)), .inr (.inr (.inr (.inl h))), .inl h,
      .inr (.inr (.inr (.inr h)))]
  · rintro (h | h | h | h | h)
    exacts [.inr (.inr (.inr (.inl h))), .inl h, .inr (.inl h), .inr (.inr (.inl h)),
      .inr (.inr (.inr (.inr h)))]

/-- Timestamps of an allocated list. Flapjack proof infrastructure. -/
theorem valueTimestamps_listToValue (t : Value) :
    ∀ (xs : List Value) (ts stamp : Nat),
      ((ts ≤ stamp ∧ stamp < ts + xs.length) ∨ stamp ∈ valueTimestamps t ∨
        ∃ x ∈ xs, stamp ∈ valueTimestamps x) → stamp ∈ valueTimestamps (listToValue ts t xs) := by
  intro xs
  induction xs with
  | nil =>
    intro ts stamp h
    rcases h with h | h | ⟨x, mem, _⟩
    · simp at h; omega
    · exact h
    · simp at mem
  | cons x xs ih =>
    intro ts stamp h
    show stamp ∈ valueTimestamps (.block ts consTag [x, listToValue (ts + 1) t xs])
    rw [valueTimestamps]
    simp only [List.mem_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
    rcases h with ⟨lo, hi⟩ | h | ⟨y, mem, inY⟩
    · by_cases e : stamp = ts
      · exact .inl e
      · exact .inr (.inr (ih (ts + 1) stamp (.inl ⟨by omega, by simp at hi; omega⟩)))
    · exact .inr (.inr (ih (ts + 1) stamp (.inr (.inl h))))
    · rcases List.mem_cons.mp mem with rfl | mem
      · exact .inr (.inl inY)
      · exact .inr (.inr (ih (ts + 1) stamp (.inr (.inr ⟨y, mem, inY⟩))))

/-- HOL `all_ts_list_to_v_SUBSET`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_ts_list_to_v_SUBSET"]
theorem allTimestamps_listToValue_subset :
    ∀ (xs : List Flapjack.Compiler.Backend.DataSem.Value) (ts : Nat)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (t : Flapjack.Compiler.Backend.DataSem.Value),
      ∀ x, (ts ≤ x ∧ x < ts + xs.length) → allTimestamps refs [listToValue ts t xs] x := by
  intro xs ts refs t x mem
  exact ⟨listToValue ts t xs, .inr (by simp), valueTimestamps_listToValue t xs ts x (.inl mem)⟩

/-- HOL `all_ts_SUBSET_list_to_v`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_ts_SUBSET_list_to_v"]
theorem allTimestamps_subset_listToValue :
    ∀ (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (t : Flapjack.Compiler.Backend.DataSem.Value)
      (xs stack : List Flapjack.Compiler.Backend.DataSem.Value) (ts : Nat),
      ∀ x, allTimestamps refs (t :: (xs ++ stack)) x → allTimestamps refs (listToValue ts t xs :: stack) x := by
  rintro refs t xs stack ts x ⟨value, source, stamp⟩
  rcases source with inRefs | inStack
  · exact ⟨value, .inl inRefs, stamp⟩
  · simp only [List.mem_cons, List.mem_append] at inStack
    rcases inStack with eq | inXs | inStack
    · exact ⟨listToValue ts t xs, .inr (by simp), valueTimestamps_listToValue _ xs ts x (.inr (.inl (eq ▸ stamp)))⟩
    · exact ⟨listToValue ts t xs, .inr (by simp),
        valueTimestamps_listToValue t xs ts x (.inr (.inr ⟨value, inXs, stamp⟩))⟩
    · exact ⟨value, .inr (by simp [inStack]), stamp⟩

/-- HOL `new_all_ts_SUBSET_list_to_v`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "new_all_ts_SUBSET_list_to_v"]
theorem new_allTimestamps_subset_listToValue :
    ∀ (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (t : Flapjack.Compiler.Backend.DataSem.Value)
      (xs stack : List Flapjack.Compiler.Backend.DataSem.Value) (ts : Nat),
      ∀ x, (ts ≤ x ∧ x < ts + xs.length) → allTimestamps refs (listToValue ts t xs :: stack) x := by
  intro refs t xs stack ts x mem
  exact ⟨listToValue ts t xs, .inr (by simp), valueTimestamps_listToValue t xs ts x (.inl mem)⟩

/-- HOL `v_all_vs_list_to_v1`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_all_vs_list_to_v1"]
theorem valueListValues_listToValue1 :
    ∀ (xs stack : List Flapjack.Compiler.Backend.DataSem.Value) (ts : Nat) (t : Flapjack.Compiler.Backend.DataSem.Value)
      (t1 a1 : Nat) (xs1 : List Flapjack.Compiler.Backend.DataSem.Value),
      t1 < ts ∧ .block t1 a1 xs1 ∈ valueListValues (listToValue ts t xs :: stack) →
        .block t1 a1 xs1 ∈ valueListValues (t :: (xs ++ stack)) := by
  rintro xs stack ts t t1 a1 xs1 ⟨lt, mem⟩
  rcases (mem_valueListValues_listToValue t _ xs ts stack).mp mem with ⟨j, jlt, eq⟩ | h
  · obtain ⟨x, hx⟩ := listToValue_drop_block t xs ts j jlt
    rw [hx] at eq
    obtain ⟨e, -, -⟩ := Value.block.inj eq
    omega
  · exact h

/-- HOL `blocks_unique_GT_ts`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_GT_ts"]
theorem blocksUnique_gt_ts (ts : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (t : Flapjack.Compiler.Backend.DataSem.Value) (xs stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (t' a1 : Nat) (xs1 : List Flapjack.Compiler.Backend.DataSem.Value) :
    blocksUnique ts (allValues refs (t :: (xs ++ stack))) ∧ t' ≥ ts ∧ xs1 ≠ [] →
      ¬ allValues refs (t :: (xs ++ stack)) (.block t' a1 xs1) := by
  rintro ⟨unique, ge, ne⟩ mem
  have := (unique t' a1 xs1 a1 xs1 ⟨mem, ne, mem, ne⟩).2.2
  omega

/-- HOL `Block_NOT_IN_all_vs`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "Block_NOT_IN_all_vs"]
theorem block_not_in_allValues :
    ∀ (xs : List Flapjack.Compiler.Backend.DataSem.Value) (t : Flapjack.Compiler.Backend.DataSem.Value)
      (t' a2 : Nat) (xs2 : List Flapjack.Compiler.Backend.DataSem.Value) (h : Flapjack.Compiler.Backend.DataSem.Value)
      (stack : List Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)),
      ¬ allValues refs (t :: h :: (xs ++ stack)) (.block t' a2 xs2) →
        ∀ m, m > 0 → .block t' a2 xs2 ∉ valueListValues [listToValue (t' + m) t xs] := by
  intro xs t t' a2 xs2 h stack refs notIn m pos mem
  rcases (mem_valueListValues_listToValue t _ xs (t' + m) []).mp mem with ⟨j, jlt, eq⟩ | inner
  · obtain ⟨x, hx⟩ := listToValue_drop_block t xs (t' + m) j jlt
    rw [hx] at eq
    obtain ⟨e, -, -⟩ := Value.block.inj eq
    omega
  · apply notIn
    simp only [allValues]
    refine .inr (.inr (.inr ?_))
    rw [mem_valueListValues_iff] at inner ⊢
    obtain ⟨v, vmem, inV⟩ := inner
    refine ⟨v, ?_, inV⟩
    simp only [List.append_nil, List.mem_cons, List.mem_append] at vmem ⊢
    tauto

/-- HOL `v_all_vs_list_to_v2`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_all_vs_list_to_v2"]
theorem valueListValues_listToValue2 :
    ∀ (xs : List Flapjack.Compiler.Backend.DataSem.Value) (t' a1 a2 : Nat)
      (xs1 xs2 : List Flapjack.Compiler.Backend.DataSem.Value) (ts : Nat) (t : Flapjack.Compiler.Backend.DataSem.Value)
      (stack : List Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)),
      .block t' a1 xs1 ∈ valueListValues (listToValue ts t xs :: stack) ∧ xs1 ≠ [] ∧
        .block t' a2 xs2 ∈ valueListValues (listToValue ts t xs :: stack) ∧ xs2 ≠ [] ∧
        ¬ allValues refs (t :: (xs ++ stack)) (.block t' a1 xs1) ∧
        ¬ allValues refs (t :: (xs ++ stack)) (.block t' a2 xs2) →
        a1 = a2 ∧ xs1 = xs2 ∧ t' < ts + xs.length := by
  rintro xs t' a1 a2 xs1 xs2 ts t stack refs ⟨m1, _, m2, _, n1, n2⟩
  have spineOf : ∀ a ys, .block t' a ys ∈ valueListValues (listToValue ts t xs :: stack) →
      ¬ allValues refs (t :: (xs ++ stack)) (.block t' a ys) →
      ∃ j, j < xs.length ∧ .block t' a ys = listToValue (ts + j) t (xs.drop j) := by
    intro a ys mem notIn
    rcases (mem_valueListValues_listToValue t _ xs ts stack).mp mem with h | h
    · exact h
    · exact absurd (.inr (.inr (.inr h))) notIn
  obtain ⟨j1, lt1, e1⟩ := spineOf a1 xs1 m1 n1
  obtain ⟨j2, lt2, e2⟩ := spineOf a2 xs2 m2 n2
  obtain ⟨x1, h1⟩ := listToValue_drop_block t xs ts j1 lt1
  obtain ⟨x2, h2⟩ := listToValue_drop_block t xs ts j2 lt2
  rw [h1] at e1
  rw [h2] at e2
  obtain ⟨s1, rfl, rfl⟩ := Value.block.inj e1
  obtain ⟨s2, rfl, rfl⟩ := Value.block.inj e2
  have : j1 = j2 := by omega
  subst this
  rw [h1] at h2
  obtain ⟨-, -, h⟩ := Value.block.inj h2
  obtain ⟨rfl, -⟩ := List.cons.inj h
  exact ⟨rfl, rfl, by omega⟩

/-- HOL `blocks_unique_cons_multi`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_cons_multi"]
theorem blocksUnique_consMulti (ts : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (t : Flapjack.Compiler.Backend.DataSem.Value) (xs stack : List Flapjack.Compiler.Backend.DataSem.Value) :
    blocksUnique ts (allValues refs (t :: (xs ++ stack))) →
      blocksUnique (ts + xs.length) (allValues refs (listToValue ts t xs :: stack)) := by
  intro unique stamp tag1 xs1 tag2 xs2 ⟨h1, ne1, h2, ne2⟩
  have old : ∀ tg ys, allValues refs (t :: (xs ++ stack)) (.block stamp tg ys) → ys ≠ [] → stamp < ts :=
    fun tg ys hs ne => (unique stamp tg ys tg ys ⟨hs, ne, hs, ne⟩).2.2
  have spine : ∀ tg ys, (∃ j, j < xs.length ∧ Value.block stamp tg ys = listToValue (ts + j) t (xs.drop j)) →
      ts ≤ stamp ∧ stamp < ts + xs.length := by
    rintro tg ys ⟨j, lt, eq⟩
    obtain ⟨x, hx⟩ := listToValue_drop_block t xs ts j lt
    rw [hx] at eq
    obtain ⟨rfl, -, -⟩ := Value.block.inj eq
    omega
  rcases (allValues_listToValue refs t xs ts stack _).mp h1 with s1 | o1 <;>
    rcases (allValues_listToValue refs t xs ts stack _).mp h2 with s2 | o2
  · have hi := (spine tag1 xs1 s1).2
    obtain ⟨j1, lt1, e1⟩ := s1
    obtain ⟨j2, lt2, e2⟩ := s2
    obtain ⟨x1, h1'⟩ := listToValue_drop_block t xs ts j1 lt1
    obtain ⟨x2, h2'⟩ := listToValue_drop_block t xs ts j2 lt2
    rw [h1'] at e1
    rw [h2'] at e2
    obtain ⟨s1, rfl, rfl⟩ := Value.block.inj e1
    obtain ⟨s2, rfl, rfl⟩ := Value.block.inj e2
    have : j1 = j2 := by omega
    subst this
    rw [h1'] at h2'
    obtain ⟨-, -, h⟩ := Value.block.inj h2'
    obtain ⟨rfl, -⟩ := List.cons.inj h
    exact ⟨rfl, rfl, hi⟩
  · have := (spine tag1 xs1 s1).1
    have := old tag2 xs2 o2 ne2
    omega
  · have := (spine tag2 xs2 s2).1
    have := old tag1 xs1 o1 ne1
    omega
  · obtain ⟨a, b, c⟩ := unique stamp tag1 xs1 tag2 xs2 ⟨o1, ne1, o2, ne2⟩
    exact ⟨a, b, by omega⟩


/-- Pairwise relation on matching suffixes. Flapjack proof infrastructure. -/
theorem forall₂_drop_cons {α β : Type} (R : α → β → Prop) :
    ∀ (j : Nat) (xs : List α) (rs : List β), List.Forall₂ R xs rs →
      ∀ x xr r rr, xs.drop j = x :: xr → rs.drop j = r :: rr → R x r ∧ List.Forall₂ R xr rr := by
  intro j
  induction j with
  | zero =>
    intro xs rs rel x xr r rr hx hr
    simp only [List.drop_zero] at hx hr
    subst hx hr
    cases rel with
    | cons h t => exact ⟨h, t⟩
  | succ j ih =>
    intro xs rs rel x xr r rr hx hr
    cases rel with
    | nil => simp at hx
    | cons _ t => exact ih _ _ t x xr r rr (by simpa using hx) (by simpa using hr)

/-- The second field of a cons-chain cell: the next cell, or the list tail
after the last element. Flapjack proof infrastructure. -/
def consNext {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (rt : HeapAddress (WordLocW width)) (p : Nat) : List (HeapAddress (WordLocW width)) → HeapAddress (WordLocW width)
  | [] => rt
  | _ :: _ => .pointer p (.word (ptrBits conf consTag 2))

/-- The cell at offset `3 * j` of a cons-block chain. Flapjack proof
infrastructure. -/
theorem heapLookup_listToBlockReps {width : Nat} [NeZero width] {β : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (rt : HeapAddress (WordLocW width)) :
    ∀ (rs : List (HeapAddress (WordLocW width))) (a j : Nat) (r : HeapAddress (WordLocW width))
      (rest : List (HeapAddress (WordLocW width))), rs.drop j = r :: rest →
      heapLookup (3 * j) (listToBlockReps conf rt a rs : List (HeapElement _ (HeapTag × List β))) =
        some (blockRep consTag [r, consNext conf rt (a + 3 * j + 3) rest]) := by
  intro rs
  induction rs with
  | nil => intro a j r rest h; simp at h
  | cons h l ih =>
    intro a j r rest hd
    cases j with
    | zero =>
      simp only [List.drop_zero, List.cons.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      cases l with
      | nil => simp [listToBlockReps_single, heapLookup, consNext]
      | cons h' l' => simp [listToBlockReps_cons, heapLookup, consNext]
    | succ j =>
      simp only [List.drop_succ_cons] at hd
      cases l with
      | nil => simp at hd
      | cons h' l' =>
        rw [listToBlockReps_cons]
        have step : heapLookup (3 * (j + 1)) (blockRep consTag [h, .pointer (a + 3) (.word (ptrBits conf consTag 2))] ::
            listToBlockReps conf rt (a + 3) (h' :: l') : List (HeapElement _ (HeapTag × List β))) =
            heapLookup (3 * j) (listToBlockReps conf rt (a + 3) (h' :: l')) := by
          simp [heapLookup, blockRep, elLength, show 3 * (j + 1) - 3 = 3 * j by omega]
        rw [step, ih (a + 3) j r rest hd]
        cases rest <;> simp [consNext, show a + 3 + 3 * j + 3 = a + 3 * (j + 1) + 3 by omega]

/-- Each spine block of an allocated list satisfies the value invariant in the
final heap. Flapjack proof infrastructure for `v_inv_list_to_v_lem`. -/
theorem valueInv_listToValue_spine {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (f tf' : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) (t : Value)
    (rt : HeapAddress (WordLocW width)) (xs : List Value) (rs : List (HeapAddress (WordLocW width)))
    (a ts : Nat) (rel : List.Forall₂ (fun v x => valueInv conf v refs (x, f, tf', heap)) xs rs)
    (tail : valueInv conf t refs (rt, f, tf', heap))
    (stamps : ∀ j, j < xs.length → tf'.lookup (ts + j) = some (a + 3 * j))
    (cells : ∀ j r rest, rs.drop j = r :: rest →
      heapLookup (a + 3 * j) heap = some (blockRep consTag [r, consNext conf rt (a + 3 * j + 3) rest])) :
    ∀ k j, j + k = xs.length → 0 < k →
      valueInv conf (listToValue (ts + j) t (xs.drop j)) refs
        (.pointer (a + 3 * j) (.word (ptrBits conf consTag 2)), f, tf', heap) := by
  have lens := rel.length_eq
  intro k
  induction k with
  | zero => intro j _ h; omega
  | succ k ih =>
    intro j sum _
    obtain ⟨x, xr, hx⟩ : ∃ x xr, xs.drop j = x :: xr := by
      cases h : xs.drop j with
      | nil => simp at h; omega
      | cons x xr => exact ⟨x, xr, rfl⟩
    obtain ⟨r, rr, hr⟩ : ∃ r rr, rs.drop j = r :: rr := by
      cases h : rs.drop j with
      | nil => simp at h; omega
      | cons r rr => exact ⟨r, rr, rfl⟩
    obtain ⟨head, restRel⟩ := forall₂_drop_cons _ j xs rs rel x xr r rr hx hr
    rw [hx]
    show valueInv conf (.block (ts + j) consTag [x, listToValue (ts + j + 1) t xr]) refs _
    rw [valueInv_nonemptyBlock conf (ts + j) consTag _ refs _ f tf' heap (by simp)]
    refine ⟨a + 3 * j, [r, consNext conf rt (a + 3 * j + 3) rr], ?_,
      stamps j (by omega), rfl, cells j r rr hr⟩
    refine .cons head (.cons ?_ .nil)
    cases rr with
    | nil =>
      cases xr with
      | nil => simpa [consNext, listToValue] using tail
      | cons _ _ => cases restRel
    | cons r' rr' =>
      have more : xs.drop (j + 1) = xr := by rw [← List.drop_drop, hx]; rfl
      have kpos : 0 < k := by
        cases xr with
        | nil => cases restRel
        | cons _ _ =>
          have := congrArg List.length more
          simp at this; omega
      have := ih (j + 1) (by omega) kpos
      rw [more] at this
      simpa [consNext, Nat.add_assoc, Nat.mul_succ] using this

/-- HOL `v_inv_list_to_v_lem`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_list_to_v_lem"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_listToValue_lem {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat) :
    ∀ (rs : List (HeapAddress (WordLocW width))) (xs : List Flapjack.Compiler.Backend.DataSem.Value)
      (t : Flapjack.Compiler.Backend.DataSem.Value) (rt : HeapAddress (WordLocW width))
      (ha hb : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (sp ts : Nat),
      let hm : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) :=
        listToBlockReps conf rt (heapLength ha) rs
      rs ≠ [] ∧ valueInv conf t refs (rt, f, tf, ha ++ heapExpand sp ++ hb) ∧
        List.Forall₂ (fun v x => valueInv conf v refs (x, f, tf, ha ++ heapExpand sp ++ hb)) xs rs ∧
        heapLength hm ≤ sp ∧ (∀ t, tf.lookup t ≠ none → t < ts) →
      valueInv conf (listToValue ts t xs) refs
        (.pointer (heapLength ha) (.word (ptrBits conf consTag 2 : BitVec width)), f,
          bindEach tf ts (heapLength ha) 3 xs.length, ha ++ hm ++ heapExpand (sp - heapLength hm) ++ hb) := by
  intro rs xs t rt ha hb sp ts hm ⟨ne, tailInv, rel, fits, bound⟩
  have lens := rel.length_eq
  have hmLen : heapLength hm = 3 * rs.length :=
    listToBlockReps_heapLength conf rt rs (heapLength ha) ne
  have pos : 0 < heapLength hm := by
    rw [hmLen]; cases rs with
    | nil => exact absurd rfl ne
    | cons _ _ => simp
  let heap := ha ++ hm ++ heapExpand (sp - heapLength hm) ++ hb
  let tf' := bindEach tf ts (heapLength ha) 3 xs.length
  have transfer : ∀ v x, valueInv conf v refs (x, f, tf, ha ++ heapExpand sp ++ hb) →
      valueInv conf v refs (x, f, tf', heap) := by
    intro v x inv ck
    have moved := valueInv_lemma conf v refs x f tf hm ha hb sp ⟨pos, fits, inv⟩
    exact valueInv_submap_lemma conf f tf' heap ck v refs x f tf _ moved
      ⟨fun _ _ h => h, bindEach_submap xs.length tf ts (heapLength ha) 3 bound, fun _ _ => rfl⟩
  have spine := valueInv_listToValue_spine conf refs f tf' heap t rt xs rs (heapLength ha) ts
    (rel.imp (fun v x h => transfer v x h)) (transfer t rt tailInv)
    (by
      intro j lt
      show (bindEach tf ts (heapLength ha) 3 xs.length).lookup (ts + j) = _
      rw [lookup_bindEach_closed, if_pos (by omega)]
      simp)
    (by
      intro j r rest hd
      have jlt : 3 * j < heapLength hm := by
        have : j < rs.length := by
          have := congrArg List.length hd
          simp at this; omega
        omega
      show heapLookup (heapLength ha + 3 * j) (ha ++ hm ++ heapExpand (sp - heapLength hm) ++ hb) = _
      rw [List.append_assoc, List.append_assoc, heapLookup_append1 ha _ _ (by omega),
        show heapLength ha + 3 * j - heapLength ha = 3 * j by omega,
        heapLookup_append2 hm _ _ jlt]
      exact heapLookup_listToBlockReps conf rt rs (heapLength ha) j r rest hd)
    xs.length 0 (by simp) (by rw [lens]; cases rs with
      | nil => exact absurd rfl ne
      | cons _ _ => simp)
  simpa [heap, tf'] using spine

/-- HOL `v_inv_list_to_v` (`v_inv_list_to_v_lem` with its `let` unfolded). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_list_to_v"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_listToValue {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat) :
    ∀ (rs : List (HeapAddress (WordLocW width))) (xs : List Flapjack.Compiler.Backend.DataSem.Value)
      (t : Flapjack.Compiler.Backend.DataSem.Value) (rt : HeapAddress (WordLocW width))
      (ha hb : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (sp ts : Nat),
      rs ≠ [] ∧ valueInv conf t refs (rt, f, tf, ha ++ heapExpand sp ++ hb) ∧
        List.Forall₂ (fun v x => valueInv conf v refs (x, f, tf, ha ++ heapExpand sp ++ hb)) xs rs ∧
        heapLength (listToBlockReps conf rt (heapLength ha) rs :
          List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) ≤ sp ∧
        (∀ t, tf.lookup t ≠ none → t < ts) →
      valueInv conf (listToValue ts t xs) refs
        (.pointer (heapLength ha) (.word (ptrBits conf consTag 2 : BitVec width)), f,
          bindEach tf ts (heapLength ha) 3 xs.length,
          ha ++ listToBlockReps conf rt (heapLength ha) rs ++
            heapExpand (sp - heapLength (listToBlockReps conf rt (heapLength ha) rs :
              List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))) ++ hb) :=
  valueInv_listToValue_lem conf refs f tf
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

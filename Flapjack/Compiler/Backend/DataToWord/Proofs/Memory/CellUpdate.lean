module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.RefUpdate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.EvaluatedThunk
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.GcRefinement
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.MutBlockInsert

@[expose] public section

/-!
# Thunk-block heap updates and heap-store framing lemmas

Counterparts of `heap_store_ThunkBlock_thm`, `heap_lookup_ThunkBlock_lemma`,
`heap_store_ThunkBlock`, `INJ_NEQ`, `heap_lookup_heap_split`,
`heap_store_heap_lookup`, `data_up_to_alt`, `data_up_to_heap_store`,
`blocks_unique_update_thunk`, `thunk_deref_def`, `heap_store_BlockRep_thm`,
`heap_lookup_BlockRep_lemma`, `heap_store_BlockRep`, `v_inv_MutBlock_hole_lemma`,
`v_inv_MutBlock_hole`, `blocks_unique_update_mutblock`, `ref_edge_MutBlock_UPDATE`
and `reachable_refs_MutBlock_UPDATE` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`. HOL
`INJ (FAPPLY f) (FDOM f) s` is the HOL-shaped `mapInjInto f s`, `x ∈ FDOM f` is
`f.lookup x ≠ none` and `f ' x` is `holFapply f x`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- HOL `heap_store_ThunkBlock_thm`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_store_ThunkBlock_thm"]
theorem heapStore_thunkBlock {α β : Type} (ev1 ev2 : AstHOL.ThunkMode) (v1 v2 : HeapAddress α)
    (hb : List (HeapElement α (HeapTag × List β))) :
    ∀ ha : List (HeapElement α (HeapTag × List β)),
      heapStore (heapLength ha) [thunkBlock ev1 v1] (ha ++ thunkBlock ev2 v2 :: hb) =
        (ha ++ thunkBlock ev1 v1 :: hb, true) := by
  intro ha
  rw [heapStore_atPrefix]
  simp [heapLength, thunkBlock, elLength]

/-- HOL `heap_lookup_ThunkBlock_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_lookup_ThunkBlock_lemma"]
theorem heapLookup_thunkBlock_lemma {α β : Type} (n : Nat) (ha hb : List (HeapElement α (HeapTag × List β)))
    (ev : AstHOL.ThunkMode) (v : HeapAddress α) (x : HeapElement α (HeapTag × List β)) :
    (heapLookup n (ha ++ thunkBlock ev v :: hb) = some x) ↔
      if n < heapLength ha then heapLookup n ha = some x
      else if n = heapLength ha then x = thunkBlock ev v
      else if heapLength ha + 2 ≤ n then heapLookup (n - heapLength ha - 2) hb = some x
      else False := by
  rw [heapLookup_append]
  by_cases lt : n < heapLength ha
  · simp [lt]
  · simp only [lt, if_false]
    by_cases eq : n = heapLength ha
    · subst eq
      simp [heapLookup, eq_comm]
    · have pos : n - heapLength ha ≠ 0 := by omega
      simp only [eq, if_false, heapLookup, pos, thunkBlock, elLength]
      by_cases le : heapLength ha + 2 ≤ n
      · have notLt : ¬ n - heapLength ha < 1 + 1 := by omega
        simp only [notLt, if_false, le, if_true]
      · have isLt : n - heapLength ha < 1 + 1 := by omega
        simp [isLt, le]

/-- HOL `heap_store_ThunkBlock`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_store_ThunkBlock"]
theorem heapStore_thunkBlock_source {α β : Type} (n : Nat) (heap : List (HeapElement α (HeapTag × List β)))
    (y h : HeapAddress α) (ev : AstHOL.ThunkMode) :
    heapLookup n heap = some (thunkBlock .notEvaluated y) →
      ∃ heap2, heapStore n [thunkBlock ev h] heap = (heap2, true) ∧
        heapLookup n heap2 = some (thunkBlock ev h) ∧ heapLength heap2 = heapLength heap ∧
        heap2.filter isForwardPointer = heap.filter isForwardPointer ∧
        (∀ xs l d, HeapElement.dataElement xs l d ∈ heap2 →
          HeapElement.dataElement xs l d = thunkBlock ev h ∨ HeapElement.dataElement xs l d ∈ heap) ∧
        (∀ a, isSomeDataElement (heapLookup a heap2) ↔ isSomeDataElement (heapLookup a heap)) ∧
        ∀ m x, m ≠ n ∧ heapLookup m heap = some x → heapLookup m heap2 = some x := by
  intro found
  obtain ⟨pre, suf, rfl, rfl⟩ := heapLookup_split heap n _ found
  have elLen : elLength (thunkBlock ev h : HeapElement α (HeapTag × List β)) =
      elLength (thunkBlock .notEvaluated y : HeapElement α (HeapTag × List β)) := by
    simp [thunkBlock, elLength]
  have lookup : ∀ a, heapLookup a (pre ++ thunkBlock ev h :: suf) =
      if a = heapLength pre then some (thunkBlock ev h)
      else heapLookup a (pre ++ thunkBlock .notEvaluated y :: suf) := by
    intro a
    rw [heapLookup_append, heapLookup_append]
    by_cases lt : a < heapLength pre
    · simp [lt, show a ≠ heapLength pre by omega]
    · simp only [lt, if_false]
      rw [heapLookup_cons_sameLength _ _ suf elLen]
      by_cases eq : a = heapLength pre
      · simp [eq]
      · simp [eq, show a - heapLength pre ≠ 0 by omega]
  refine ⟨pre ++ thunkBlock ev h :: suf, heapStore_thunkBlock ev .notEvaluated h y suf pre, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact heapLookup_prefix pre suf _
  · simp [heapLength, elLength, thunkBlock]
  · simp [List.filter_append, isForwardPointer, thunkBlock]
  · intro xs l d member
    simp only [List.mem_append, List.mem_cons] at member
    rcases member with member | eq | member
    · exact Or.inr (by simp [member])
    · exact Or.inl eq
    · exact Or.inr (by simp [member])
  · intro a
    rw [lookup]
    by_cases eq : a = heapLength pre
    · subst eq
      rw [heapLookup_prefix]
      simp [isSomeDataElement, thunkBlock]
    · simp [eq]
  · rintro m x ⟨ne, hm⟩
    rw [lookup, if_neg ne]
    exact hm

/-- HOL `INJ_NEQ`. The finite map has polymorphic keys and the heap its own
carriers, as inferred by HOL; `INJ (FAPPLY f) (FDOM f) s` is written out as
its two defining conjuncts. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "INJ_NEQ"
  (fmap_as_finite_support_relation := [f])]
theorem inj_neq {α β γ : Type} (f : HolFiniteMapExact α Nat) (heap : List (HeapElement β γ)) (n ptr : α) :
    ((∀ x, f.lookup x ≠ none → isSomeDataElement (heapLookup (holFapply f x) heap)) ∧
        (∀ x y, f.lookup x ≠ none ∧ f.lookup y ≠ none → holFapply f x = holFapply f y → x = y)) ∧
        f.lookup n ≠ none ∧ f.lookup ptr ≠ none ∧ n ≠ ptr →
      holFapply f n ≠ holFapply f ptr := by
  rintro ⟨⟨-, injective⟩, hn, hp, ne⟩ eq
  exact ne (injective n ptr ⟨hn, hp⟩ eq)

/-- HOL `heap_lookup_heap_split`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_lookup_heap_split"]
theorem heapLookup_heapSplit {α β : Type} :
    ∀ (heap : List (HeapElement α β)) (a b : Nat) (h1 h2 : List (HeapElement α β)) (x : HeapElement α β),
      heapSplit a heap = some (h1, h2) ∧ heapLookup b heap = some x →
      if b < a then x ∈ h1 else x ∈ h2 := by
  rintro heap a b h1 h2 x ⟨split, found⟩
  obtain ⟨len, -, rfl⟩ := heapSplit_heapLength heap h1 h2 a split
  rw [heapLookup_append] at found
  subst len
  by_cases lt : b < heapLength h1
  · rw [if_pos lt] at found ⊢
    exact heapLookup_mem _ _ _ found
  · rw [if_neg lt] at found ⊢
    exact heapLookup_mem _ _ _ found

/-- HOL `heap_store_heap_lookup`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_store_heap_lookup"]
theorem heapStore_heapLookup {α β : Type} :
    ∀ (heap heap2 : List (HeapElement α β)) (a : Nat) (x : List (HeapElement α β)) (n : Nat),
      heapStore a x heap = (heap2, true) ∧ n < a → heapLookup n heap = heapLookup n heap2 := by
  intro heap
  induction heap with
  | nil => rintro heap2 a x n ⟨h, _⟩; simp [heapStore] at h
  | cons head tail ih =>
    rintro heap2 a x n ⟨store, lt⟩
    have a0 : a ≠ 0 := by omega
    simp only [heapStore, a0, if_false] at store
    by_cases inside : a < elLength head
    · simp [inside] at store
    · simp only [inside, if_false] at store
      generalize rest : heapStore (a - elLength head) x tail = result at store
      rcases result with ⟨rest', ok⟩
      simp only [Prod.mk.injEq] at store
      obtain ⟨rfl, rfl⟩ := store
      by_cases z : n = 0
      · simp [heapLookup, z]
      · by_cases nIn : n < elLength head
        · simp [heapLookup, z, nIn]
        · simp only [heapLookup, z, nIn, if_false]
          exact ih rest' (a - elLength head) x (n - elLength head) ⟨rest, by omega⟩

open Classical in
/-- HOL `data_up_to_alt`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_up_to_alt"]
theorem dataUpTo_alt {α β γ δ : Type} (n : Nat) (x : HeapElement γ δ) (xs : List (HeapElement γ δ)) :
    (dataUpTo n ([] : List (HeapElement α β)) ↔ n = 0) ∧
      (dataUpTo n (x :: xs) ↔
        if n = 0 then True
        else if n < elLength x ∨ ¬ isDataElement x then False
        else dataUpTo (n - elLength x) xs) := by
  constructor
  · constructor
    · rintro ⟨first, second, split, _⟩
      by_contra ne
      simp [heapSplit, ne] at split
    · rintro rfl
      exact ⟨[], [], by simp [heapSplit], by simp⟩
  · by_cases z : n = 0
    · subst z
      simp only [if_true, iff_true]
      exact ⟨[], x :: xs, by simp [heapSplit], by simp⟩
    · simp only [z, if_false]
      by_cases bad : n < elLength x ∨ ¬ isDataElement x
      · simp only [bad, if_true, iff_false]
        rintro ⟨first, second, split, data⟩
        rcases bad with lt | notData
        · simp [heapSplit, z, lt] at split
        · cases rest : heapSplit (n - elLength x) xs with
          | none => simp [heapSplit, z, rest] at split
          | some p =>
            have lt : ¬ n < elLength x := by
              intro lt; simp [heapSplit, z, lt] at split
            simp [heapSplit, z, lt, rest] at split
            obtain ⟨rfl, -⟩ := split
            exact notData (data x (by simp))
      · simp only [bad, if_false]
        rw [not_or, not_not] at bad
        obtain ⟨notLt, data⟩ := bad
        constructor
        · rintro ⟨first, second, split, allData⟩
          cases rest : heapSplit (n - elLength x) xs with
          | none => simp [heapSplit, z, notLt, rest] at split
          | some p =>
            rcases p with ⟨a, b⟩
            simp [heapSplit, z, notLt, rest] at split
            obtain ⟨rfl, rfl⟩ := split
            exact ⟨a, b, rest, fun e m => allData e (by simp [m])⟩
        · rintro ⟨first, second, split, allData⟩
          refine ⟨x :: first, second, by simp [heapSplit, z, notLt, split], ?_⟩
          intro e m
          rcases List.mem_cons.mp m with rfl | m
          · exact data
          · exact allData e m

open Classical in
/-- HOL `data_up_to_heap_store`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_up_to_heap_store"]
theorem dataUpTo_heapStore {α β : Type} :
    ∀ (heap : List (HeapElement α β)) (a b : Nat) (heap2 : List (HeapElement α β)) (y : HeapElement α β),
      dataUpTo a heap ∧ heapStore b [y] heap = (heap2, true) ∧ isDataElement y → dataUpTo a heap2 := by
  intro heap
  induction heap with
  | nil => rintro a b heap2 y ⟨_, store, _⟩; simp [heapStore] at store
  | cons head tail ih =>
    rintro a b heap2 y ⟨up, store, data⟩
    by_cases b0 : b = 0
    · subst b0
      simp only [heapStore, if_true, Prod.mk.injEq] at store
      obtain ⟨rfl, len⟩ := store
      simp only [decide_eq_true_eq] at len
      have len' : elLength y = elLength head := by simp [heapLength] at len; omega
      rw [(dataUpTo_alt (α := α) (β := β) a head tail).2] at up
      rw [List.singleton_append, (dataUpTo_alt (α := α) (β := β) a y tail).2, len']
      by_cases z : a = 0
      · simp [z]
      · simp only [z, if_false] at up ⊢
        by_cases bad : a < elLength head ∨ ¬ isDataElement head
        · simp [bad] at up
        · simp only [bad, if_false] at up
          have : ¬ (a < elLength head ∨ ¬ isDataElement y) := by
            rw [not_or, not_not]; exact ⟨(not_or.mp bad).1, data⟩
          simp only [this, if_false]
          exact up
    · simp only [heapStore, b0, if_false] at store
      by_cases inside : b < elLength head
      · simp [inside] at store
      · simp only [inside, if_false] at store
        generalize rest : heapStore (b - elLength head) [y] tail = result at store
        rcases result with ⟨rest', ok⟩
        simp only [Prod.mk.injEq] at store
        obtain ⟨rfl, rfl⟩ := store
        rw [(dataUpTo_alt (α := α) (β := β) a head tail).2] at up
        rw [(dataUpTo_alt (α := α) (β := β) a head rest').2]
        by_cases z : a = 0
        · simp [z]
        · simp only [z, if_false] at up ⊢
          by_cases bad : a < elLength head ∨ ¬ isDataElement head
          · simp [bad] at up
          · simp only [bad, if_false] at up ⊢
            exact ih (a - elLength head) (b - elLength head) rest' y ⟨up, rest, data⟩

/-- HOL `blocks_unique_update_thunk`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_update_thunk"]
theorem blocksUnique_updateThunk (ts ptr : Nat) (ev : AstHOL.ThunkMode)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (h : Flapjack.Compiler.Backend.DataSem.Value) (stack : List Flapjack.Compiler.Backend.DataSem.Value) :
    blocksUnique ts (allValues refs (h :: .refPtr false ptr :: stack)) →
      blocksUnique ts (allValues (sptInsert ptr (.thunk ev h) refs) (h :: .refPtr false ptr :: stack)) := by
  intro unique
  have sub : ∀ s t xs, allValues (sptInsert ptr (.thunk ev h) refs) (h :: .refPtr false ptr :: stack)
      (.block s t xs) → allValues refs (h :: .refPtr false ptr :: stack) (.block s t xs) := by
    intro s t xs hv
    rcases hv with ⟨i, vs, found, m⟩ | ⟨i, mode, ch, found, m⟩ | ⟨i, t', fin, l', c', r', found, m⟩ | m
    · by_cases eq : i = ptr
      · subst i; simp [sptLookup_sptInsert_same] at found
      · rw [sptLookup_sptInsert_ne ptr i _ refs eq] at found
        exact Or.inl ⟨i, vs, found, m⟩
    · by_cases eq : i = ptr
      · subst i
        simp only [sptLookup_sptInsert_same, Option.some.injEq, BvlSem.Ref.thunk.injEq] at found
        obtain ⟨-, rfl⟩ := found
        exact Or.inr (Or.inr (Or.inr (mem_valueListValues_extend_tl _ _ _ m)))
      · rw [sptLookup_sptInsert_ne ptr i _ refs eq] at found
        exact Or.inr (Or.inl ⟨i, mode, ch, found, m⟩)
    · by_cases eq : i = ptr
      · subst i; simp [sptLookup_sptInsert_same] at found
      · rw [sptLookup_sptInsert_ne ptr i _ refs eq] at found
        exact Or.inr (Or.inr (Or.inl ⟨i, t', fin, l', c', r', found, m⟩))
    · exact Or.inr (Or.inr (Or.inr m))
  intro stamp tag1 xs1 tag2 xs2 ⟨h1, n1, h2, n2⟩
  exact unique stamp tag1 xs1 tag2 xs2 ⟨sub _ _ _ h1, n1, sub _ _ _ h2, n2⟩

/-- HOL `thunk_deref_def`: the addresses stored in an unevaluated thunk block. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "thunk_deref_def"]
def thunkDeref {α β : Type} (a : Nat) (heap : List (HeapElement α (HeapTag × List β))) :
    Option (List (HeapAddress α)) :=
  match heapLookup a heap with
  | some (.dataElement xs _ (.thunkTag .notEvaluated, [])) => some xs
  | _ => none

/-- HOL `heap_store_BlockRep_thm`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_store_BlockRep_thm"]
theorem heapStore_blockRep {α β : Type} (tag : Nat) (x y : List (HeapAddress α))
    (hb : List (HeapElement α (HeapTag × List β))) :
    ∀ ha : List (HeapElement α (HeapTag × List β)), x.length = y.length →
      heapStore (heapLength ha) [blockRep tag x] (ha ++ blockRep tag y :: hb) =
        (ha ++ blockRep tag x :: hb, true) := by
  intro ha len
  rw [heapStore_atPrefix]
  simp [heapLength, blockRep, elLength, len]

/-- HOL `heap_lookup_BlockRep_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_lookup_BlockRep_lemma"]
theorem heapLookup_blockRep_lemma {α β : Type} (n tag : Nat) (ha hb : List (HeapElement α (HeapTag × List β)))
    (y : List (HeapAddress α)) (x : HeapElement α (HeapTag × List β)) :
    (heapLookup n (ha ++ blockRep tag y :: hb) = some x) ↔
      if n < heapLength ha then heapLookup n ha = some x
      else if n = heapLength ha then x = blockRep tag y
      else if heapLength ha + (y.length + 1) ≤ n then
        heapLookup (n - heapLength ha - (y.length + 1)) hb = some x
      else False := by
  rw [heapLookup_append]
  by_cases lt : n < heapLength ha
  · simp [lt]
  · simp only [lt, if_false]
    by_cases eq : n = heapLength ha
    · subst eq
      simp [heapLookup, eq_comm]
    · have pos : n - heapLength ha ≠ 0 := by omega
      simp only [eq, if_false, heapLookup, pos, blockRep, elLength]
      by_cases le : heapLength ha + (y.length + 1) ≤ n
      · have notLt : ¬ n - heapLength ha < y.length + 1 := by omega
        simp only [notLt, if_false, le, if_true]
      · have isLt : n - heapLength ha < y.length + 1 := by omega
        simp [isLt, le]

/-- HOL `heap_store_BlockRep`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_store_BlockRep"]
theorem heapStore_blockRep_source {α β : Type} (y h : List (HeapAddress α)) (n tag : Nat)
    (heap : List (HeapElement α (HeapTag × List β))) :
    y.length = h.length ∧ heapLookup n heap = some (blockRep tag y) →
      ∃ heap2, heapStore n [blockRep tag h] heap = (heap2, true) ∧
        heapLookup n heap2 = some (blockRep tag h) ∧ heapLength heap2 = heapLength heap ∧
        heap2.filter isForwardPointer = heap.filter isForwardPointer ∧
        (∀ xs l d, HeapElement.dataElement xs l d ∈ heap2 →
          HeapElement.dataElement xs l d = blockRep tag h ∨ HeapElement.dataElement xs l d ∈ heap) ∧
        (∀ a, isSomeDataElement (heapLookup a heap2) ↔ isSomeDataElement (heapLookup a heap)) ∧
        ∀ m x, m ≠ n ∧ heapLookup m heap = some x → heapLookup m heap2 = some x := by
  rintro ⟨len, found⟩
  obtain ⟨pre, suf, rfl, rfl⟩ := heapLookup_split heap n _ found
  have elLen : elLength (blockRep tag h : HeapElement α (HeapTag × List β)) =
      elLength (blockRep tag y : HeapElement α (HeapTag × List β)) := by
    simp [blockRep, elLength, len]
  have lookup : ∀ a, heapLookup a (pre ++ blockRep tag h :: suf) =
      if a = heapLength pre then some (blockRep tag h)
      else heapLookup a (pre ++ blockRep tag y :: suf) := by
    intro a
    rw [heapLookup_append, heapLookup_append]
    by_cases lt : a < heapLength pre
    · simp [lt, show a ≠ heapLength pre by omega]
    · simp only [lt, if_false]
      rw [heapLookup_cons_sameLength _ _ suf elLen]
      by_cases eq : a = heapLength pre
      · simp [eq]
      · simp [eq, show a - heapLength pre ≠ 0 by omega]
  refine ⟨pre ++ blockRep tag h :: suf, heapStore_blockRep tag h y suf pre len.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact heapLookup_prefix pre suf _
  · simp [heapLength, elLength, blockRep, len]
  · simp [List.filter_append, isForwardPointer, blockRep]
  · intro xs l d member
    simp only [List.mem_append, List.mem_cons] at member
    rcases member with member | eq | member
    · exact Or.inr (by simp [member])
    · exact Or.inl eq
    · exact Or.inr (by simp [member])
  · intro a
    rw [lookup]
    by_cases eq : a = heapLength pre
    · subst eq
      rw [heapLookup_prefix]
      simp [isSomeDataElement, blockRep]
    · simp [eq]
  · rintro m x ⟨ne, hm⟩
    rw [lookup, if_neg ne]
    exact hm

/-- HOL `v_inv_MutBlock_hole_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_MutBlock_hole_lemma"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_mutBlockHole_lemma {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ptr tag : Nat) (fin1 fin2 : Bool)
    (ll : List Flapjack.Compiler.Backend.DataSem.Value) (cv1 cv2 : Flapjack.Compiler.Backend.DataSem.Value)
    (rr : List Flapjack.Compiler.Backend.DataSem.Value) :
    ∀ (ck : Nat) (v1 : Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (y : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
      (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))),
      valueInv conf v1 refs (y, f, tf, heap) ∧ sptLookup ptr refs = some (.mutBlock tag fin1 ll cv1 rr) →
      ClockValueInv ck conf v1 (sptInsert ptr (.mutBlock tag fin2 ll cv2 rr) refs) (y, f, tf, heap) := by
  rintro ck v1 refs y f tf heap ⟨inv, old⟩
  apply clockValueInv_refsTransfer ck conf refs _ f
  · intro n _
    by_cases eq : n = ptr
    · subst n; simp [sptLookup_sptInsert_same, old, refPtrAnnot]
    · rw [sptLookup_sptInsert_ne ptr n _ refs eq]
  · intro n mode body found
    have ne : n ≠ ptr := by rintro rfl; simp [old] at found
    rw [sptLookup_sptInsert_ne ptr n _ refs ne]; exact found
  · intro n _ notThunk mode body
    by_cases eq : n = ptr
    · subst n; simp [sptLookup_sptInsert_same]
    · rw [sptLookup_sptInsert_ne ptr n _ refs eq]; exact notThunk mode body
  · intro n _ tag' fin' left body right lookup
    by_cases eq : n = ptr
    · subst n
      simp only [sptLookup_sptInsert_same, Option.some.injEq, BvlSem.Ref.mutBlock.injEq] at lookup
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := lookup
      exact ⟨fin1, cv1, old⟩
    · rw [sptLookup_sptInsert_ne ptr n _ refs eq] at lookup; exact ⟨fin', body, lookup⟩
  · intro value notThunk
    cases value with
    | refPtr bit index =>
      by_cases eq : index = ptr
      · subst index; simp [destThunk, sptLookup_sptInsert_same]
      · simpa [destThunk, sptLookup_sptInsert_ne ptr index _ refs eq] using notThunk
    | number _ | block _ _ _ | codePtr _ | word64 _ => simp [destThunk]
  · exact inv ck

/-- HOL `v_inv_MutBlock_hole`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_MutBlock_hole"
  (fmap_as_finite_support_relation := [ff, tff]) (words_as_type_indexed_bitvec)]
theorem valueInv_mutBlockHole {width : Nat} [NeZero width] :
    ∀ (cnf : Flapjack.Compiler.Backend.DataToWord.Config) (vv : Flapjack.Compiler.Backend.DataSem.Value)
      (rfs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (yy : HeapAddress (WordLocW width))
      (ff : HolFiniteMapExact Nat Nat) (tff : HolFiniteMapExact Nat Nat)
      (hp : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (pp tg : Nat)
      (b1 b2 : Bool) (l1 : List Flapjack.Compiler.Backend.DataSem.Value)
      (c1 c2 : Flapjack.Compiler.Backend.DataSem.Value) (r1 : List Flapjack.Compiler.Backend.DataSem.Value),
      valueInv cnf vv rfs (yy, ff, tff, hp) ∧ sptLookup pp rfs = some (.mutBlock tg b1 l1 c1 r1) →
      valueInv cnf vv (sptInsert pp (.mutBlock tg b2 l1 c2 r1) rfs) (yy, ff, tff, hp) := by
  intro cnf vv rfs yy ff tff hp pp tg b1 b2 l1 c1 c2 r1 h ck
  exact valueInv_mutBlockHole_lemma cnf pp tg b1 b2 l1 c1 c2 r1 ck vv rfs yy ff tff hp h

/-- HOL `blocks_unique_update_mutblock`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_update_mutblock"]
theorem blocksUnique_updateMutBlock (ts ptr tag : Nat) (fin : Bool)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (l : List Flapjack.Compiler.Backend.DataSem.Value) (cv h : Flapjack.Compiler.Backend.DataSem.Value)
    (r stack : List Flapjack.Compiler.Backend.DataSem.Value) :
    sptLookup ptr refs = some (.mutBlock tag fin l cv r) ∧
        blocksUnique ts (allValues refs (h :: .refPtr false ptr :: stack)) →
      blocksUnique ts (allValues (sptInsert ptr (.mutBlock tag fin l h r) refs) (h :: .refPtr false ptr :: stack)) := by
  rintro ⟨old, unique⟩
  have sub : ∀ s t xs, allValues (sptInsert ptr (.mutBlock tag fin l h r) refs) (h :: .refPtr false ptr :: stack)
      (.block s t xs) → allValues refs (h :: .refPtr false ptr :: stack) (.block s t xs) := by
    intro s t xs hv
    rcases hv with ⟨i, vs, found, m⟩ | ⟨i, mode, ch, found, m⟩ | ⟨i, t', fin', l', c', r', found, m⟩ | m
    · by_cases eq : i = ptr
      · subst i; simp [sptLookup_sptInsert_same] at found
      · rw [sptLookup_sptInsert_ne ptr i _ refs eq] at found
        exact Or.inl ⟨i, vs, found, m⟩
    · by_cases eq : i = ptr
      · subst i; simp [sptLookup_sptInsert_same] at found
      · rw [sptLookup_sptInsert_ne ptr i _ refs eq] at found
        exact Or.inr (Or.inl ⟨i, mode, ch, found, m⟩)
    · by_cases eq : i = ptr
      · subst i
        simp only [sptLookup_sptInsert_same, Option.some.injEq, BvlSem.Ref.mutBlock.injEq] at found
        obtain ⟨-, -, rfl, rfl, rfl⟩ := found
        rw [valueListValues_append, valueListValues_append, List.mem_append, List.mem_append] at m
        rcases m with (m | m) | m
        · refine Or.inr (Or.inr (Or.inl ⟨ptr, tag, fin, l, cv, r, old, ?_⟩))
          rw [valueListValues_append, valueListValues_append]; simp [m]
        · exact Or.inr (Or.inr (Or.inr (mem_valueListValues_extend_tl _ _ _ m)))
        · refine Or.inr (Or.inr (Or.inl ⟨ptr, tag, fin, l, cv, r, old, ?_⟩))
          rw [valueListValues_append]; simp [m]
      · rw [sptLookup_sptInsert_ne ptr i _ refs eq] at found
        exact Or.inr (Or.inr (Or.inl ⟨i, t', fin', l', c', r', found, m⟩))
    · exact Or.inr (Or.inr (Or.inr m))
  intro stamp tag1 xs1 tag2 xs2 ⟨h1, n1, h2, n2⟩
  exact unique stamp tag1 xs1 tag2 xs2 ⟨sub _ _ _ h1, n1, sub _ _ _ h2, n2⟩

/-- HOL `ref_edge_MutBlock_UPDATE`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "ref_edge_MutBlock_UPDATE"]
theorem refEdge_mutBlock_update (ptr tg : Nat) (fin : Bool) (ll : List Flapjack.Compiler.Backend.DataSem.Value)
    (cc h : Flapjack.Compiler.Backend.DataSem.Value) (rr : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (r1 z : Nat) :
    sptLookup ptr refs = some (.mutBlock tg fin ll cc rr) ∧
        refEdge (sptInsert ptr (.mutBlock tg fin ll h rr) refs) r1 z ∧ z ∉ getRefs h →
      refEdge refs r1 z := by
  rintro ⟨old, edge, notH⟩
  rw [refEdge_mutBlock] at edge
  by_cases eq : r1 = ptr
  · subst r1
    rw [if_pos rfl] at edge
    simp only [getRefs, List.mem_flatMap, List.mem_append, List.mem_singleton] at edge
    obtain ⟨v, (vl | rfl) | vr, hz⟩ := edge
    · simp only [refEdge, old, getRefs, List.mem_flatMap, List.mem_append, List.mem_singleton]
      exact ⟨v, Or.inl (Or.inl vl), hz⟩
    · exact absurd hz notH
    · simp only [refEdge, old, getRefs, List.mem_flatMap, List.mem_append, List.mem_singleton]
      exact ⟨v, Or.inr vr, hz⟩
  · rwa [if_neg eq] at edge

/-- HOL `reachable_refs_MutBlock_UPDATE`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "reachable_refs_MutBlock_UPDATE"]
theorem reachableRefs_mutBlock_update (ptr tg n : Nat) (fin b : Bool)
    (ll : List Flapjack.Compiler.Backend.DataSem.Value) (cc h : Flapjack.Compiler.Backend.DataSem.Value)
    (rr stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) :
    sptLookup ptr refs = some (.mutBlock tg fin ll cc rr) ∧
        reachableRefs (h :: .refPtr b ptr :: stack) (sptInsert ptr (.mutBlock tg fin ll h rr) refs) n →
      reachableRefs (h :: .refPtr b ptr :: stack) refs n := by
  rintro ⟨old, reach⟩
  apply reachableRefs_insert_subset refs _ ptr _ _ n reach
  intro dest edge
  by_cases inH : dest ∈ getRefs h
  · exact ⟨h, dest, by simp, inH, .refl⟩
  · have oldEdge := refEdge_mutBlock_update ptr tg fin ll cc h rr refs ptr dest ⟨old, edge, inH⟩
    exact ⟨.refPtr b ptr, ptr, by simp, by simp [getRefs], .single oldEdge⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

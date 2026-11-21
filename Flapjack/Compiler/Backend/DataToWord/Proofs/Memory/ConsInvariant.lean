module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.Submap
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.HeapExtend
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ConsAllocation
public import Flapjack.FiniteMap.Exact

@[expose] public section

/-!
# Value invariant under heap extension and timestamp binding

Counterparts of `v_inv_SUBMAP_lemma`, both `v_inv_lemma` declarations,
`v_inv_LIST_REL`, `bind_each_def`, `bind_each_MONO` and `bind_each_SUBMAP` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`. HOL
`f ⊑ g` is `HolFiniteMapExact.submap`, `|+` is `HolFiniteMapExact.update`, and
`x ∈ FDOM m` is `m.lookup x ≠ none`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- HOL `v_inv_SUBMAP_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_SUBMAP_lemma"
  (fmap_as_finite_support_relation := [f, tf, f1, tf1]) (words_as_type_indexed_bitvec)]
theorem valueInv_submap_lemma {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (f1 : HolFiniteMapExact Nat Nat) (tf1 : HolFiniteMapExact Nat Nat)
    (heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) :
    ∀ (ck : Nat) (w : Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (x : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width),
      valueInv conf w refs (x, f, tf, heap) →
        f.submap f1 ∧ tf.submap tf1 ∧ heapStoreRel heap heap1 →
        ClockValueInv ck conf w refs (x, f1, tf1, heap1) := by
  rintro ck w refs x f tf heap inv ⟨references, timestamps, rel⟩
  apply clockValueInv_mapHeapExtend ck conf refs f f1 tf tf1 heap heap1 references timestamps ?_ w x (inv ck)
  intro ptr cell data found
  obtain ⟨xs, len, d, rfl⟩ := data
  exact (rel ptr ⟨xs, len, d, found⟩).trans found

/-- Data lookups survive replacing a free region by an allocation followed
by the remaining free space. -/
theorem heapLookup_expand_allocate {α β : Type} (ha hs hb : List (HeapElement α β)) (sp : Nat)
    (pos : 0 < heapLength hs) (le : heapLength hs ≤ sp) (ptr : Nat) (cell : HeapElement α β)
    (data : isDataElement cell) (found : heapLookup ptr (ha ++ heapExpand sp ++ hb) = some cell) :
    heapLookup ptr (ha ++ hs ++ heapExpand (sp - heapLength hs) ++ hb) = some cell := by
  have spPos : sp ≠ 0 := by omega
  have expand : (heapExpand sp : List (HeapElement α β)) = [.unused (sp - 1)] := by
    simp [heapExpand, spPos]
  rw [expand] at found
  have expandLen : ∀ m : Nat, heapLength (heapExpand m : List (HeapElement α β)) = m := by
    intro m
    cases m <;> simp [heapExpand, heapLength, elLength]
  have size : heapLength (hs ++ heapExpand (sp - heapLength hs)) = sp - 1 + 1 := by
    rw [heapLength_append, expandLen]
    omega
  have := heapLookup_allocate_preservesData ha hb (hs ++ heapExpand (sp - heapLength hs)) (sp - 1) size ptr cell
    data found
  simpa [List.append_assoc] using this

/-- HOL `v_inv_lemma` (the clock-indexed declaration at line 2448). The bound
variable `y` is unused, as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_lemma" 2448
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_lemma_ck {width : Nat} [NeZero width] {γ : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (ha hs hb : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (sp : Nat) :
    ∀ (ck : Nat) (v : Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (_y : γ)
      (x : HeapAddress (WordLocW width)) (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat),
      valueInv conf v refs (x, f, tf, ha ++ heapExpand sp ++ hb) →
        0 < heapLength hs ∧ heapLength hs ≤ sp →
        ClockValueInv ck conf v refs (x, f, tf, ha ++ hs ++ heapExpand (sp - heapLength hs) ++ hb) := by
  rintro ck v refs _ x f tf inv ⟨pos, le⟩
  exact clockValueInv_mapHeapExtend ck conf refs f f tf tf _ _ (fun _ _ h => h) (fun _ _ h => h)
    (fun ptr cell data found => heapLookup_expand_allocate ha hs hb sp pos le ptr cell data found) v x (inv ck)

/-- HOL `v_inv_lemma` (the unclocked declaration at line 2504). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_lemma" 2504
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_lemma {width : Nat} [NeZero width] :
    ∀ (conf : Flapjack.Compiler.Backend.DataToWord.Config) (v : Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (x : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
      (hs ha hb : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (sp : Nat),
      0 < heapLength hs ∧ heapLength hs ≤ sp ∧ valueInv conf v refs (x, f, tf, ha ++ heapExpand sp ++ hb) →
      valueInv conf v refs (x, f, tf, ha ++ hs ++ heapExpand (sp - heapLength hs) ++ hb) := by
  rintro conf v refs x f tf hs ha hb sp ⟨pos, le, inv⟩ ck
  exact valueInv_lemma_ck (γ := Unit) conf ha hs hb sp ck v refs () x f tf inv ⟨pos, le⟩

/-- HOL `v_inv_LIST_REL`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_LIST_REL"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_listRel {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
    (hs ha hb : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (sp : Nat) :
    ∀ (l1 : List (HeapAddress (WordLocW width))) (l2 : List Flapjack.Compiler.Backend.DataSem.Value),
      0 < heapLength hs ∧ heapLength hs ≤ sp ∧
        List.Forall₂ (fun z y => valueInv conf y refs (z, f, tf, ha ++ heapExpand sp ++ hb)) l1 l2 →
      List.Forall₂ (fun z y => valueInv conf y refs (z, f, tf, ha ++ hs ++ heapExpand (sp - heapLength hs) ++ hb))
        l1 l2 := by
  rintro l1 l2 ⟨pos, le, rel⟩
  exact rel.imp (fun z y inv => valueInv_lemma conf y refs z f tf hs ha hb sp ⟨pos, le, inv⟩)

/-- HOL `bind_each_def`: bind `n` consecutive timestamps from `ts`, each to
the next address in steps of `i` from `k`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bind_each_def"
  (fmap_as_finite_support_result)]
def bindEach (tf : HolFiniteMapExact Nat Nat) (ts k i : Nat) : Nat → HolFiniteMapExact Nat Nat
  | 0 => tf
  | n + 1 => (bindEach tf (ts + 1) (k + i) i n).update (ts, k)

/-- Independent raw-lookup rendering of `bind_each` for the codec witness. -/
def bindEachRaw (tf : Nat → Option Nat) (ts k i : Nat) : Nat → Nat → Option Nat
  | 0 => tf
  | n + 1 => fun key => if ts = key then some k else bindEachRaw tf (ts + 1) (k + i) i n key

/-- The canonical `bindEach` agrees with the raw lookup rendering. -/
theorem holFmapAsFiniteSupportResultWitness_bindEach (tf : HolFiniteMapExact Nat Nat) (ts k i n key : Nat) :
    (bindEach tf ts k i n).lookup key = bindEachRaw tf.lookup ts k i n key := by
  induction n generalizing ts k with
  | zero => rfl
  | succ n ih =>
    simp only [bindEach, bindEachRaw, HolFiniteMapExact.update, FUPDATE, ← ih]
    by_cases h : ts = key <;> simp [h]

/-- Lookup in `bindEach`. -/
theorem lookup_bindEach (tf : HolFiniteMapExact Nat Nat) (ts k i n key : Nat) :
    (bindEach tf ts k i (n + 1)).lookup key =
      if ts = key then some k else (bindEach tf (ts + 1) (k + i) i n).lookup key := by
  rw [holFmapAsFiniteSupportResultWitness_bindEach, holFmapAsFiniteSupportResultWitness_bindEach]
  rfl

/-- HOL `bind_each_MONO`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bind_each_MONO"
  (fmap_as_finite_support_relation := [tf])]
theorem bindEach_mono :
    ∀ (n t1 t2 : Nat) (tf : HolFiniteMapExact Nat Nat) (k i : Nat),
      t1 < t2 ∧ (∀ t, tf.lookup t ≠ none → t < t1) → ¬ (bindEach tf t2 k i n).lookup t1 ≠ none := by
  intro n
  induction n with
  | zero =>
    rintro t1 t2 tf k i ⟨lt, bound⟩ present
    have := bound t1 present
    omega
  | succ n ih =>
    rintro t1 t2 tf k i ⟨lt, bound⟩ present
    rw [lookup_bindEach, if_neg (by omega)] at present
    exact ih t1 (t2 + 1) tf (k + i) i ⟨by omega, bound⟩ present

/-- HOL `bind_each_SUBMAP`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bind_each_SUBMAP"
  (fmap_as_finite_support_relation := [tf])]
theorem bindEach_submap :
    ∀ (n : Nat) (tf : HolFiniteMapExact Nat Nat) (ts k i : Nat),
      (∀ t, tf.lookup t ≠ none → t < ts) → tf.submap (bindEach tf ts k i n) := by
  intro n
  induction n with
  | zero => intro tf ts k i _ key value h; exact h
  | succ n ih =>
    intro tf ts k i bound key value found
    rw [lookup_bindEach]
    have below := bound key (by simp [found])
    rw [if_neg (by omega)]
    exact ih tf (ts + 1) (k + i) i (fun t h => by have := bound t h; omega) key value found

/-- Updating an unused timestamp preserves existing timestamp lookups. -/
theorem lookup_update_fresh (tf : HolFiniteMapExact Nat Nat) (ts' a n p : Nat)
    (fresh : ¬ tf.lookup ts' ≠ none) (found : tf.lookup n = some p) :
    (tf.update (ts', a)).lookup n = some p := by
  have ne : ts' ≠ n := by
    rintro rfl
    exact fresh (by simp [found])
  simp [HolFiniteMapExact.update, FUPDATE, ne, found]

/-- HOL `v_inv_tf_update_thm_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_tf_update_thm_lemma"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_tfUpdate_lemma {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) :
    ∀ (ck : Nat) (v : Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (y : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
      (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (ts' a : Nat),
      valueInv conf v refs (y, f, tf, heap) ∧ ¬ tf.lookup ts' ≠ none →
        ClockValueInv ck conf v refs (y, f, tf.update (ts', a), heap) := by
  rintro ck v refs y f tf heap ts' a ⟨inv, fresh⟩
  exact clockValueInv_mapHeapExtend ck conf refs f f tf _ heap heap (fun _ _ h => h)
    (fun n p found => lookup_update_fresh tf ts' a n p fresh found) (fun _ _ _ h => h) v y (inv ck)

/-- HOL `v_inv_tf_update_thm`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_tf_update_thm"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_tfUpdate {width : Nat} [NeZero width] :
    ∀ (conf : Flapjack.Compiler.Backend.DataToWord.Config) (v : Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (y : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
      (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (ts' a : Nat),
      valueInv conf v refs (y, f, tf, heap) ∧ ¬ tf.lookup ts' ≠ none →
        valueInv conf v refs (y, f, tf.update (ts', a), heap) := by
  intro conf v refs y f tf heap ts' a h ck
  exact valueInv_tfUpdate_lemma conf ck v refs y f tf heap ts' a h

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

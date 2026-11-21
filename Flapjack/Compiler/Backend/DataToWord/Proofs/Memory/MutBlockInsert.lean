module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdateValue
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.RefUpdate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values.AllValues

@[expose] public section

/-!
# Inserting mutable blocks into the reference store

Counterparts of `v_inv_MutBlock_insert_lemma`, `v_inv_MutBlock_insert`,
`v_inv_MutBlock_fin_lemma`, `v_inv_MutBlock_fin`, `all_ts_SUBSET_gen`,
`all_ts_SUBSET_ts`, `all_ts_mutcons`, `blocks_unique_mutcons`, `ref_edge_MutBlock`,
`reachable_refs_MutCons_lemma`, `reachable_refs_MutCons`, `take_el_drop` and
`dest_thunk_insert_fresh` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`.
`k IN domain refs` is `sptMem k refs` and `FDOM f SUBSET domain refs` is
`∀ k, f.lookup k ≠ none → sptMem k refs`. Sets are predicates (`s SUBSET t`
is `∀ x, s x → t x`), `TAKE`/`DROP` are `List.take`/`List.drop` and `EL` is
`holEl`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- The clocked value relation transfers to a new reference store that keeps
every thunk, every pointer annotation and the thunk/mutable status of every
reference in `f`'s domain, and does not create thunks. Flapjack proof
infrastructure for the reference-insertion lemmas. -/
theorem clockValueInv_refsTransfer {width : Nat} [NeZero width] (ck : Nat)
    (conf : Config) (refs refs' : Spt (BvlSem.Ref Value)) (f : HolFiniteMapExact Nat Nat)
    (annot : ∀ n, f.lookup n ≠ none →
      refPtrAnnot (width := width) conf (sptLookup n refs') = refPtrAnnot conf (sptLookup n refs))
    (thunks : ∀ n mode body, sptLookup n refs = some (.thunk mode body) →
      sptLookup n refs' = some (.thunk mode body))
    (noThunks : ∀ n, f.lookup n ≠ none → (∀ mode body, sptLookup n refs ≠ some (.thunk mode body)) →
      ∀ mode body, sptLookup n refs' ≠ some (.thunk mode body))
    (muts : ∀ n, f.lookup n ≠ none → ∀ tag fin left body right,
      sptLookup n refs' = some (.mutBlock tag fin left body right) →
      ∃ fin', sptLookup n refs = some (.mutBlock tag fin' left body right))
    (dest : ∀ value, destThunk value refs = .notThunk → destThunk value refs' = .notThunk) :
    ∀ (value : Value) (tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
      (x : HeapAddress (WordLocW width)),
      ClockValueInv ck conf value refs (x, f, tf, heap) → ClockValueInv ck conf value refs' (x, f, tf, heap) := by
  induction ck using Nat.strongRecOn with
  | ind ck ih =>
    intro value tf heap x related
    cases related with
    | numberSmall _ _ i _ _ _ _ small => exact .numberSmall ck conf i _ f tf heap small
    | numberBig _ _ i address _ _ _ _ large found => exact .numberBig ck conf i address _ f tf heap large found
    | word64 _ _ word address _ _ _ _ found => exact .word64 ck conf word address _ f tf heap found
    | codePtr _ _ n _ _ _ _ => exact .codePtr ck conf n _ f tf heap
    | refPtr bit _ _ n _ _ _ _ domain notThunk notMut =>
      have defined : f.lookup n ≠ none := by
        obtain ⟨p, h⟩ := domain
        simp [h]
      rw [← annot n defined]
      apply ClockValueInv.refPtr bit ck conf n _ f tf heap domain (noThunks n defined notThunk)
      intro tag fin left body right lookup
      obtain ⟨fin', old⟩ := muts n defined tag fin left body right lookup
      exact notMut tag fin' left body right old
    | refPtrThunk _ _ mode n body addr _ _ _ _ found evaluated domain cell recursive =>
      refine .refPtrThunk ck conf mode n body addr _ f tf heap (thunks n mode body found)
        (fun h => dest body (evaluated h)) domain cell ?_
      intro positive
      exact ih (ck - 1) (by omega) body tf heap addr (recursive positive)
    | refPtrThunkInlined _ _ n body _ _ _ _ _ found notThunk recursive =>
      refine .refPtrThunkInlined ck conf n body x _ f tf heap (thunks n .evaluated body found)
        (dest body notThunk) ?_
      intro positive
      exact ih (ck - 1) (by omega) body tf heap x (recursive positive)
    | blockNil _ _ stamp tag values _ _ _ _ empty bound zero =>
      exact .blockNil ck conf stamp tag values _ f tf heap empty bound zero
    | blockCons _ _ stamp tag address values xs _ _ _ _ nonempty recursive timestamp cell =>
      refine .blockCons ck conf stamp tag address values xs _ f tf heap nonempty ?_ timestamp cell
      intro positive
      apply (clockValueListInv_iff _ _ _ _ _ _ _ _).mpr
      apply List.Forall₂.imp _ ((clockValueListInv_iff _ _ _ _ _ _ _ _).mp (recursive positive))
      intro child addr childInv
      exact ih (ck - 1) (by omega) child tf heap addr childInv

/-- Inserting at a fresh key changes no other lookup. -/
theorem sptLookup_insert_fresh_of_mem {α : Type} (refs : Spt α) (ptr n : Nat) (cell : α)
    (mem : sptMem n refs) (fresh : ¬ sptMem ptr refs) :
    sptLookup n (sptInsert ptr cell refs) = sptLookup n refs := by
  have ne : n ≠ ptr := by
    rintro rfl
    exact fresh mem
  exact sptLookup_sptInsert_ne ptr n cell refs ne

/-- HOL `v_inv_MutBlock_insert_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_MutBlock_insert_lemma"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_insertMutBlock_lemma {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ptr tag : Nat) (fin : Bool)
    (l : List Flapjack.Compiler.Backend.DataSem.Value) (cv : Flapjack.Compiler.Backend.DataSem.Value)
    (r : List Flapjack.Compiler.Backend.DataSem.Value) :
    ∀ (ck : Nat) (v1 : Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (y : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
      (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))),
      valueInv conf v1 refs (y, f, tf, heap) ∧ ¬ sptMem ptr refs ∧ (∀ k, f.lookup k ≠ none → sptMem k refs) →
      ClockValueInv ck conf v1 (sptInsert ptr (.mutBlock tag fin l cv r) refs) (y, f, tf, heap) := by
  rintro ck v1 refs y f tf heap ⟨inv, fresh, sub⟩
  have same : ∀ n, f.lookup n ≠ none →
      sptLookup n (sptInsert ptr (.mutBlock tag fin l cv r) refs) = sptLookup n refs :=
    fun n h => sptLookup_insert_fresh_of_mem refs ptr n _ (sub n h) fresh
  have absent : sptLookup ptr refs = none := by
    cases h : sptLookup ptr refs with
    | none => rfl
    | some cell => exact absurd (by simp [sptMem, sptDomain, h]) fresh
  apply clockValueInv_refsTransfer ck conf refs _ f
  · intro n h; rw [same n h]
  · intro n mode body found
    have ne : n ≠ ptr := by rintro rfl; simp [absent] at found
    rw [sptLookup_sptInsert_ne ptr n _ refs ne]; exact found
  · intro n h notThunk mode body; rw [same n h]; exact notThunk mode body
  · intro n h tag' fin' left body right lookup; rw [same n h] at lookup; exact ⟨fin', lookup⟩
  · intro value notThunk
    cases value with
    | refPtr bit index =>
      by_cases eq : index = ptr
      · subst index; simp [destThunk, absent] at notThunk
      · simpa [destThunk, sptLookup_sptInsert_ne ptr index _ refs eq] using notThunk
    | number _ | block _ _ _ | codePtr _ | word64 _ => simp [destThunk]
  · exact inv ck

/-- HOL `v_inv_MutBlock_insert`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_MutBlock_insert"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_insertMutBlock {width : Nat} [NeZero width] :
    ∀ (conf : Flapjack.Compiler.Backend.DataToWord.Config) (v1 : Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (v2 : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
      (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (ptr tag : Nat)
      (fin : Bool) (l : List Flapjack.Compiler.Backend.DataSem.Value) (cv : Flapjack.Compiler.Backend.DataSem.Value)
      (r : List Flapjack.Compiler.Backend.DataSem.Value),
      valueInv conf v1 refs (v2, f, tf, heap) ∧ ¬ sptMem ptr refs ∧ (∀ k, f.lookup k ≠ none → sptMem k refs) →
      valueInv conf v1 (sptInsert ptr (.mutBlock tag fin l cv r) refs) (v2, f, tf, heap) := by
  intro conf v1 refs v2 f tf heap ptr tag fin l cv r h ck
  exact valueInv_insertMutBlock_lemma conf ptr tag fin l cv r ck v1 refs v2 f tf heap h

/-- HOL `v_inv_MutBlock_fin_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_MutBlock_fin_lemma"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_mutBlockFin_lemma {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ptr tag : Nat) (fin1 fin2 : Bool)
    (ll : List Flapjack.Compiler.Backend.DataSem.Value) (cv : Flapjack.Compiler.Backend.DataSem.Value)
    (rr : List Flapjack.Compiler.Backend.DataSem.Value) :
    ∀ (ck : Nat) (v1 : Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (y : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
      (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))),
      valueInv conf v1 refs (y, f, tf, heap) ∧ sptLookup ptr refs = some (.mutBlock tag fin1 ll cv rr) →
      ClockValueInv ck conf v1 (sptInsert ptr (.mutBlock tag fin2 ll cv rr) refs) (y, f, tf, heap) := by
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
      exact ⟨fin1, old⟩
    · rw [sptLookup_sptInsert_ne ptr n _ refs eq] at lookup; exact ⟨fin', lookup⟩
  · intro value notThunk
    cases value with
    | refPtr bit index =>
      by_cases eq : index = ptr
      · subst index; simp [destThunk, sptLookup_sptInsert_same]
      · simpa [destThunk, sptLookup_sptInsert_ne ptr index _ refs eq] using notThunk
    | number _ | block _ _ _ | codePtr _ | word64 _ => simp [destThunk]
  · exact inv ck

/-- HOL `v_inv_MutBlock_fin`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_MutBlock_fin"
  (fmap_as_finite_support_relation := [ff, tff]) (words_as_type_indexed_bitvec)]
theorem valueInv_mutBlockFin {width : Nat} [NeZero width] :
    ∀ (cnf : Flapjack.Compiler.Backend.DataToWord.Config) (vv : Flapjack.Compiler.Backend.DataSem.Value)
      (rfs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (yy : HeapAddress (WordLocW width))
      (ff : HolFiniteMapExact Nat Nat) (tff : HolFiniteMapExact Nat Nat)
      (hp : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (pp tg : Nat)
      (b1 b2 : Bool) (l1 : List Flapjack.Compiler.Backend.DataSem.Value) (c1 : Flapjack.Compiler.Backend.DataSem.Value)
      (r1 : List Flapjack.Compiler.Backend.DataSem.Value),
      valueInv cnf vv rfs (yy, ff, tff, hp) ∧ sptLookup pp rfs = some (.mutBlock tg b1 l1 c1 r1) →
      valueInv cnf vv (sptInsert pp (.mutBlock tg b2 l1 c1 r1) rfs) (yy, ff, tff, hp) := by
  intro cnf vv rfs yy ff tff hp pp tg b1 b2 l1 c1 r1 h ck
  exact valueInv_mutBlockFin_lemma cnf pp tg b1 b2 l1 c1 r1 ck vv rfs yy ff tff hp h

/-- HOL `all_ts_SUBSET_gen`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_ts_SUBSET_gen"]
theorem allTimestamps_subset_gen (refs1 refs2 : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (stack1 stack2 : List Flapjack.Compiler.Backend.DataSem.Value) :
    (∀ x, ((∃ n r', sptLookup n refs1 = some r' ∧ findRef r' x) ∨ x ∈ stack1) →
        ((∃ n r', sptLookup n refs2 = some r' ∧ findRef r' x) ∨ x ∈ stack2)) →
      ∀ t, allTimestamps refs1 stack1 t → allTimestamps refs2 stack2 t := by
  rintro h t ⟨x, member, stamp⟩
  exact ⟨x, h x member, stamp⟩

/-- HOL `all_ts_SUBSET_ts`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_ts_SUBSET_ts"]
theorem allTimestamps_subset_ts (refs1 refs2 : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (stack1 stack2 : List Flapjack.Compiler.Backend.DataSem.Value) :
    (∀ x t, (((∃ n r', sptLookup n refs1 = some r' ∧ findRef r' x) ∨ x ∈ stack1) ∧ t ∈ valueTimestamps x) →
        ∃ x', ((∃ n r', sptLookup n refs2 = some r' ∧ findRef r' x') ∨ x' ∈ stack2) ∧ t ∈ valueTimestamps x') →
      ∀ t, allTimestamps refs1 stack1 t → allTimestamps refs2 stack2 t := by
  rintro h t ⟨x, member, stamp⟩
  exact h x t ⟨member, stamp⟩

/-- HOL `all_ts_mutcons`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_ts_mutcons"]
theorem allTimestamps_mutcons (ptr tag : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (l : List Flapjack.Compiler.Backend.DataSem.Value) (c : Flapjack.Compiler.Backend.DataSem.Value)
    (r stack : List Flapjack.Compiler.Backend.DataSem.Value) :
    ¬ sptMem ptr refs →
      ∀ t, allTimestamps refs ((l ++ [c] ++ r) ++ stack) t →
        allTimestamps (sptInsert ptr (.mutBlock tag false l c r) refs) (.refPtr false ptr :: stack) t := by
  intro fresh
  apply allTimestamps_subset_gen
  rintro x (⟨n, cell, found, member⟩ | member)
  · have ne : n ≠ ptr := by
      rintro rfl
      exact fresh (by simp [sptMem, sptDomain, found])
    exact Or.inl ⟨n, cell, by rw [sptLookup_sptInsert_ne ptr n _ refs ne]; exact found, member⟩
  · rcases List.mem_append.mp member with inBlock | inStack
    · exact Or.inl ⟨ptr, _, sptLookup_sptInsert_same .., inBlock⟩
    · exact Or.inr (List.mem_cons_of_mem _ inStack)

/-- HOL `ref_edge_MutBlock`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "ref_edge_MutBlock"]
theorem refEdge_mutBlock (ptr tag : Nat) (fin : Bool) (l : List Flapjack.Compiler.Backend.DataSem.Value)
    (c : Flapjack.Compiler.Backend.DataSem.Value) (r : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (x y : Nat) :
    refEdge (sptInsert ptr (.mutBlock tag fin l c r) refs) x y ↔
      if x = ptr then y ∈ getRefs (.block 0 (holArb Nat) (l ++ [c] ++ r)) else refEdge refs x y := by
  by_cases h : x = ptr
  · subst h
    simp [refEdge, sptLookup_sptInsert_same, getRefs]
  · simp [refEdge, sptLookup_sptInsert_ne ptr x _ refs h, h]

/-- HOL `take_el_drop`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "take_el_drop"
  (total_function_inhabitants := [α])]
theorem take_el_drop {α : Type} [Nonempty α] :
    ∀ (index : Nat) (vals : List α), index < vals.length →
      vals.take index ++ [holEl index vals] ++ vals.drop (index + 1) = vals := by
  intro index vals h
  rw [holEl_eq_getElem index vals h, List.append_assoc, List.singleton_append,
    ← List.drop_eq_getElem_cons h, List.take_append_drop]

/-- HOL `dest_thunk_insert_fresh`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "dest_thunk_insert_fresh"]
theorem destThunk_insert_fresh (ptr : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (v : Flapjack.Compiler.Backend.DataSem.Value) (x : BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value) :
    ¬ sptMem ptr refs ∧ destThunk v refs = .notThunk → destThunk v (sptInsert ptr x refs) = .notThunk := by
  rintro ⟨fresh, notThunk⟩
  cases v with
  | refPtr bit index =>
    by_cases eq : index = ptr
    · subst index
      have absent : sptLookup ptr refs = none := by
        cases h : sptLookup ptr refs with
        | none => rfl
        | some cell => exact absurd (by simp [sptMem, sptDomain, h]) fresh
      simp [destThunk, absent] at notThunk
    · simpa [destThunk, sptLookup_sptInsert_ne ptr index _ refs eq] using notThunk
  | number _ | block _ _ _ | codePtr _ | word64 _ => simp [destThunk]

/-- HOL `blocks_unique_mutcons`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_mutcons"]
theorem blocksUnique_mutcons (ts ptr tag : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (l : List Flapjack.Compiler.Backend.DataSem.Value) (c : Flapjack.Compiler.Backend.DataSem.Value)
    (r stack : List Flapjack.Compiler.Backend.DataSem.Value) :
    blocksUnique ts (allValues refs ((l ++ [c] ++ r) ++ stack)) →
      blocksUnique ts (allValues (sptInsert ptr (.mutBlock tag false l c r) refs) (.refPtr false ptr :: stack)) := by
  intro unique
  have toStack : ∀ v, v ∈ valueListValues (l ++ [c] ++ r) →
      v ∈ valueListValues ((l ++ [c] ++ r) ++ stack) := by
    intro v h
    rw [valueListValues_append, List.mem_append]
    exact Or.inl h
  have sub : ∀ s t xs, allValues (sptInsert ptr (.mutBlock tag false l c r) refs) (.refPtr false ptr :: stack)
      (.block s t xs) → allValues refs ((l ++ [c] ++ r) ++ stack) (.block s t xs) := by
    intro s t xs h
    rcases h with ⟨i, vs, found, m⟩ | ⟨i, mode, ch, found, m⟩ | ⟨i, t', fin, l', c', r', found, m⟩ | m
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
        exact Or.inr (Or.inr (Or.inr (toStack _ m)))
      · rw [sptLookup_sptInsert_ne ptr i _ refs eq] at found
        exact Or.inr (Or.inr (Or.inl ⟨i, t', fin, l', c', r', found, m⟩))
    · rw [valueListValues_cons] at m
      simp only [valueListValues, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        reduceCtorEq, false_or] at m
      refine Or.inr (Or.inr (Or.inr ?_))
      rw [valueListValues_append, List.mem_append]
      exact Or.inr m
  intro stamp tag1 xs1 tag2 xs2 ⟨h1, n1, h2, n2⟩
  exact unique stamp tag1 xs1 tag2 xs2 ⟨sub _ _ _ h1, n1, sub _ _ _ h2, n2⟩

/-- HOL `reachable_refs_MutCons_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "reachable_refs_MutCons_lemma"]
theorem reachableRefs_mutCons_lemma (ptr tag : Nat) (l : List Flapjack.Compiler.Backend.DataSem.Value)
    (c : Flapjack.Compiler.Backend.DataSem.Value) (r : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) :
    ∀ r1 n, Relation.ReflTransGen (refEdge (sptInsert ptr (.mutBlock tag false l c r) refs)) r1 n →
      n ≠ ptr →
      Relation.ReflTransGen (refEdge refs) r1 n ∨
        ∃ s, s ∈ getRefs (.block 0 (holArb Nat) (l ++ [c] ++ r)) ∧ Relation.ReflTransGen (refEdge refs) s n := by
  intro r1 n path
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => intro _; exact Or.inl .refl
  | @head a b edge _ ih =>
    intro ne
    rw [refEdge_mutBlock] at edge
    by_cases eq : a = ptr
    · rw [if_pos eq] at edge
      rcases ih ne with path | ⟨s, member, path⟩
      · exact Or.inr ⟨b, edge, path⟩
      · exact Or.inr ⟨s, member, path⟩
    · rw [if_neg eq] at edge
      rcases ih ne with path | ⟨s, member, path⟩
      · exact Or.inl (.head edge path)
      · exact Or.inr ⟨s, member, path⟩

/-- HOL `reachable_refs_MutCons`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "reachable_refs_MutCons"]
theorem reachableRefs_mutCons (ptr tag n : Nat) (stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (l : List Flapjack.Compiler.Backend.DataSem.Value) (c : Flapjack.Compiler.Backend.DataSem.Value)
    (r : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) :
    reachableRefs (.refPtr false ptr :: stack) (sptInsert ptr (.mutBlock tag false l c r) refs) n ∧
        n ≠ ptr ∧ ¬ sptMem ptr refs →
      reachableRefs ((l ++ [c] ++ r) ++ stack) refs n := by
  rintro ⟨⟨root, start, rootMember, startMember, path⟩, ne, fresh⟩
  have absent : sptLookup ptr refs = none := by
    cases h : sptLookup ptr refs with
    | none => rfl
    | some cell => exact absurd (by simp [sptMem, sptDomain, h]) fresh
  have fromBlock : ∀ s, s ∈ getRefs (.block 0 (holArb Nat) (l ++ [c] ++ r)) →
      Relation.ReflTransGen (refEdge refs) s n → reachableRefs ((l ++ [c] ++ r) ++ stack) refs n := by
    intro s member path
    simp only [getRefs, List.mem_flatMap] at member
    obtain ⟨v, vMember, sMember⟩ := member
    exact ⟨v, s, List.mem_append_left _ vMember, sMember, path⟩
  rcases reachableRefs_mutCons_lemma ptr tag l c r refs start n path ne with oldPath | ⟨s, member, blockPath⟩
  · rcases List.mem_cons.mp rootMember with rfl | inStack
    · simp only [getRefs, List.mem_singleton] at startMember
      subst startMember
      rcases Relation.ReflTransGen.cases_head oldPath with eq | ⟨z, edge, _⟩
      · exact absurd eq.symm ne
      · simp [refEdge, absent] at edge
    · exact ⟨root, start, List.mem_append_right _ inStack, startMember, oldPath⟩
  · exact fromBlock s member blockPath

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

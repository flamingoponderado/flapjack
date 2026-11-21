module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.MutBlockInsert
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.Submap
public import Flapjack.Compiler.Backend.Semantics.DataSem.Finalise
public import Flapjack.Misc.PredSet
public import Flapjack.Misc.SptreeLookup
public import Flapjack.FiniteMap.DomExact
public import Flapjack.FiniteMap.BroadCodec
public import Flapjack.FiniteMap.SubmapExact

@[expose] public section

/-!
# Finalising mutable constructor chains

Counterparts of `INJ_FUPDATE`, `finalise_cons_none`, `v_inv_swap_refs`,
`bc_stack_ref_inv_swap_refs`, the FinaliseCons stack-invariant group
(`blocks_unique_SUBSET` through `bc_stack_ref_inv_FinaliseCons_lemma`) and
`memory_rel_FinaliseCons` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`.
Sets are predicates: `s SUBSET t` is `∀ x, s x → t x`, `x INSERT s` is
`fun y => y = x ∨ s y`, `INJ` is `holInj`, `FDOM` is
`HolFiniteMapExact.dom`, `x ∉ FRANGE tf` is `¬ ∃ k, tf.lookup k = some x`,
`FAPPLY` is `holFapply`, `|+` is `HolFiniteMapExact.updateEq`, `EL` is
`holEl`, `THE` is `holThe`, `IS_SOME` is `Option.isSome`, `union`,
`delete`, `insert` and `lookup` on `sptree` are `sptUnion`, `sptDelete`,
`sptInsert` and `sptLookup`, and `SUC` is `+ 1`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Canonical map codec roundtrip for the `INJ_FUPDATE` parameter `tf`. -/
theorem holFmapAsFiniteSupportParamWitness_inj_fupdate_tf {α β : Type}
    (tf : HolFiniteMapExact α β) (key : α) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad tf)).lookup key = tf.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad tf)).finiteSupport = tf.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad tf) = tf := by
  cases tf
  exact ⟨rfl, rfl, rfl⟩

/-- HOL `INJ_FUPDATE`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "INJ_FUPDATE"
  (fmap_as_finite_support_parameters := [tf]) (total_function_inhabitants := [β])]
theorem inj_fupdate {α β : Type} [DecidableEq α] [Nonempty β] (tf : HolFiniteMapExact α β)
    (s : β → Prop) (ts2 : α) (x : β) :
    holInj (holFapply tf) tf.dom s ∧ ts2 ∉ tf.dom ∧ ¬ (∃ k, tf.lookup k = some x) ∧ s x →
      holInj (holFapply (tf.updateEq (ts2, x))) (tf.updateEq (ts2, x)).dom s := by
  rintro ⟨⟨into, inj⟩, fresh, notRange, sx⟩
  have apply_upd : ∀ k, holFapply (tf.updateEq (ts2, x)) k = if k = ts2 then x else holFapply tf k := by
    intro k
    by_cases h : k = ts2
    · subst h; simp [holFapply, HolFiniteMapExact.updateEq, FUPDATE_HOL]
    · simp [holFapply, HolFiniteMapExact.updateEq, FUPDATE_HOL, h]
  have dom_upd : ∀ k, k ∈ (tf.updateEq (ts2, x)).dom ↔ k = ts2 ∨ k ∈ tf.dom := by
    intro k
    by_cases h : k = ts2
    · subst h; simp [HolFiniteMapExact.dom, HolFiniteMapExact.updateEq, FUPDATE_HOL]
    · simp [HolFiniteMapExact.dom, HolFiniteMapExact.updateEq, FUPDATE_HOL, h]
  have inRange : ∀ k, k ∈ tf.dom → holFapply tf k ≠ x := by
    intro k hk eq
    apply notRange
    refine ⟨k, ?_⟩
    cases h : tf.lookup k with
    | none => exact absurd h hk
    | some v => simp [holFapply, h] at eq; rw [eq]
  constructor
  · intro k hk
    rw [apply_upd]
    rcases (dom_upd k).mp hk with eq | old
    · subst eq; simpa using sx
    · have ne : k ≠ ts2 := fun eq => fresh (eq ▸ old)
      simpa [ne] using into k old
  · intro a b ⟨ha, hb⟩ eq
    rw [apply_upd, apply_upd] at eq
    rcases (dom_upd a).mp ha with ea | oa <;> rcases (dom_upd b).mp hb with eb | ob
    · exact ea.trans eb.symm
    · have ne : b ≠ ts2 := fun e => fresh (e ▸ ob)
      simp [ea, ne] at eq
      exact absurd eq.symm (inRange b ob)
    · have ne : a ≠ ts2 := fun e => fresh (e ▸ oa)
      simp [eb, ne] at eq
      exact absurd eq (inRange a oa)
    · have na : a ≠ ts2 := fun e => fresh (e ▸ oa)
      have nb : b ≠ ts2 := fun e => fresh (e ▸ ob)
      simp [na, nb] at eq
      exact inj a b ⟨oa, ob⟩ eq

/-- The reference-pointer equation of `finaliseCons`, with the dependent
match on the lookup replaced by an ordinary one. Flapjack proof
infrastructure. -/
theorem finaliseCons_refPtr_eq (bit : Bool) (ptr : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (ts : Option Nat) :
    finaliseCons (.refPtr bit ptr) refs ts =
      match sptLookup ptr refs with
      | some (.mutBlock tag finalised left child right) =>
          if finalised then none else
            match finaliseCons child (sptDelete ptr refs) ts with
            | none => none
            | some (result, rest, nextTimestamp) =>
                some (.block (nextTimestamp.getD 0) tag (left ++ [result] ++ right),
                  sptInsert ptr (.mutBlock tag true left child right) rest, nextTimestamp.map (· + 1))
      | some _ => some (.refPtr bit ptr, refs, ts)
      | none => none := by
  rw [finaliseCons.eq_def]
  simp only
  split
  · split
    · simp_all
    · simp_all
      split <;> simp_all
  all_goals simp_all

/-- HOL `finalise_cons_none`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "finalise_cons_none"]
theorem finaliseCons_none (ptr : Nat) :
    ∀ (v : Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (ts_opt : Option Nat) (v' : Flapjack.Compiler.Backend.DataSem.Value)
      (refs' : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (ts' : Option Nat),
      finaliseCons v refs ts_opt = some (v', refs', ts') ∧ sptLookup ptr refs = none →
        sptLookup ptr refs' = none := by
  intro v refs ts_opt
  induction v, refs using finaliseCons.induct (timestamp := ts_opt) with
  | case1 refs bit p tag left child right found =>
      rintro v' refs' ts' ⟨h, -⟩
      rw [finaliseCons_refPtr_eq, found] at h
      simp at h
  | case2 refs bit p tag fin left child right found nfin noneEq _ =>
      rintro v' refs' ts' ⟨h, -⟩
      rw [finaliseCons_refPtr_eq, found] at h
      simp [nfin, noneEq] at h
  | case3 refs bit p tag fin left child right found nfin result rest next eq ih =>
      rintro v' refs' ts' ⟨h, absent⟩
      rw [finaliseCons_refPtr_eq, found] at h
      simp [nfin, eq] at h
      obtain ⟨-, rfl, -⟩ := h
      have pne : ptr ≠ p := by rintro rfl; simp [found] at absent
      rw [sptLookup_sptInsert_ne _ _ _ _ pne]
      exact ih result rest next ⟨eq, by rw [sptLookup_sptDelete]; simp [pne, absent]⟩
  | case4 refs bit p val notMut found =>
      rintro v' refs' ts' ⟨h, absent⟩
      rw [finaliseCons_refPtr_eq, found] at h
      cases val with
      | mutBlock tag fin left child right => exact (notMut tag fin left child right rfl).elim
      | _ => simp at h; obtain ⟨-, rfl, -⟩ := h; exact absent
  | case5 refs bit p found =>
      rintro v' refs' ts' ⟨h, -⟩
      rw [finaliseCons_refPtr_eq, found] at h
      simp at h
  | case6 refs other notRef =>
      rintro v' refs' ts' ⟨h, absent⟩
      cases other with
      | refPtr bit p => exact (notRef bit p rfl).elim
      | _ => simp [finaliseCons] at h; obtain ⟨-, rfl, -⟩ := h; exact absent

/-- HOL `v_inv_swap_refs`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_swap_refs"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_swapRefs {width : Nat} [NeZero width] :
    ∀ (c : Flapjack.Compiler.Backend.DataToWord.Config) (v : Flapjack.Compiler.Backend.DataSem.Value) (refs1 : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
      (x : HeapAddress (WordLocW width)) (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
      (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)),
      valueInv c v refs1 (x, f, tf, heap) ∧ (∀ n, sptLookup n refs = sptLookup n refs1) →
        valueInv c v refs (x, f, tf, heap) := by
  rintro c v refs1 x f tf heap refs ⟨inv, same⟩ ck
  apply clockValueInv_refsTransfer ck c refs1 refs f
  · intro n _; rw [same n]
  · intro n mode body found; rw [same n]; exact found
  · intro n _ notThunk mode body; rw [same n]; exact notThunk mode body
  · intro n _ tag fin left body right lookup
    rw [same n] at lookup; exact ⟨fin, body, lookup⟩
  · intro value notThunk
    cases value with
    | refPtr bit index => simpa [destThunk, same index] using notThunk
    | number _ | block _ _ _ | codePtr _ | word64 _ => simp [destThunk]
  · exact inv ck

/-- Reference-store functions observed through lookups agree on stores with
the same lookups. Flapjack proof infrastructure for the swap lemmas. -/
theorem lookupCongr_observers {width : Nat} [NeZero width]
    (c : Flapjack.Compiler.Backend.DataToWord.Config) (refs refs1 : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (same : ∀ n, sptLookup n refs = sptLookup n refs1) :
    allTimestamps refs = allTimestamps refs1 ∧ allValues refs = allValues refs1 ∧
      refEdge refs = refEdge refs1 ∧
      (∀ v, destThunk v refs = destThunk v refs1) ∧
      (∀ v (ctx : ValueContext width), valueInv c v refs ctx ↔ valueInv c v refs1 ctx) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext stack t; simp only [allTimestamps, same]
  · funext stack v; simp only [allValues, same]
  · funext i t; simp only [refEdge, same]
  · intro v
    cases v with
    | refPtr bit index => simp [destThunk, same index]
    | number _ | block _ _ _ | codePtr _ | word64 _ => simp [destThunk]
  · rintro v ⟨x, f, tf, heap⟩
    exact ⟨fun h => valueInv_swapRefs c v refs x f tf heap refs1 ⟨h, fun n => (same n).symm⟩,
      fun h => valueInv_swapRefs c v refs1 x f tf heap refs ⟨h, same⟩⟩

/-- HOL `bc_stack_ref_inv_swap_refs`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bc_stack_ref_inv_swap_refs"
  (words_as_type_indexed_bitvec)]
theorem bcStackRefInv_swapRefs {width : Nat} [NeZero width]
    (c : Flapjack.Compiler.Backend.DataToWord.Config) (ts : Nat) (vars : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (xs : List (HeapAddress (WordLocW width)))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (be : Bool)
    (refs1 : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) :
    bcStackRefInv c ts vars refs (xs, heap, be) ∧ (∀ n, sptLookup n refs = sptLookup n refs1) →
      bcStackRefInv c ts vars refs1 (xs, heap, be) := by
  rintro ⟨⟨f, tf, injF, domF, injTf, tsTf, ltTf, beq, unique, rel, refInv⟩, same⟩
  obtain ⟨hts, hvs, hedge, hdest, hinv⟩ := lookupCongr_observers (width := width) c refs refs1 same
  refine ⟨f, tf, injF, ?_, injTf, ?_, ltTf, beq, ?_, ?_, ?_⟩
  · intro n hn; rw [← same n]; exact domF n hn
  · rw [← hts]; exact tsTf
  · rw [← hvs]; exact unique
  · exact rel.imp fun v a h => (hinv v _).mp h
  · intro n ⟨reach, dom⟩
    have old := refInv n ⟨by simpa [reachableRefs, hedge] using reach, dom⟩
    simp only [bcRefInv] at old ⊢
    rw [← same n]
    split at old <;> simp_all

/-- HOL `blocks_unique_SUBSET`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_SUBSET"]
theorem blocksUnique_subset (ts : Nat) (vs2 vs1 : Flapjack.Compiler.Backend.DataSem.Value → Prop) :
    blocksUnique ts vs2 ∧ (∀ v, vs1 v → vs2 v) → blocksUnique ts vs1 := by
  rintro ⟨unique, sub⟩ stamp tag1 xs1 tag2 xs2 ⟨h1, n1, h2, n2⟩
  exact unique stamp tag1 xs1 tag2 xs2 ⟨sub _ h1, n1, sub _ h2, n2⟩

/-- HOL `blocks_unique_INSERT`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_INSERT"]
theorem blocksUnique_insert (ts : Nat) (vs : Flapjack.Compiler.Backend.DataSem.Value → Prop) (tag : Nat) (l : List Flapjack.Compiler.Backend.DataSem.Value) :
    blocksUnique ts vs → blocksUnique (ts + 1) (fun v => v = .block ts tag l ∨ vs v) := by
  intro unique stamp tag1 xs1 tag2 xs2 ⟨h1, n1, h2, n2⟩
  rcases h1 with e1 | h1 <;> rcases h2 with e2 | h2
  · simp only [Flapjack.Compiler.Backend.DataSem.Value.block.injEq] at e1 e2
    obtain ⟨rfl, rfl, rfl⟩ := e1
    obtain ⟨-, rfl, rfl⟩ := e2
    exact ⟨rfl, rfl, by omega⟩
  · simp only [Flapjack.Compiler.Backend.DataSem.Value.block.injEq] at e1
    obtain ⟨rfl, rfl, rfl⟩ := e1
    have := (unique stamp tag2 xs2 tag2 xs2 ⟨h2, n2, h2, n2⟩).2.2
    omega
  · simp only [Flapjack.Compiler.Backend.DataSem.Value.block.injEq] at e2
    obtain ⟨rfl, rfl, rfl⟩ := e2
    have := (unique stamp tag1 xs1 tag1 xs1 ⟨h1, n1, h1, n1⟩).2.2
    omega
  · obtain ⟨a, b, c⟩ := unique stamp tag1 xs1 tag2 xs2 ⟨h1, n1, h2, n2⟩
    exact ⟨a, b, by omega⟩

/-- HOL `all_ts_CONS_SUBSET`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_ts_CONS_SUBSET"]
theorem allTimestamps_cons_subset (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (stack : List Flapjack.Compiler.Backend.DataSem.Value) (x : Flapjack.Compiler.Backend.DataSem.Value) :
    ∀ t, allTimestamps refs stack t → allTimestamps refs (x :: stack) t := by
  apply allTimestamps_subset_gen
  rintro v (h | h)
  · exact Or.inl h
  · exact Or.inr (List.mem_cons_of_mem _ h)

/-- HOL `in_all_vs_stack`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "in_all_vs_stack"]
theorem allValues_of_stack (v : Flapjack.Compiler.Backend.DataSem.Value) (stack : List Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) :
    v ∈ valueListValues stack → allValues refs stack v :=
  fun h => Or.inr (Or.inr (Or.inr h))

/-- HOL `in_all_vs_MutBlock`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "in_all_vs_MutBlock"]
theorem allValues_of_mutBlock (n : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (tg : Nat) (fin : Bool)
    (l : List Flapjack.Compiler.Backend.DataSem.Value) (c : Flapjack.Compiler.Backend.DataSem.Value) (r : List Flapjack.Compiler.Backend.DataSem.Value) (v : Flapjack.Compiler.Backend.DataSem.Value) (stack : List Flapjack.Compiler.Backend.DataSem.Value) :
    sptLookup n refs = some (.mutBlock tg fin l c r) ∧ v ∈ valueListValues (l ++ [c] ++ r) →
      allValues refs stack v :=
  fun ⟨found, member⟩ => Or.inr (Or.inr (Or.inl ⟨n, tg, fin, l, c, r, found, member⟩))

/-- HOL `all_vs_CONS_SUBSET`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_vs_CONS_SUBSET"]
theorem allValues_cons_subset (x : Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (stack : List Flapjack.Compiler.Backend.DataSem.Value) :
    allValues refs stack x → ∀ v, allValues refs (x :: stack) v → allValues refs stack v := by
  intro hx v hv
  rcases hv with a | t | m | inStack
  · exact Or.inl a
  · exact Or.inr (Or.inl t)
  · exact Or.inr (Or.inr (Or.inl m))
  · rw [valueListValues_cons, List.mem_append] at inStack
    rcases inStack with nested | rest
    · exact allValues_valueListValues x v stack refs ⟨hx, nested⟩
    · exact Or.inr (Or.inr (Or.inr rest))

/-- HOL `all_vs_MutBlock_centre`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_vs_MutBlock_centre"]
theorem allValues_mutBlock_centre (ptr : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (tag : Nat) (fin : Bool)
    (left : List Flapjack.Compiler.Backend.DataSem.Value) (cen : Flapjack.Compiler.Backend.DataSem.Value) (right stack : List Flapjack.Compiler.Backend.DataSem.Value) :
    sptLookup ptr refs = some (.mutBlock tag fin left cen right) →
      ∀ v, allValues refs (cen :: stack) v → allValues refs stack v := by
  intro found
  apply allValues_cons_subset
  exact allValues_of_mutBlock ptr refs tag fin left cen right cen stack
    ⟨found, mem_valueListValues _ _ (by simp)⟩

/-- HOL `all_vs_MutBlock_T`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_vs_MutBlock_T"]
theorem allValues_mutBlock_T (ptr : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (tag : Nat)
    (left : List Flapjack.Compiler.Backend.DataSem.Value) (cen : Flapjack.Compiler.Backend.DataSem.Value) (right : List Flapjack.Compiler.Backend.DataSem.Value) (ts2 : Nat) (res : Flapjack.Compiler.Backend.DataSem.Value)
    (vars : List Flapjack.Compiler.Backend.DataSem.Value) (b : Bool) :
    sptLookup ptr refs = some (.mutBlock tag false left cen right) →
      ∀ v, allValues (sptInsert ptr (.mutBlock tag true left cen right) refs)
          (.block ts2 tag (left ++ [res] ++ right) :: vars) v →
        v = .block ts2 tag (left ++ [res] ++ right) ∨
          allValues refs (res :: .refPtr b ptr :: vars) v := by
  intro found v hv
  have lookupIns : ∀ i, sptLookup i (sptInsert ptr (.mutBlock tag true left cen right) refs) =
      if i = ptr then some (.mutBlock tag true left cen right) else sptLookup i refs := by
    intro i
    by_cases h : i = ptr
    · subst h; simp [sptLookup_sptInsert_same]
    · simp [sptLookup_sptInsert_ne _ _ _ _ h, h]
  rcases hv with ⟨i, vs, f, m⟩ | ⟨i, mode, ch, f, m⟩ | ⟨i, t, fin, l, c, r, f, m⟩ | m
  · rw [lookupIns] at f
    split at f
    · simp at f
    · exact Or.inr (Or.inl ⟨i, vs, f, m⟩)
  · rw [lookupIns] at f
    split at f
    · simp at f
    · exact Or.inr (Or.inr (Or.inl ⟨i, mode, ch, f, m⟩))
  · rw [lookupIns] at f
    split at f
    · simp only [Option.some.injEq, BvlSem.Ref.mutBlock.injEq] at f
      obtain ⟨-, -, rfl, rfl, rfl⟩ := f
      exact Or.inr (allValues_of_mutBlock ptr refs tag false left cen right v _ ⟨found, m⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, t, fin, l, c, r, f, m⟩)))
  · rw [valueListValues_cons, List.mem_append] at m
    rcases m with head | rest
    · simp only [valueListValues, List.append_nil, List.mem_cons] at head
      rcases head with rfl | nested
      · exact Or.inl rfl
      · rw [valueListValues_append, valueListValues_append, List.mem_append, List.mem_append] at nested
        rcases nested with (inL | inRes) | inR
        · exact Or.inr (allValues_of_mutBlock ptr refs tag false left cen right v _
            ⟨found, by rw [valueListValues_append, valueListValues_append]; simp [inL]⟩)
        · refine Or.inr (allValues_of_stack v _ refs ?_)
          rw [valueListValues_cons, List.mem_append]; exact Or.inl inRes
        · exact Or.inr (allValues_of_mutBlock ptr refs tag false left cen right v _
            ⟨found, by rw [valueListValues_append, valueListValues_append]; simp [inR]⟩)
    · refine Or.inr (allValues_of_stack v _ refs ?_)
      rw [valueListValues_cons, List.mem_append]
      exact Or.inr (by simp [valueListValues, rest])

/-- HOL `reachable_refs_MutBlock_centre`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "reachable_refs_MutBlock_centre"]
theorem reachableRefs_mutBlock_centre (ptr : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (tag : Nat) (fin : Bool)
    (left : List Flapjack.Compiler.Backend.DataSem.Value) (cen : Flapjack.Compiler.Backend.DataSem.Value) (right : List Flapjack.Compiler.Backend.DataSem.Value) (b : Bool) (vars : List Flapjack.Compiler.Backend.DataSem.Value) (n : Nat) :
    sptLookup ptr refs = some (.mutBlock tag fin left cen right) ∧
        reachableRefs (cen :: .refPtr b ptr :: vars) refs n →
      reachableRefs (.refPtr b ptr :: vars) refs n := by
  rintro ⟨found, root, start, rootMem, startMem, path⟩
  rcases List.mem_cons.mp rootMem with rfl | rest
  · refine ⟨.refPtr b ptr, ptr, List.mem_cons_self, by simp [getRefs], .head ?_ path⟩
    simp only [refEdge, found, getRefs, List.mem_flatMap]
    exact ⟨root, by simp, startMem⟩
  · exact ⟨root, start, rest, startMem, path⟩

/-- HOL `ref_edge_insert_MutBlock`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "ref_edge_insert_MutBlock"]
theorem refEdge_insert_mutBlock (ptr : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (tg : Nat) (fin1 : Bool)
    (l : List Flapjack.Compiler.Backend.DataSem.Value) (c : Flapjack.Compiler.Backend.DataSem.Value) (r : List Flapjack.Compiler.Backend.DataSem.Value) (fin2 : Bool) :
    sptLookup ptr refs = some (.mutBlock tg fin1 l c r) →
      refEdge (sptInsert ptr (.mutBlock tg fin2 l c r) refs) = refEdge refs := by
  intro found
  funext i t
  by_cases h : i = ptr
  · subst h; simp [refEdge, sptLookup_sptInsert_same, found]
  · simp [refEdge, sptLookup_sptInsert_ne _ _ _ _ h]

/-- HOL `reachable_refs_MutBlock_T`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "reachable_refs_MutBlock_T"]
theorem reachableRefs_mutBlock_T (ptr : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (tag : Nat)
    (left : List Flapjack.Compiler.Backend.DataSem.Value) (cen : Flapjack.Compiler.Backend.DataSem.Value) (right : List Flapjack.Compiler.Backend.DataSem.Value) (ts2 : Nat) (res : Flapjack.Compiler.Backend.DataSem.Value)
    (vars : List Flapjack.Compiler.Backend.DataSem.Value) (n : Nat) (b : Bool) :
    sptLookup ptr refs = some (.mutBlock tag false left cen right) ∧
        reachableRefs (.block ts2 tag (left ++ [res] ++ right) :: vars)
          (sptInsert ptr (.mutBlock tag true left cen right) refs) n →
      reachableRefs (res :: .refPtr b ptr :: vars) refs n := by
  rintro ⟨found, root, start, rootMem, startMem, path⟩
  rw [refEdge_insert_mutBlock ptr refs tag false left cen right true found] at path
  have viaPtr : ∀ e, e ∈ left ∨ e ∈ right → start ∈ getRefs e →
      reachableRefs (res :: .refPtr b ptr :: vars) refs n := by
    intro e eMem sMem
    refine ⟨.refPtr b ptr, ptr, by simp, by simp [getRefs], .head ?_ path⟩
    simp only [refEdge, found, getRefs, List.mem_flatMap]
    exact ⟨e, by rcases eMem with h | h <;> simp [h], sMem⟩
  rcases List.mem_cons.mp rootMem with rfl | rest
  · simp only [getRefs, List.mem_flatMap] at startMem
    obtain ⟨e, eMem, sMem⟩ := startMem
    simp only [List.append_assoc, List.singleton_append, List.mem_append, List.mem_cons] at eMem
    rcases eMem with inL | rfl | inR
    · exact viaPtr e (Or.inl inL) sMem
    · exact ⟨e, start, List.mem_cons_self, sMem, path⟩
    · exact viaPtr e (Or.inr inR) sMem
  · exact ⟨root, start, by simp [rest], startMem, path⟩

/-- HOL `dest_thunk_insert_MutBlock`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "dest_thunk_insert_MutBlock"]
theorem destThunk_insert_mutBlock (ptr : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (tg : Nat) (fin1 : Bool)
    (l : List Flapjack.Compiler.Backend.DataSem.Value) (c : Flapjack.Compiler.Backend.DataSem.Value) (r : List Flapjack.Compiler.Backend.DataSem.Value) (v : Flapjack.Compiler.Backend.DataSem.Value) (fin2 : Bool) :
    sptLookup ptr refs = some (.mutBlock tg fin1 l c r) →
      destThunk v (sptInsert ptr (.mutBlock tg fin2 l c r) refs) = destThunk v refs := by
  intro found
  cases v with
  | refPtr bit index =>
    by_cases h : index = ptr
    · subst h; simp [destThunk, sptLookup_sptInsert_same, found]
    · simp [destThunk, sptLookup_sptInsert_ne _ _ _ _ h]
  | number _ | block _ _ _ | codePtr _ | word64 _ => simp [destThunk]

/-- HOL `bc_stack_ref_inv_MutBlock_centre`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bc_stack_ref_inv_MutBlock_centre"
  (words_as_type_indexed_bitvec)]
theorem bcStackRefInv_mutBlock_centre {width : Nat} [NeZero width]
    (c : Flapjack.Compiler.Backend.DataToWord.Config) (ts : Nat) (b : Bool) (ptr : Nat)
    (vars : List Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (x : HeapAddress (WordLocW width))
    (xs : List (HeapAddress (WordLocW width)))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (be : Bool)
    (tag : Nat) (left : List Flapjack.Compiler.Backend.DataSem.Value) (cen : Flapjack.Compiler.Backend.DataSem.Value) (right : List Flapjack.Compiler.Backend.DataSem.Value) :
    bcStackRefInv c ts (.refPtr b ptr :: vars) refs (x :: xs, heap, be) ∧
        sptLookup ptr refs = some (.mutBlock tag false left cen right) →
      ∃ (ptr_n : Nat) (zs : List (HeapAddress (WordLocW width))),
        x = .pointer ptr_n (refPtrAnnot c (sptLookup ptr refs)) ∧
        heapLookup ptr_n heap = some (blockRep tag zs) ∧
        zs.length = left.length + 1 + right.length ∧
        bcStackRefInv c ts (cen :: .refPtr b ptr :: vars) refs (holEl left.length zs :: x :: xs, heap, be) := by
  rintro ⟨⟨f, tf, injF, domF, injTf, tsTf, ltTf, beq, unique, rel, refInv⟩, found⟩
  obtain ⟨headInv, restInv⟩ := List.forall₂_cons.mp rel
  have noThunk : ∀ mode value, sptLookup ptr refs ≠ some (.thunk mode value) := by
    intro mode value h; rw [found] at h; cases h
  obtain ⟨⟨p, hp⟩, -, hx⟩ := (valueInv_refPtr_notThunk c b ptr refs x f tf heap noThunk).mp headInv
  have reach : reachableRefs (.refPtr b ptr :: vars) refs ptr :=
    ⟨.refPtr b ptr, ptr, List.mem_cons_self, by simp [getRefs], .refl⟩
  have cell := refInv ptr ⟨reach, ⟨p, hp⟩⟩
  simp only [bcRefInv, hp, found] at cell
  obtain ⟨-, -, zs, heapZs, pairs⟩ := cell
  have lenEq := pairs.length_eq
  simp only [List.length_append, List.length_singleton] at lenEq
  have fp : holFapply f ptr = p := holFapply_of_lookup hp
  refine ⟨p, zs, by rw [hx, fp], heapZs, lenEq, f, tf, injF, domF, injTf, ?_, ltTf, beq, ?_, ?_, ?_⟩
  · intro n hn; exact allTimestamps_cons_subset refs _ cen n (tsTf n hn)
  · exact blocksUnique_subset ts _ _ ⟨unique, allValues_mutBlock_centre ptr refs tag false left cen right _ found⟩
  · refine List.Forall₂.cons ?_ rel
    have idx : left.length < zs.length := by omega
    obtain ⟨-, get⟩ := List.forall₂_iff_get.mp pairs
    have := get left.length idx (by simp)
    rw [holEl_eq_getElem _ _ idx]
    simpa using this
  · intro n ⟨reachN, domN⟩
    exact refInv n ⟨reachableRefs_mutBlock_centre ptr refs tag false left cen right b vars n ⟨found, reachN⟩, domN⟩

/-- HOL `bc_stack_ref_inv_union_del_ins_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bc_stack_ref_inv_union_del_ins_lemma"
  (words_as_type_indexed_bitvec)]
theorem bcStackRefInv_union_del_ins_lemma {width : Nat} [NeZero width]
    (c : Flapjack.Compiler.Backend.DataToWord.Config) (ts : Nat) (vars : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs frame : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (xs : List (HeapAddress (WordLocW width)))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (be : Bool)
    (ptr : Nat) (x : BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value) :
    bcStackRefInv c ts vars (sptUnion refs frame) (xs, heap, be) ∧ sptLookup ptr refs = some x →
      bcStackRefInv c ts vars (sptUnion (sptDelete ptr refs) (sptInsert ptr x frame)) (xs, heap, be) := by
  rintro ⟨inv, found⟩
  apply bcStackRefInv_swapRefs c ts vars _ xs heap be _ ⟨inv, ?_⟩
  intro n
  rw [sptLookup_sptUnion, sptLookup_sptUnion, sptLookup_sptDelete]
  by_cases h : n = ptr
  · subst h; simp [found, sptLookup_sptInsert_same]
  · simp [h, sptLookup_sptInsert_ne _ _ _ _ h]

/-- `mapInjInto` is `INJ (FAPPLY f) (FDOM f)`. Flapjack proof
infrastructure. -/
theorem mapInjInto_iff_holInj (f : HolFiniteMapExact Nat Nat) (t : Nat → Prop) :
    mapInjInto f t ↔ holInj (holFapply f) f.dom t := by
  have dom : ∀ k, mapDomain f k ↔ k ∈ f.dom := by
    intro k
    simp only [mapDomain, HolFiniteMapExact.dom, Set.mem_ofPred_eq]
    cases f.lookup k <;> simp
  simp only [mapInjInto, holInj]
  constructor
  · rintro ⟨a, b⟩
    exact ⟨fun k hk => a k ((dom k).mpr hk), fun x y ⟨hx, hy⟩ => b x y ⟨(dom x).mpr hx, (dom y).mpr hy⟩⟩
  · rintro ⟨a, b⟩
    exact ⟨fun k hk => a k ((dom k).mp hk), fun x y ⟨hx, hy⟩ => b x y ⟨(dom x).mp hx, (dom y).mp hy⟩⟩

/-- HOL `bc_stack_ref_inv_MutBlock_F`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bc_stack_ref_inv_MutBlock_F"
  (words_as_type_indexed_bitvec)]
theorem bcStackRefInv_mutBlock_F {width : Nat} [NeZero width]
    (c : Flapjack.Compiler.Backend.DataToWord.Config) (ts2 : Nat) (res : Flapjack.Compiler.Backend.DataSem.Value) (b : Bool) (ptr : Nat)
    (vars : List Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (zs : List (HeapAddress (WordLocW width)))
    (left : List Flapjack.Compiler.Backend.DataSem.Value) (ptr_n tag : Nat) (right : List Flapjack.Compiler.Backend.DataSem.Value)
    (xs : List (HeapAddress (WordLocW width)))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (be : Bool)
    (cen : Flapjack.Compiler.Backend.DataSem.Value) :
    bcStackRefInv c ts2 (res :: .refPtr b ptr :: vars) refs
        (holEl left.length zs ::
          .pointer ptr_n (.word (ptrBits c tag (left.length + (right.length + 1)))) :: xs, heap, be) ∧
        heapLookup ptr_n heap = some (blockRep tag zs) ∧
        sptLookup ptr refs = some (.mutBlock tag false left cen right) →
      bcStackRefInv c (ts2 + 1) (.block ts2 tag (left ++ [res] ++ right) :: vars)
        (sptInsert ptr (.mutBlock tag true left cen right) refs)
        (.pointer ptr_n (.word (ptrBits c tag (left.length + (right.length + 1)))) :: xs, heap, be) := by
  rintro ⟨⟨f, tf, injF, domF, injTf, tsTf, ltTf, beq, unique, rel, refInv⟩, heapZs, found⟩
  obtain ⟨resInv, ptrRel⟩ := List.forall₂_cons.mp rel
  obtain ⟨ptrInv, varsInv⟩ := List.forall₂_cons.mp ptrRel
  have noThunk : ∀ mode value, sptLookup ptr refs ≠ some (.thunk mode value) := by
    intro mode value h; rw [found] at h; cases h
  obtain ⟨⟨p, hp⟩, -, hx⟩ := (valueInv_refPtr_notThunk c b ptr refs _ f tf heap noThunk).mp ptrInv
  have fp : holFapply f ptr = p := holFapply_of_lookup hp
  rw [fp] at hx
  simp only [HeapAddress.pointer.injEq] at hx
  obtain ⟨rfl, -⟩ := hx
  have reach : reachableRefs (res :: .refPtr b ptr :: vars) refs ptr :=
    ⟨.refPtr b ptr, ptr, by simp, by simp [getRefs], .refl⟩
  have cell := refInv ptr ⟨reach, ⟨ptr_n, hp⟩⟩
  simp only [bcRefInv, hp, found] at cell
  obtain ⟨gcOk, notStamped, zs', heapZs', pairs⟩ := cell
  have zsEq : zs' = zs := by
    rw [heapZs] at heapZs'
    simp only [blockRep, Option.some.injEq, HeapElement.dataElement.injEq] at heapZs'
    exact heapZs'.1.symm
  rw [zsEq] at pairs
  have lenEq := pairs.length_eq
  simp only [List.length_append, List.length_singleton] at lenEq
  have fresh : ts2 ∉ tf.dom := by
    intro h
    have : mapDomain tf ts2 := by
      simp only [HolFiniteMapExact.dom, Set.mem_ofPred_eq] at h
      cases e : tf.lookup ts2 with
      | none => exact absurd e h
      | some v => exact ⟨v, e⟩
    exact absurd (ltTf ts2 this) (by omega)
  set tf' := tf.updateEq (ts2, ptr_n) with htf'
  set refs' := sptInsert ptr (.mutBlock tag true left cen right) refs with hrefs'
  have tfLookup : ∀ k, tf'.lookup k = if k = ts2 then some ptr_n else tf.lookup k := by
    intro k; simp [htf', HolFiniteMapExact.updateEq, FUPDATE_HOL]
  have sub : tf.submap tf' := by
    intro k v h
    rw [tfLookup]
    have : k ≠ ts2 := by
      rintro rfl
      exact fresh (by simp [HolFiniteMapExact.dom, h])
    simp [this, h]
  have transfer : ∀ v a, valueInv c v refs (a, f, tf, heap) → valueInv c v refs' (a, f, tf', heap) :=
    fun v a h => valueInv_submap c refs' f f tf tf' heap heap v a
      ⟨HolFiniteMapExact.submap_refl f, sub, fun _ _ => rfl,
        valueInv_mutBlockFin c v refs a f tf heap ptr tag false true left cen right ⟨h, found⟩⟩
  have refsLookup : ∀ i, sptLookup i refs' =
      if i = ptr then some (.mutBlock tag true left cen right) else sptLookup i refs := by
    intro i
    by_cases h : i = ptr
    · subst h; simp [hrefs', sptLookup_sptInsert_same]
    · simp [hrefs', sptLookup_sptInsert_ne _ _ _ _ h, h]
  have ptrData : isSomeDataElement (heapLookup ptr_n heap) := ⟨_, _, _, heapZs⟩
  have notRange : ¬ ∃ k, tf.lookup k = some ptr_n := by
    rintro ⟨k, hk⟩
    exact notStamped trivial ⟨k, ⟨ptr_n, hk⟩, holFapply_of_lookup hk⟩
  have blockInv : valueInv c (.block ts2 tag (left ++ [res] ++ right)) refs'
      (.pointer ptr_n (.word (ptrBits c tag (left.length + (right.length + 1)))), f, tf', heap) := by
    apply (valueInv_nonemptyBlock c ts2 tag _ refs' _ f tf' heap (by simp)).mpr
    refine ⟨ptr_n, zs, ?_, by simp [tfLookup], by congr 3; omega, heapZs⟩
    rw [List.forall₂_iff_get] at pairs ⊢
    obtain ⟨-, get⟩ := pairs
    refine ⟨by simp; omega, ?_⟩
    intro i h1 h2
    by_cases hi : i = left.length
    · subst hi
      have := resInv
      rw [holEl_eq_getElem _ _ (by omega)] at this
      simpa using transfer _ _ this
    · have := get i h2 (by simpa using h1)
      apply transfer
      have eqv : (left ++ [res] ++ right).get ⟨i, h1⟩ = (left ++ [cen] ++ right).get ⟨i, by simpa using h1⟩ := by
        simp only [List.get_eq_getElem, List.append_assoc, List.singleton_append, List.getElem_append]
        split
        · rfl
        · simp only [List.getElem_cons]
          split
          · omega
          · rfl
      rw [eqv]; exact this
  refine ⟨f, tf', injF, ?_, ?_, ?_, ?_, beq, ?_, List.Forall₂.cons blockInv (varsInv.imp fun v a h => transfer v a h), ?_⟩
  · intro n hn
    rw [refsLookup]
    split
    · exact ⟨_, rfl⟩
    · exact domF n hn
  · rw [mapInjInto_iff_holInj] at injTf ⊢
    exact inj_fupdate tf _ ts2 ptr_n ⟨injTf, fresh, notRange, ptrData⟩
  · intro n ⟨v, hv⟩
    rw [tfLookup] at hv
    split at hv
    · subst n
      exact ⟨.block ts2 tag (left ++ [res] ++ right), Or.inr (by simp), by simp [valueTimestamps]⟩
    · apply allTimestamps_subset_ts refs refs' (res :: .refPtr b ptr :: vars) _ _ n (tsTf n ⟨v, hv⟩)
      rintro x t ⟨(⟨i, cell, hcell, hfind⟩ | inStack), ht⟩
      · by_cases hi : i = ptr
        · subst hi
          rw [found] at hcell
          cases hcell
          exact ⟨x, Or.inl ⟨i, .mutBlock tag true left cen right, by rw [refsLookup, if_pos rfl],
            by simpa [findRef] using hfind⟩, ht⟩
        · exact ⟨x, Or.inl ⟨i, cell, by rw [refsLookup, if_neg hi]; exact hcell, hfind⟩, ht⟩
      · simp only [List.mem_cons] at inStack
        rcases inStack with rfl | rfl | inVars
        · refine ⟨.block ts2 tag (left ++ [x] ++ right), Or.inr (by simp), ?_⟩
          simp only [valueTimestamps, List.mem_cons, List.mem_flatMap]
          exact Or.inr ⟨x, by simp, ht⟩
        · simp [valueTimestamps] at ht
        · exact ⟨x, Or.inr (by simp [inVars]), ht⟩
  · intro n ⟨v, hv⟩
    rw [tfLookup] at hv
    split at hv
    · omega
    · have := ltTf n ⟨v, hv⟩; omega
  · apply blocksUnique_subset (ts2 + 1) _ _
      ⟨blocksUnique_insert ts2 _ tag (left ++ [res] ++ right) unique, ?_⟩
    exact allValues_mutBlock_T ptr refs tag left cen right ts2 res vars b found
  · intro n ⟨reachN, domN⟩
    have old := refInv n ⟨reachableRefs_mutBlock_T ptr refs tag left cen right ts2 res vars n b ⟨found, reachN⟩, domN⟩
    obtain ⟨fn, hfn⟩ := domN
    simp only [bcRefInv, hfn] at old ⊢
    rw [refsLookup]
    by_cases hn : n = ptr
    · subst hn
      rw [if_pos rfl]
      rw [found] at old
      obtain ⟨g, -, zs2, h2, pairs2⟩ := old
      exact ⟨g, by simp, zs2, h2, pairs2.imp fun a v h => transfer v a h⟩
    · rw [if_neg hn]
      revert old
      cases hcell : sptLookup n refs with
      | none => simp
      | some cell =>
        cases cell with
        | valueArray values =>
          rintro ⟨addrs, h1, h2⟩
          exact ⟨addrs, h1, h2.imp fun a v h => transfer v a h⟩
        | byteArray cmp bytes => exact id
        | thunk mode value =>
          rintro ⟨addr, h1, h2, h3⟩
          refine ⟨addr, h1, ?_, transfer _ _ h3⟩
          intro ev
          rw [hrefs', destThunk_insert_mutBlock ptr refs tag false left cen right value true found]
          exact h2 ev
        | mutBlock tag' fin' l' c' r' =>
          rintro ⟨g, ns, addrs, h1, h2⟩
          refine ⟨g, ?_, addrs, h1, h2.imp fun a v h => transfer v a h⟩
          rintro nf ⟨stamp, ⟨sv, hs⟩, happ⟩
          rw [tfLookup] at hs
          split at hs
          · subst stamp
            have : holFapply tf' ts2 = ptr_n := holFapply_of_lookup (by simp [tfLookup])
            rw [this] at happ
            exact hn (injF.2 n ptr ⟨⟨_, hfn⟩, ⟨_, hp⟩⟩
              (by rw [holFapply_of_lookup hfn, holFapply_of_lookup hp, happ]))
          · apply ns nf ⟨stamp, ⟨sv, hs⟩, ?_⟩
            have e1 : holFapply tf' stamp = sv := holFapply_of_lookup (by rw [tfLookup, if_neg ‹_›]; exact hs)
            rw [holFapply_of_lookup hs, ← e1]; exact happ

/-- HOL `bc_stack_ref_inv_FinaliseCons_lemma`. HOL's universally quantified
`w : α` does not occur in the statement; it is kept as the binder `_w` at an
independent type `α`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bc_stack_ref_inv_FinaliseCons_lemma"
  (words_as_type_indexed_bitvec)]
theorem bcStackRefInv_finaliseCons_lemma {width : Nat} [NeZero width] {α : Type}
    (c : Flapjack.Compiler.Backend.DataToWord.Config)
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (be : Bool) :
    ∀ (v : Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (ts_opt : Option Nat) (v' : Flapjack.Compiler.Backend.DataSem.Value)
      (refs' : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (ts' : Option Nat) (ts : Nat) (vars : List Flapjack.Compiler.Backend.DataSem.Value) (_w : α)
      (frame : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (x : HeapAddress (WordLocW width))
      (xs : List (HeapAddress (WordLocW width))),
      finaliseCons v refs ts_opt = some (v', refs', ts') ∧ ts_opt = some ts ∧
          bcStackRefInv c ts (v :: vars) (sptUnion refs frame) (x :: xs, heap, be) →
        ts'.isSome = true ∧
          bcStackRefInv c (holThe ts') (v' :: vars) (sptUnion refs' frame) (x :: xs, heap, be) := by
  intro v refs ts_opt
  induction v, refs using finaliseCons.induct (timestamp := ts_opt) with
  | case1 refs bit p tag left child right found =>
      rintro v' refs' ts' ts vars w frame x xs ⟨h, -, -⟩
      rw [finaliseCons_refPtr_eq, found] at h
      simp at h
  | case2 refs bit p tag fin left child right found nfin noneEq _ =>
      rintro v' refs' ts' ts vars w frame x xs ⟨h, -, -⟩
      rw [finaliseCons_refPtr_eq, found] at h
      simp [nfin, noneEq] at h
  | case3 refs bit p tag fin left child right found nfin result rest next eq ih =>
      rintro v' refs' ts' ts vars w frame x xs ⟨h, rfl, inv⟩
      rw [finaliseCons_refPtr_eq, found] at h
      simp only [nfin, eq, if_false, Bool.false_eq_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Bool.not_eq_true] at nfin
      subst nfin
      have foundU : sptLookup p (sptUnion refs frame) = some (.mutBlock tag false left child right) := by
        rw [sptLookup_sptUnion, found]
      obtain ⟨ptr_n, zs, hx, heapZs, lenZs, inv2⟩ :=
        bcStackRefInv_mutBlock_centre c ts bit p vars _ x xs heap be tag left child right ⟨inv, foundU⟩
      have inv3 := bcStackRefInv_union_del_ins_lemma c ts _ refs frame _ heap be p _ ⟨inv2, found⟩
      obtain ⟨someNext, inv4⟩ := ih result rest next ts (.refPtr bit p :: vars) w
        (sptInsert p (.mutBlock tag false left child right) frame) _ _ ⟨eq, rfl, inv3⟩
      have restNone : sptLookup p rest = none :=
        finaliseCons_none p child (sptDelete p refs) (some ts) result rest next
          ⟨eq, by rw [sptLookup_sptDelete]; simp⟩
      have foundU2 : sptLookup p (sptUnion rest (sptInsert p (.mutBlock tag false left child right) frame)) =
          some (.mutBlock tag false left child right) := by
        rw [sptLookup_sptUnion, restNone]; simp [sptLookup_sptInsert_same]
      rw [foundU] at hx
      simp only [refPtrAnnot] at hx
      have lenEq : left.length + 1 + right.length = left.length + (right.length + 1) := by omega
      rw [lenEq] at hx
      subst hx
      have inv5 := bcStackRefInv_mutBlock_F c (holThe next) result bit p vars _ zs left ptr_n tag right xs heap be
        child ⟨inv4, heapZs, foundU2⟩
      obtain ⟨k, rfl⟩ := Option.isSome_iff_exists.mp someNext
      refine ⟨by simp, ?_⟩
      apply bcStackRefInv_swapRefs c _ _ _ _ heap be _ ⟨inv5, ?_⟩
      intro n
      by_cases hn : n = p
      · subst hn
        rw [sptLookup_sptInsert_same, sptLookup_sptUnion, sptLookup_sptInsert_same]
      · rw [sptLookup_sptInsert_ne _ _ _ _ hn, sptLookup_sptUnion, sptLookup_sptUnion,
          sptLookup_sptInsert_ne _ _ _ _ hn, sptLookup_sptInsert_ne _ _ _ _ hn]
  | case4 refs bit p val notMut found =>
      rintro v' refs' ts' ts vars w frame x xs ⟨h, rfl, inv⟩
      rw [finaliseCons_refPtr_eq, found] at h
      cases val with
      | mutBlock tag fin left child right => exact (notMut tag fin left child right rfl).elim
      | _ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, inv⟩
  | case5 refs bit p found =>
      rintro v' refs' ts' ts vars w frame x xs ⟨h, -, -⟩
      rw [finaliseCons_refPtr_eq, found] at h
      simp at h
  | case6 refs other notRef =>
      rintro v' refs' ts' ts vars w frame x xs ⟨h, rfl, inv⟩
      cases other with
      | refPtr bit p => exact (notRef bit p rfl).elim
      | _ =>
        simp only [finaliseCons, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, inv⟩

/-- HOL `memory_rel_FinaliseCons`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_FinaliseCons"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_finaliseCons {width : Nat} [NeZero width]
    (c : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat) (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) (v : Flapjack.Compiler.Backend.DataSem.Value) (w : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (v' : Flapjack.Compiler.Backend.DataSem.Value) (refs' : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (ts' : Option Nat) :
    memoryRel c be ts refs sp st m dm ((v, w) :: vars) ∧
        finaliseCons v refs (some ts) = some (v', refs', ts') →
      ts'.isSome = true ∧ memoryRel c be (holThe ts') refs' sp st m dm ((v', w) :: vars) := by
  rintro ⟨⟨heap, limit, a, sp0, sp1, gens, store, ⟨roots, ⟨ok1, ok2, ok3, ok4, inv⟩, addrs⟩, bound, space⟩, run⟩
  cases roots with
  | nil => simp at addrs
  | cons x xs =>
    have inv' : bcStackRefInv c ts (v :: vars.map Prod.fst) (sptUnion refs .ln) (x :: xs, heap, be) := by
      apply bcStackRefInv_swapRefs c ts _ refs _ heap be _ ⟨inv, ?_⟩
      intro n; rw [sptLookup_sptUnion]; cases sptLookup n refs <;> simp [sptLookup]
    obtain ⟨isSome, inv2⟩ := bcStackRefInv_finaliseCons_lemma (α := Unit) c heap be v refs (some ts) v' refs' ts'
      ts (vars.map Prod.fst) () .ln x xs ⟨run, rfl, inv'⟩
    refine ⟨isSome, heap, limit, a, sp0, sp1, gens, store, ⟨x :: xs, ⟨ok1, ok2, ok3, ok4, ?_⟩, addrs⟩, bound, space⟩
    apply bcStackRefInv_swapRefs c _ _ _ _ heap be _ ⟨inv2, ?_⟩
    intro n; rw [sptLookup_sptUnion]; cases sptLookup n refs' <;> simp [sptLookup]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

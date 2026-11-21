module

public import Flapjack.Compiler.Backend.WordBignum.Proofs.HeapLemmas
public import Flapjack.Compiler.Backend.WordBignum.Proofs.WordSemClauses
public import Flapjack.Pancake.Semantics.LoopProps.NestedSeqExact

@[expose] public section

/-! The call-frame lemmas of
`cakeml/compiler/backend/proofs/word_bignumProofScript.sml`: the singleton
return environment of a compiled loop call, and the evaluation of the
register save/load sequences used by compiled `Rec` calls. -/

namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack
open Flapjack.WordSemStateFiniteExact.BignumClauses

namespace CallFrameSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
fields named by `evaluate_SaveRegs`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Same-module canonical roundtrip witness for the mini-language state
carrier, required by the relation qualifier on `evaluate_LoadRegs`. -/
theorem holFmapAsFiniteSupportRelationWitness_MiniState {width : Nat} [NeZero width] :
    (∀ s : MiniStateBroad width, (MiniState.ofBroad s).toBroad = s) ∧
      (∀ s : MiniState width, MiniState.ofBroad s.toBroad = s) :=
  Flapjack.Compiler.Backend.WordBignum.holFmapAsFiniteSupportWitness

/-- Same-module canonical roundtrip witness for the `wordSem` state carrier,
required by the relation qualifier on `evaluate_LoadRegs`. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact {width : Nat}
    [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CallFrameSupport

/-- HOL `env_to_list_insert_0_LN` (`word_bignumProofScript.sml:356`): the
environment holding only the return location at name `0` is listed as that
single entry, and the permutation sequence is shifted. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "env_to_list_insert_0_LN"
  (words_as_type_indexed_bitvec)]
theorem envToList_insert_0_LN {width : Nat} [NeZero width] (retVal : WordLocW width)
    (p : Nat → Nat → Nat) :
    wordSemEnvToList (sptInsert 0 retVal (.ln : Spt (WordLocW width))) p =
      ([(0, retVal)], fun n => p (n + 1)) := by
  have hl : sptToAList (sptInsert 0 retVal (.ln : Spt (WordLocW width))) = [(0, retVal)] := by
    simp [sptToAList, sptFoldi]
  have hs : Basis.Pure.MlList.sort wordSemKeyValCompare [(0, retVal)] = [(0, retVal)] := by
    simp [Basis.Pure.MlList.sort, Basis.Pure.MlList.mergesortTail, Basis.Pure.MlList.mergesortNTail]
  have hr : wordSemListRearrange (p 0) [(0, retVal)] = [(0, retVal)] := by
    unfold wordSemListRearrange
    split
    · simp
    · rfl
  simp only [wordSemEnvToList, hl, hs, hr]

/-- Flapjack-only helper for `evaluate_LoadRegs`: inserting at a key outside the
updated key list commutes with `list_update`. -/
theorem listUpdateSpt_insert_comm {α : Type} [Nonempty α] (k : Nat) (v : α) :
    ∀ (xs : List Nat) (ys : List α) (t : Spt α), k ∉ xs →
      listUpdateSpt xs ys (sptInsert k v t) = sptInsert k v (listUpdateSpt xs ys t)
  | [], _, _, _ => rfl
  | x :: xs, y :: ys, t, h => by
    simp only [listUpdateSpt]
    rw [listUpdateSpt_insert_comm k v xs ys t (fun hm => h (List.mem_cons_of_mem _ hm))]
    exact sptInsert_comm x k y v _ (fun he => h (he ▸ List.mem_cons_self))
  | x :: xs, [], t, h => by
    simp only [listUpdateSpt]
    rw [listUpdateSpt_insert_comm k v xs [] t (fun hm => h (List.mem_cons_of_mem _ hm))]
    exact sptInsert_comm x k _ v _ (fun he => h (he ▸ List.mem_cons_self))

/-- HOL `evaluate_LoadRegs` (`word_bignumProofScript.sml:542`): loading the
saved registers from their temporaries is the same as writing their values,
through HOL's `list_update`, into the locals at the shifted names. HOL's
`EVERY` is read as membership and `ALL_DISTINCT` as `List.Nodup`; `LIST_REL`
is `List.Forall₂`; HOL's one conjunction premise is one hypothesis. The
statement's free variables `s1`, `cs2`, `t0`, `frame` and `p` are explicit
parameters. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "evaluate_LoadRegs"
  (fmap_as_finite_support_relation :=
    [MiniState.regs, WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluate_LoadRegs {width : Nat} [NeZero width] {β : Type} {C F : Type}
    (s1 : MiniState width)
    (cs2 : β × List (Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width)))
    (t0 : WordSemStateFiniteExact width C F)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (p : WordLangProgHOL (BitVec width)) :
    ∀ (saveRegs : List Nat) (vals : List (BitVec width)) (t1 : WordSemStateFiniteExact width C F),
      stateRel s1 t1 cs2 t0 frame ∧ (∀ n ∈ saveRegs, n < 25) ∧ saveRegs.Nodup ∧
          List.Forall₂ (fun n v => s1.regs.lookup n = some v) saveRegs vals →
        WordSemStateFiniteExact.evaluate (loadRegs saveRegs p) t1 =
          WordSemStateFiniteExact.evaluate p
            { t1 with locals :=
                listUpdateSpt (saveRegs.map (fun n => n + 2)) (vals.map WordLocW.word) t1.locals }
  | [], vals, t1, ⟨_, _, _, hrel⟩ => by
    cases hrel
    simp [loadRegs, listUpdateSpt]
  | h :: rest, vals, t1, ⟨hstate, hlt, hnd, hrel⟩ => by
    cases hrel with
    | cons hv hrest =>
      rename_i v vs
      have hstore := (hstate.2.2.1 h v hv).2
      simp only [loadRegs]
      rw [evaluate_seq, evaluate_get]
      simp only [WordSemStateFiniteExact.getStore, hstore]
      have ih := evaluate_LoadRegs s1 cs2 t0 frame p rest vs
        (WordSemStateFiniteExact.setVar (h + 2) (.word v) t1)
        ⟨hstate, fun n hn => hlt n (List.mem_cons_of_mem _ hn), (List.nodup_cons.mp hnd).2, hrest⟩
      rw [ih]
      simp only [WordSemStateFiniteExact.setVar, List.map_cons, listUpdateSpt]
      have hnot : h + 2 ∉ rest.map (fun n => n + 2) := by
        intro hm
        obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
        have : a = h := by omega
        exact (List.nodup_cons.mp hnd).1 (this ▸ ha)
      rw [listUpdateSpt_insert_comm _ _ _ _ _ hnot]

/-- HOL `evaluate_SaveRegs` (`word_bignumProofScript.sml:597`): saving the
registers stored in the shifted locals writes them to their temporaries, as
HOL's `list_store` describes. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "evaluate_SaveRegs"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_SaveRegs {width : Nat} [NeZero width] {C F : Type} :
    ∀ (saves : List Nat) (t7 : WordSemStateFiniteExact width C F) (vals : List (BitVec width)),
      List.Forall₂ (fun n v => sptLookup (n + 2) t7.locals = some (.word v)) saves vals ∧
          saves.Nodup ∧ (∀ n ∈ saves, n < 25) →
        WordSemStateFiniteExact.evaluate (saveRegs saves) t7 =
          (none, { t7 with store := listStore saves (vals.map WordLocW.word) t7.store })
  | [], t7, vals, ⟨hrel, _, _⟩ => by
    cases hrel
    simp [saveRegs, evaluate_skip, listStore]
  | h :: rest, t7, vals, ⟨hrel, hnd, hlt⟩ => by
    cases hrel with
    | cons hv hrest =>
      rename_i v vs
      simp only [saveRegs]
      rw [evaluate_seq, evaluate_set]
      simp only [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, hv]
      have hne : ¬ ((WordStore.temp (BitVec.ofNat 5 h) : WordStoreHOL) = .handler ∨
          (WordStore.temp (BitVec.ofNat 5 h) : WordStoreHOL) = .bitmapBase) := by simp
      rw [if_neg hne]
      have ih := evaluate_SaveRegs rest
        (WordSemStateFiniteExact.setStore (.temp (BitVec.ofNat 5 h)) (.word v) t7) vs
        ⟨hrest, (List.nodup_cons.mp hnd).2, fun n hn => hlt n (List.mem_cons_of_mem _ hn)⟩
      simp only
      rw [ih]
      have hcomm := listStore_FUPDATE rest t7.store (vs.map WordLocW.word) h v
        ⟨(List.nodup_cons.mp hnd).1, hlt h List.mem_cons_self,
          fun n hn => hlt n (List.mem_cons_of_mem _ hn)⟩
      simp [WordSemStateFiniteExact.setStore, hcomm, listStore, holHd]

end Flapjack.Compiler.Backend.WordBignum

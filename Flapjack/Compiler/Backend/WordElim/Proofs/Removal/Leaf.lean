module

public import Flapjack.Compiler.Backend.WordElim.Proofs.Removal.Basic

@[expose] public section

/-!
# `word_removal_lemma`: the leaf cases

The cases of HOL `word_removal_lemma` (`word_elimProofScript.sml:931-1601`) for
statements without a sub-program: `Skip`, `Alloc`, `StoreConsts`, `Move`, `Inst`,
`Assign`, `Get`, `Set`, `OpCurrHeap`, `Store`, `Tick`, `Return`, `Raise`,
`Break`, `Continue`, `LocValue`, `Install`, `CodeBufferWrite`,
`DataBufferWrite`, `FFI` and `ShareInst`.  Each piece is HOL's statement
(`WordRemovalGoal`) for that constructor, with every constructor argument and the
state universally quantified; the leaf cases have no induction hypothesis.
-/

namespace Flapjack.Compiler.Backend.WordElim
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordProps

namespace WordElimRemovalLeafSupport
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end WordElimRemovalLeafSupport

section LeafCases
variable {width : Nat} [NeZero width] {C F : Type}

theorem destResultLoc_none (n : Nat) : ¬ destResultLoc (width := width) none n := id

/-- Case `Skip` of HOL `word_removal_lemma` (`Resume word_removal_lemma[Skip]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_Skip :
    ∀ (state : WordSemStateFiniteExact width C F), WordRemovalGoal .skip state := by
  intro state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  cases hev
  exact ⟨LocsWithin.refl _, fun n hn => hn.elim⟩

/-- Case `Alloc` of HOL `word_removal_lemma` (`Resume word_removal_lemma[Alloc]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_Alloc :
    ∀ (n : Nat) (names : WordLangCutsetsHOL) (state : WordSemStateFiniteExact width C F),
      WordRemovalGoal (.alloc n names) state := by
  intro n names state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  split at hev
  · obtain ⟨hl, hr⟩ := alloc_locsWithin _ _ _ _ _ herr hg hev
    refine ⟨hl, ?_⟩
    rcases hr with rfl | rfl <;> intro n hn <;> exact hn.elim
  · cases hev; exact absurd rfl herr

/-- Case `StoreConsts` of HOL `word_removal_lemma`
    (`Resume word_removal_lemma[StoreConsts]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_StoreConsts :
    ∀ (t1 t2 addr offset : Nat) (words : List (Bool × BitVec width))
      (state : WordSemStateFiniteExact width C F),
      WordRemovalGoal (.storeConsts t1 t2 addr offset words) state := by
  intro t1 t2 addr offset words state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  split at hev
  · split at hev
    · cases hev; exact absurd rfl herr
    · cases hev
      refine ⟨?_, fun n hn => hn.elim⟩
      refine (locsWithin_setVar _ _ _ (locOf_word _ _)).trans ?_
      refine (locsWithin_setVar _ _ _ (locOf_word _ _)).trans ?_
      refine (locsWithin_unsetVar _ _).trans ?_
      refine (locsWithin_unsetVar _ _).trans ?_
      exact locsWithin_constWrites _ _ _ _
  · cases hev; exact absurd rfl herr

/-- Case `Move` of HOL `word_removal_lemma` (`Resume word_removal_lemma[Move]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_Move :
    ∀ (pri : Nat) (moves : List (Nat × Nat)) (state : WordSemStateFiniteExact width C F),
      WordRemovalGoal (.move pri moves) state := by
  intro pri moves state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  split at hev
  · split at hev
    · cases hev; exact absurd rfl herr
    · rename_i vs hvs
      cases hev
      exact ⟨locsIn_setVars _ _ _ (locsIn_self _) (locOf_getVars _ _ hvs),
        fun n hn => hn.elim⟩
  · cases hev; exact absurd rfl herr

/-- Case `Inst` of HOL `word_removal_lemma` (`Resume word_removal_lemma[Inst]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_Inst :
    ∀ (i : WordLangInst (BitVec width)) (state : WordSemStateFiniteExact width C F),
      WordRemovalGoal (.inst i) state := by
  intro i state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  split at hev
  · rename_i s2 hi
    cases hev
    exact ⟨inst_locsWithin _ _ _ hi, fun n hn => hn.elim⟩
  · cases hev; exact absurd rfl herr

/-- Case `Assign` of HOL `word_removal_lemma` (`Resume word_removal_lemma[Assign]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_Assign :
    ∀ (v : Nat) (exp : WordLangExpHOL (BitVec width)) (state : WordSemStateFiniteExact width C F),
      WordRemovalGoal (.assign v exp) state := by
  intro v exp state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  split at hev
  · cases hev; exact absurd rfl herr
  · rename_i w hw
    cases hev
    exact ⟨locsWithin_setVar _ _ _ (wordExp_locOf _ _ hw), fun n hn => hn.elim⟩

/-- Case `Get` of HOL `word_removal_lemma` (`Resume word_removal_lemma[Get]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_Get :
    ∀ (v : Nat) (name : WordStoreHOL) (state : WordSemStateFiniteExact width C F),
      WordRemovalGoal (.get v name) state := by
  intro v name state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  split at hev
  · cases hev; exact absurd rfl herr
  · rename_i w hw
    cases hev
    exact ⟨locsWithin_setVar _ _ _ (wordExp_locOf _ (.lookup name) (by simpa [wordExp] using hw)),
      fun n hn => hn.elim⟩

/-- Case `Set` of HOL `word_removal_lemma` (`Resume word_removal_lemma[Set]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_Set :
    ∀ (v : WordStoreHOL) (exp : WordLangExpHOL (BitVec width))
      (state : WordSemStateFiniteExact width C F),
      WordRemovalGoal (.set v exp) state := by
  intro v exp state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  split at hev
  · cases hev; exact absurd rfl herr
  · split at hev
    · cases hev; exact absurd rfl herr
    · rename_i w hw
      cases hev
      exact ⟨locsWithin_setStore _ _ _ (wordExp_locOf _ _ hw), fun n hn => hn.elim⟩

/-- Case `OpCurrHeap` of HOL `word_removal_lemma`
    (`Resume word_removal_lemma[OpCurrHeap]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_OpCurrHeap :
    ∀ (b : BinOp) (dst src : Nat) (state : WordSemStateFiniteExact width C F),
      WordRemovalGoal (.opCurrHeap b dst src) state := by
  intro b dst src state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  split at hev
  · cases hev; exact absurd rfl herr
  · rename_i w hw
    cases hev
    exact ⟨locsWithin_setVar _ _ _ (wordExp_locOf _ _ hw), fun n hn => hn.elim⟩

/-- Case `Store` of HOL `word_removal_lemma` (`Resume word_removal_lemma[Store]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_Store :
    ∀ (exp : WordLangExpHOL (BitVec width)) (v : Nat) (state : WordSemStateFiniteExact width C F),
      WordRemovalGoal (.store exp v) state := by
  intro exp v state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  split at hev
  · split at hev
    · rename_i hw _ s2 hst
      cases hev
      exact ⟨locsWithin_memStore _ _ _ _ (locOf_getVar _ _ hw) hst, fun n hn => hn.elim⟩
    · cases hev; exact absurd rfl herr
  · cases hev; exact absurd rfl herr

/-- Case `Tick` of HOL `word_removal_lemma` (`Resume word_removal_lemma[Tick]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_Tick :
    ∀ (state : WordSemStateFiniteExact width C F), WordRemovalGoal .tick state := by
  intro state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  split at hev
  · cases hev; exact ⟨locsWithin_flushState _ _, fun n hn => hn.elim⟩
  · cases hev; exact ⟨LocsWithin.refl _, fun n hn => hn.elim⟩

/-- Case `Return` of HOL `word_removal_lemma` (`Resume word_removal_lemma[Return]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_Return :
    ∀ (n : Nat) (ms : List Nat) (state : WordSemStateFiniteExact width C F),
      WordRemovalGoal (.return n ms) state := by
  intro n ms state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  split at hev
  · rename_i l1 l2 ys _ hys
    cases hev
    refine ⟨locsWithin_flushState _ _, ?_⟩
    rintro m ⟨value, hmem, hv⟩
    obtain ⟨o, rfl⟩ := (destWordLoc_eq_some_iff value m).mp hv
    exact locOf_getVars _ _ hys _ hmem m o rfl
  · cases hev; exact absurd rfl herr

/-- Case `Raise` of HOL `word_removal_lemma` (`Resume word_removal_lemma[Raise]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_Raise :
    ∀ (n : Nat) (state : WordSemStateFiniteExact width C F),
      WordRemovalGoal (.raise n) state := by
  intro n state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  split at hev
  · cases hev; exact absurd rfl herr
  · rename_i w hw
    split at hev
    · cases hev; exact absurd rfl herr
    · rename_i s2 l1 l2 hj
      cases hev
      refine ⟨jumpExc_locsWithin _ _ _ _ hj, ?_⟩
      intro m hm
      cases w with
      | word x => exact hm.elim
      | loc b o =>
        have hm' : m = b := hm
        subst hm'
        exact locOf_getVar _ _ hw m o rfl

/-- Case `Break` of HOL `word_removal_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_Break :
    ∀ (k : Nat) (state : WordSemStateFiniteExact width C F), WordRemovalGoal (.break k) state := by
  intro k state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  cases hev
  exact ⟨LocsWithin.refl _, fun n hn => hn.elim⟩

/-- Case `Continue` of HOL `word_removal_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_Continue :
    ∀ (k : Nat) (state : WordSemStateFiniteExact width C F),
      WordRemovalGoal (.continue k) state := by
  intro k state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  cases hev
  exact ⟨LocsWithin.refl _, fun n hn => hn.elim⟩

/-- Case `CodeBufferWrite` of HOL `word_removal_lemma`
    (`Resume word_removal_lemma[CodeBufferWrite]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_CodeBufferWrite :
    ∀ (r1 r2 : Nat) (state : WordSemStateFiniteExact width C F),
      WordRemovalGoal (.codeBufferWrite r1 r2) state := by
  intro r1 r2 state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  repeat' split at hev
  all_goals first
    | (cases hev; exact absurd rfl herr)
    | (cases hev; exact ⟨fun _ h => h, fun n hn => hn.elim⟩)

/-- Case `DataBufferWrite` of HOL `word_removal_lemma`
    (`Resume word_removal_lemma[DataBufferWrite]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_DataBufferWrite :
    ∀ (r1 r2 : Nat) (state : WordSemStateFiniteExact width C F),
      WordRemovalGoal (.dataBufferWrite r1 r2) state := by
  intro r1 r2 state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  repeat' split at hev
  all_goals first
    | (cases hev; exact absurd rfl herr)
    | (cases hev; exact ⟨fun _ h => h, fun n hn => hn.elim⟩)

/-- Case `FFI` of HOL `word_removal_lemma` (`Resume word_removal_lemma[FFI]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_FFI :
    ∀ (ffiIndex : Basis.Pure.MlString.MlString) (ptr1 len1 ptr2 len2 : Nat)
      (names : WordLangCutsetsHOL) (state : WordSemStateFiniteExact width C F),
      WordRemovalGoal (.ffi ffiIndex ptr1 len1 ptr2 len2 names) state := by
  intro ffiIndex ptr1 len1 ptr2 len2 names state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  repeat' split at hev
  all_goals first
    | (cases hev; exact absurd rfl herr)
    | (cases hev; exact ⟨locsWithin_flushState _ _, fun n hn => hn.elim⟩)
    | skip
  have henv := ‹wordSemCutEnv names state.locals = some _›
  simp only [Prod.mk.injEq] at hev
  obtain ⟨rfl, rfl⟩ := hev
  refine ⟨?_, fun n hn => hn.elim⟩
  intro n hn
  rw [sptMem_findLocState] at hn
  rcases hn with h | h
  · exact (sptMem_findLocState state n).mpr (Or.inl (locsWithin_cutEnv_locals state names henv n h))
  · exact locsWithin_writeBytearray state _ _ n ((sptMem_findLocState _ n).mpr (Or.inr h))

/-- Case `ShareInst` of HOL `word_removal_lemma` (`Resume word_removal_lemma[ShareInst]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_ShareInst :
    ∀ (op : WordMemOp) (v : Nat) (exp : WordLangExpHOL (BitVec width))
      (state : WordSemStateFiniteExact width C F),
      WordRemovalGoal (.shareInst op v exp) state := by
  intro op v exp state
  refine removal_leaf _ _ rfl fun res s1 hev herr hg => ?_
  rw [evaluate] at hev
  split at hev
  · cases op <;>
      simp only [shareInst, shMemSetVar, shMemLoad, shMemLoadByte, shMemLoad16, shMemLoad32,
        shMemStore, shMemStoreByte, shMemStore16, shMemStore32] at hev <;>
      (repeat' split at hev) <;>
      first
        | (cases hev; exact absurd rfl herr)
        | (cases hev; exact ⟨locsWithin_flushState _ _, fun n hn => hn.elim⟩)
        | (cases hev; exact ⟨fun _ h => h, fun n hn => hn.elim⟩)
        | (cases hev; exact ⟨locsWithin_setVar _ _ _ (locOf_word _ _), fun n hn => hn.elim⟩)
  · cases hev; exact absurd rfl herr

end LeafCases

section LocValueInstall
variable {width : Nat} [NeZero width] {C F : Type}

/-- Related code tables agree on the membership of a reachable label. -/
theorem codeRel_mem {reachable : NumSet} {c d : Spt (Nat × WordLangProgHOL (BitVec width))}
    (h : codeRel reachable c d) {n : Nat} (hn : sptMem n reachable) :
    sptMem n c ↔ sptMem n d := by
  rw [sptMem_iff_lookup, sptMem_iff_lookup, h n hn]

/-- Case `LocValue` of HOL `word_removal_lemma` (`Resume word_removal_lemma[LocValue]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_LocValue :
    ∀ (r l1 : Nat) (state : WordSemStateFiniteExact width C F),
      WordRemovalGoal (.locValue r l1) state := by
  intro r l1 state result new_state reachable removed ⟨hev, herr, hrel, _, _, _, _, hfwr, _⟩
  obtain ⟨c, rfl⟩ := wordStateRel_exists_withCode hrel
  have hl1 : sptMem l1 reachable := hfwr ((sptMem_sptInsert l1 l1 () .ln).mpr (Or.inl rfl))
  have hcode : codeRel reachable c state.code := hrel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmem := codeRel_mem hcode hl1
  rw [evaluate] at hev
  rw [evaluate]
  by_cases hm : sptMem l1 state.code
  · simp only [hm, if_true] at hev
    have hm' : sptMem l1 c := hmem.mpr hm
    simp only [hm', if_true]
    cases hev
    refine ⟨{ setVar r (.loc l1 0) state with code := c }, rfl, ?_, fun n hn => hn.elim⟩
    refine wordStateRel_withCode hrel rfl ?_
    exact locsIn_setVar (R := fun n => sptMem n reachable) state r _ (wordStateRel_locs hrel)
      (by rintro n o h; cases h; exact hl1)
  · simp only [hm, if_false] at hev
    cases hev
    exact absurd rfl herr

/-- Case `Install` of HOL `word_removal_lemma` (`Resume word_removal_lemma[Install]`):
    `no_install` excludes it. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_Install :
    ∀ (ptr len dptr dlen : Nat) (names : WordLangCutsetsHOL)
      (state : WordSemStateFiniteExact width C F),
      WordRemovalGoal (.install ptr len dptr dlen names) state := by
  intro ptr len dptr dlen names state result new_state reachable removed ⟨_, _, _, _, hni, _⟩
  simp [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] at hni

end LocValueInstall

end Flapjack.Compiler.Backend.WordElim

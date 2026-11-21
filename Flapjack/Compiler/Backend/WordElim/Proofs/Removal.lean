module

public import Flapjack.Compiler.Backend.WordElim.Proofs.Removal.Leaf
public import Flapjack.Compiler.Backend.WordElim.Proofs.Removal.Call

@[expose] public section

/-!
# `word_removal_lemma` and `word_removal_thm`

Counterpart of the MAIN LEMMAS and WORD_REMOVAL_THM sections of
`cakeml/compiler/backend/proofs/word_elimProofScript.sml` (lines 931-1663).
HOL proves `word_removal_lemma` by `recInduct evaluate_ind` with one
`Resume` block per constructor; the Lean case pieces live in
`Removal/Leaf.lean`, `Removal/Control.lean` and `Removal/Call.lean`, and the
assembling theorem below applies the rebound `evaluate_ind` to them.
-/

namespace Flapjack.Compiler.Backend.WordElim
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordProps
open Flapjack.Compiler.Backend.FlatElim

namespace WordElimRemovalSupport
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end WordElimRemovalSupport

/-- Exact HOL `word_removal_lemma` (`word_elimProofScript.sml:931-987` and its
    `Resume` blocks to line 1601): running a program on a state whose code is
    replaced by its reachable part gives the same result, with related final
    states, and the result's locations are reachable.  HOL's `no_install p` is
    `noInstallSubprogsHOL p = true`; `dest_result_loc result ⊆ domain reachable`
    is `{n | destResultLoc result n} ⊆ sptDomainSet reachable`. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma {width : Nat} [NeZero width] {C F : Type} :
    ∀ (program : WordLangProgHOL (BitVec width)) (state : WordSemStateFiniteExact width C F)
      (result : Option (WordSemResult width)) (new_state : WordSemStateFiniteExact width C F)
      (reachable : NumSet) (removed_state : WordSemStateFiniteExact width C F),
      evaluate program state = (result, new_state) ∧ result ≠ some .error ∧
        wordStateRel reachable state removed_state ∧ gcNoNewLocs state.gcFun ∧
        noInstallSubprogsHOL program = true ∧ noInstallCode state.code ∧
        noInstallCode removed_state.code ∧
        sptDomainSet (findWordRef program) ⊆ sptDomainSet reachable ∧
        codeClosed reachable state.code →
      ∃ s, evaluate program removed_state = (result, s) ∧ wordStateRel reachable new_state s ∧
        {n | destResultLoc result n} ⊆ sptDomainSet reachable := by
  intro program state
  exact evaluate_ind (fun p s => WordRemovalGoal p s)
    ⟨word_removal_lemma_Skip, word_removal_lemma_Alloc, word_removal_lemma_StoreConsts,
      word_removal_lemma_Move, word_removal_lemma_Inst, word_removal_lemma_Assign,
      word_removal_lemma_Get, word_removal_lemma_Set, word_removal_lemma_OpCurrHeap,
      word_removal_lemma_Store, word_removal_lemma_Tick, word_removal_lemma_MustTerminate,
      word_removal_lemma_Seq, word_removal_lemma_Return, word_removal_lemma_Raise,
      word_removal_lemma_Break, word_removal_lemma_Continue, word_removal_lemma_If,
      word_removal_lemma_Loop, word_removal_lemma_LocValue, word_removal_lemma_Install,
      word_removal_lemma_CodeBufferWrite, word_removal_lemma_DataBufferWrite,
      word_removal_lemma_FFI, word_removal_lemma_ShareInst, word_removal_lemma_Call⟩
    program state

/-- Lookup in the reachable part of an association list. Flapjack
    infrastructure. -/
theorem sptAListLookup_removeWordCode {α : Type} (k : Nat) (reachable : NumSet) :
    ∀ l : List (Nat × α), sptAListLookup k (removeWordCode reachable l) =
      if (sptLookup k reachable).isSome then sptAListLookup k l else none
  | [] => by simp [removeWordCode, sptAListLookup]
  | (k', v) :: rest => by
    have ih := sptAListLookup_removeWordCode k reachable rest
    simp only [removeWordCode, List.filter_cons] at ih ⊢
    by_cases hk : k = k'
    · subst hk
      by_cases hr : (sptLookup k reachable).isSome <;> simp [hr, sptAListLookup, ih]
    · split <;> simp [sptAListLookup, hk, ih]

/-- Exact HOL `word_removal_thm` (`word_elimProofScript.sml:1605-1663`).  HOL's
    universally quantified `r : δ` does not occur in the body; it is retained
    (unnamed) with an independent type, as in the typed capture.
    `ALL_DISTINCT (MAP FST code1)` is `(code1.map Prod.fst).Nodup`, and
    `closure_spt` is the reviewed `closureTotal`. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_thm {width : Nat} [NeZero width] {C F : Type} {δ : Type} :
    ∀ (start : Nat) (state : WordSemStateFiniteExact width C F)
      (result : Option (WordSemResult width)) (new_state : WordSemStateFiniteExact width C F)
      (_r : δ) (reachable : NumSet) (code1 : List (Nat × Nat × WordLangProgHOL (BitVec width))),
      evaluate (.call none (some start) [0] none) state = (result, new_state) ∧
        result ≠ some .error ∧ state.code = sptFromAList code1 ∧
        sptDomainSet (findLocState state) ⊆ sptDomainSet reachable ∧
        gcNoNewLocs state.gcFun ∧
        reachable = closureTotal (sptInsert start () .ln) (analyseWordCode code1) ∧
        (code1.map Prod.fst).Nodup ∧ noInstallCode state.code →
      ∃ s, evaluate (.call none (some start) [0] none)
          { state with code := sptFromAList (removeWordCode reachable code1) } = (result, s) := by
  intro start state result new_state _ reachable code1
    ⟨hev, herr, hcode, hloc, hg, hreach, _, hnic⟩
  have hclosure : ∀ m, sptMem m reachable ↔
      ∃ root, sptDomain (sptInsert start () .ln) root ∧
        isReachable (analyseWordCode code1) root m := by
    intro m
    rw [hreach]
    show sptDomain _ m ↔ _
    rw [closureTotal_reachable]
  have hstart : sptMem start reachable :=
    (hclosure start).mpr ⟨start, (sptMem_sptInsert start start () .ln).mpr (Or.inl rfl),
      Relation.ReflTransGen.refl⟩
  have hlookup : ∀ k, sptLookup k (sptFromAList (removeWordCode reachable code1)) =
      if (sptLookup k reachable).isSome then sptLookup k state.code else none := by
    intro k
    rw [hcode, sptLookup_sptFromAList, sptLookup_sptFromAList, sptAListLookup_removeWordCode]
  have hrel : wordStateRel reachable state
      { state with code := sptFromAList (removeWordCode reachable code1) } := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, ?_, fun n hn => hloc hn⟩
    intro n hn
    obtain ⟨u, hu⟩ := (sptMem_iff_lookup n reachable).mp hn
    show sptLookup n (sptFromAList (removeWordCode reachable code1)) = sptLookup n state.code
    rw [hlookup, hu]
    rfl
  have hnicr : noInstallCode (sptFromAList (removeWordCode reachable code1)) := by
    intro k a p hk
    rw [hlookup] at hk
    split at hk
    · exact hnic k a p hk
    · cases hk
  have hfwr : sptDomainSet (findWordRef (.call none (some start) [0] none :
      WordLangProgHOL (BitVec width))) ⊆ sptDomainSet reachable := by
    intro m hm
    have hm' : sptMem m (findWordRef (.call none (some start) [0] none :
        WordLangProgHOL (BitVec width))) := hm
    rw [findWordRef_call] at hm'
    simp only [sptMem_sptUnion, sptMem_sptInsert, sptMem_ln, or_false] at hm'
    rw [hm']
    exact hstart
  have hcc : codeClosed reachable state.code := by
    refine ⟨code1, hcode, ?_⟩
    rintro n m ⟨hn, hnm⟩
    obtain ⟨root, hroot, hrn⟩ := (hclosure n).mp hn
    exact (hclosure m).mpr ⟨root, hroot, hrn.trans hnm⟩
  obtain ⟨s, hs, -, -⟩ := word_removal_lemma _ state result new_state reachable _
    ⟨hev, herr, hrel, hg, by simp [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp], hnic,
      hnicr, hfwr, hcc⟩
  exact ⟨s, hs⟩

end Flapjack.Compiler.Backend.WordElim

module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.RootsValid
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordGcCorrect
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CollectorFilter
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LocMerge
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CollectorStore
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.DecStack
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.DecodedRoots
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordGcSize
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.FrameRoots
@[expose] public section

/-! Garbage collection preserves the data-to-word state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.WordGcFunctions

/-- Collector invariants used in the proof of the state-relation preservation
result. This helper packages intermediate facts from the HOL proof. -/
private theorem stateRelGcCore {width : Nat} [NeZero width] {C F : Type} (conf : Config) (l1 l2 : Nat)
    (s : DataSem.State C F) (t : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (related : stateRel conf l1 l2 s t none locs) (sourceEmpty : s.locals = .ln)
    (requested : Nat) (alloc : t.store.lookup .allocSize = some (.word (gcAllocSize requested))) :
    ∃ moved encMoved outMemory outStore stack,
      wordGcFun conf ((flatStack s.stack t.stack).map Prod.snd, t.memory, t.mdomain, t.store) =
        some (moved, outMemory, outStore) ∧
      t.gcFun (wordSemEncStack t.stack, t.memory, t.mdomain, t.store) = some (encMoved, outMemory, outStore) ∧
      encMoved = locMerge (wordSemEncStack t.stack) (moved.filter wordSemIsWordLoc) ∧
      wordSemDecStack encMoved t.stack = some stack ∧
      outStore.lookup (.temp 29) = t.store.lookup (.temp 29) ∧
      outStore.lookup .allocSize = t.store.lookup .allocSize ∧
      List.Forall₂ stackRel s.stack stack ∧ List.Forall₂ containsLoc stack locs ∧
      flatStack s.stack stack = ((flatStack s.stack t.stack).map Prod.fst).zip moved ∧
      stateRel conf l1 l2 {s with space := 0} {t with stack := stack, store := outStore, memory := outMemory} none locs ∧
      (WordSemStateFiniteExact.hasSpace (.word (gcAllocSize requested) : WordLocW width) {t with store := outStore} = some false ∧
        conf.gcKind ≠ .none ∧ DataSem.noThunksInRefs s.refs →
        ∀ roots2 dups n2 r2 s2,
          roots2.Perm (dups ++ s.stack.flatMap DataSem.extractStack ++ [theGlobal s.global]) ∧
          (∀ v, v ∈ dups → v ∈ s.stack.flatMap DataSem.extractStack ++ [theGlobal s.global]) ∧
          DataSem.sizeOfValues s.limits roots2 s.refs .ln = (n2, r2, s2) →
            s.limits.heapLimit < n2 + requested) := by
  have good : goodDimindex width := related.2.2.2.2.2.2.1
  have gc : t.gcFun = wordGcFun conf := related.2.2.2.1
  have stackReln : List.Forall₂ stackRel s.stack t.stack := by
    rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hstack, _⟩
    exact hstack
  have locReln : List.Forall₂ containsLoc t.stack locs := by
    rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hloc, _⟩
    exact hloc
  obtain ⟨heap, limit, a, sp, sp1, gens, hmem, hinv, hbound, _, limitEq, hvalid⟩ :=
    stateRel_gcRoots conf l1 l2 s t locs related
  obtain ⟨moved, outMemory, outStore, heap1, a1, free1, free2, gens1, root1, roots1,
    run, outHeap, absOut, globalOut, rootsOut, failed⟩ :=
    wordGcFun_correct conf (theGlobal s.global) (flatStack s.stack t.stack) s.refs heap t.be a sp sp1 limit
      (holThe s.tstamps) requested gens t.store t.memory t.mdomain t good hmem hinv
  have flatValid : ((flatStack s.stack t.stack).map Prod.snd).all locOk = true := by
    apply List.all_eq_true.mpr
    intro word member
    apply wordMlInv_roots_locOk heap t.be a sp sp1 gens limit (holThe s.tstamps) conf s.refs _ hinv word
    simp only [List.map_cons, List.mem_cons]
    exact Or.inr member
  have encValid : (wordSemEncStack t.stack).all locOk = true := by
    apply List.all_eq_true.mpr
    exact hvalid
  have filtered := wordGcFun_imp_filter conf ((flatStack s.stack t.stack).map Prod.snd) moved
    t.memory outMemory t.mdomain t.store outStore run flatValid
  rw [filter_encStack s.stack t.stack stackReln] at filtered
  have encRun := wordGcFun_locMerge conf (wordSemEncStack t.stack) (moved.filter wordSemIsWordLoc)
    t.memory outMemory t.mdomain t.store outStore filtered encValid
  obtain ⟨stack, decoded⟩ := decStack_locMerge_encStack t.stack (moved.filter wordSemIsWordLoc)
  have afterRel := stackRel_decStack_locMerge t.stack (moved.filter wordSemIsWordLoc) s.stack stack locs
    stackReln locReln decoded
  have gcRel := word_gc_IMP_EVERY2 run
  have convert : ∀ (xs ys : List (WordLocW width)), ListRel gcRootRel xs ys →
      List.Forall₂ (fun x y => wordSemIsWordLoc x = wordSemIsWordLoc y ∧
        (wordSemIsWordLoc x = false → x = y)) xs ys := by
    intro xs ys relation
    induction relation with
    | nil => exact .nil
    | @cons x y xs ys head tail ih =>
      apply List.Forall₂.cons ?_ ih
      refine ⟨head.1, ?_⟩
      intro notWord
      apply head.2
      cases x <;> simp_all [wordSemIsWordLoc, Flapjack.Compiler.Backend.WordSimp.isGcWordConst]
  have rootRel := convert _ _ gcRel
  have flatEq := wordGcFun_decStack_flat s.stack t.stack stack moved afterRel.1 rootRel decoded stackReln
  have movedInv : wordMlInv (heap1, t.be, a1, free1, free2, gens1) limit (holThe s.tstamps)
      conf s.refs ((theGlobal s.global, holFapply outStore .globals) ::
        ((flatStack s.stack t.stack).map Prod.fst).zip moved) := by
    refine ⟨root1 :: roots1, ?_, ?_⟩
    · exact absOut
    · simp only [List.map_cons]
      exact List.Forall₂.cons globalOut rootsOut
  have preserved := wordGcFun_store_invariants conf _ moved t.memory outMemory t.mdomain t.store outStore run
  have postRel : stateRel conf l1 l2 {s with space := 0}
      {t with stack := stack, store := outStore, memory := outMemory} none locs := by
    rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
      htstamp, hglobal, hzero, hlocal, hstack, hloc, hstackBound, hmax, hsize, hlocalSize, hlimit, hmemory⟩
    have hstackSize : wordSemStackSize stack = wordSemStackSize t.stack :=
      (stackRel_sizeOfStack afterRel.1).trans (stackRel_sizeOfStack hstack).symm
    have oracleOut := codeOracleRel_afterWordGc conf s.compile s.compileOracle t.store outStore
      t.compile t.compileOracle t.codeBuffer t.dataBuffer _ moved t.memory outMemory t.mdomain run horacle
    have limitOut : limitsInv s.limits (outStore.lookup .heapLength) t.stackLimit
        conf.lenSize conf.hasFpOps conf.hasFpTern := by
      rw [preserved.2.2.2.2.2.2.2.1]
      exact hlimit
    have memoryOut : memoryRel conf t.be (holThe s.tstamps) s.refs 0 outStore outMemory t.mdomain
        (joinEnv s.locals (sptToAList (sptInter t.locals (adjustSet s.locals))) ++
          [(theGlobal s.global, holFapply outStore .globals)] ++ flatStack s.stack stack) := by
      refine ⟨heap1, limit, a1, free1, free2, gens1, outHeap, ?_, hbound, Nat.zero_le _⟩
      have emptyInter : sptInter t.locals (adjustSet (.ln : Spt DataSem.Value)) = .ln := by
        cases t.locals <;> simp [adjustSet, sptToAList, sptFoldi, sptFromAList, sptInter]
      rw [sourceEmpty, emptyInter]
      simp only [sptToAList, sptFoldi, joinEnv_nil, List.nil_append, List.singleton_append]
      rw [flatEq]
      exact movedInv
    change t.ffi = s.ffi ∧ _
    refine ⟨hffi, hclock, hhandler, hgc, hcode, oracleOut, hgood, hshift, htstamp, ?_, hzero, hlocal,
      afterRel.1, afterRel.2, ?_, hmax, hsize, hlocalSize, limitOut, ?_⟩
    · simpa using preserved.2.2.2.2.2.2.2.2
    · simpa [hstackSize] using hstackBound
    · simpa using memoryOut
  refine ⟨moved, _, outMemory, outStore, stack, run, ?_, rfl, decoded, preserved.2.2.2.2.2.2.1, preserved.1, afterRel.1, afterRel.2, flatEq, postRel, ?_⟩
  · rw [gc]
    exact encRun
  · rintro ⟨hspace, hkind, noThunks⟩ roots2 dups n2 r2 s2 ⟨permutation, subset, sizeEq⟩
    have architecture : s.limits.arch64Bit = decide (width = 64) := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
    obtain ⟨otherMoved, otherMemory, otherStore, otherRun, failedBound⟩ :=
      wordGcFun_failed_sourceSize s.limits conf (theGlobal s.global) (flatStack s.stack t.stack)
        s.refs heap t.be a sp sp1 limit (holThe s.tstamps) requested gens t.store t.memory t.mdomain t
        good architecture limitEq noThunks hmem hinv
    rw [run] at otherRun
    simp only [Option.some.injEq, Prod.mk.injEq] at otherRun
    obtain ⟨rfl, rfl, rfl⟩ := otherRun
    have corePerm : (s.stack.flatMap DataSem.extractStack ++ [theGlobal s.global]).Perm
        (theGlobal s.global :: (flatStack s.stack t.stack).map Prod.fst) := by
      exact List.Perm.trans List.perm_append_comm ((flatStack_values_perm s.stack t.stack stackReln).symm.cons _)
    have perm0 : roots2.Perm (dups ++ (s.stack.flatMap DataSem.extractStack ++ [theGlobal s.global])) := by
      simpa only [List.append_assoc] using permutation
    have permNew : roots2.Perm (dups ++ (theGlobal s.global :: (flatStack s.stack t.stack).map Prod.fst)) :=
      perm0.trans (corePerm.append_left dups)
    have subsetNew : ∀ v, v ∈ dups → v ∈ theGlobal s.global :: (flatStack s.stack t.stack).map Prod.fst := by
      intro v hv
      exact (corePerm.mem_iff).mp (subset v hv)
    have bound := failedBound ⟨alloc, hspace, hkind⟩ roots2 dups permNew subsetNew
    simpa [sizeEq] using bound

namespace StateRelGcWitnesses

/-- Canonical finite-map codec for the word state used by the GC relation. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end StateRelGcWitnesses

/-- The garbage collector preserves the state relation and establishes the
allocation bound when collection fails to provide space. The three independent
unused witnesses represent the nonempty HOL types in the original statement. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_gc_gen"
  (fmap_as_finite_support_relation := [st, WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)
  (hol_existential_inhabitants := [T2._t2, W1._w1, W2._w2])]
theorem stateRel_gcGen {width : Nat} [NeZero width] {C F T2 W1 W2 : Type}
    [Nonempty T2] [Nonempty W1] [Nonempty W2]
    (conf : Config) (l1 l2 : Nat) (s : DataSem.State C F)
    (t : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat)) (k : Nat)
    (related : stateRel conf l1 l2 s t none locs)
    (premises : t.store.lookup .allocSize = some (.word (gcAllocSize k)) ∧
      s.locals = .ln ∧ t.locals = .ls (.loc l1 l2)) :
    ∃ (_t2 : T2) (wl : List (WordLocW width))
      (m : BitVec width → WordLocW width) (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
      (_w1 : W1) (_w2 : W2) (stack : List (WordSemStackFrame width)),
      t.gcFun (wordSemEncStack t.stack, t.memory, t.mdomain, t.store) = some (wl, m, st) ∧
      wordSemDecStack wl t.stack = some stack ∧
      st.lookup (.temp 29) = t.store.lookup (.temp 29) ∧
      st.lookup .allocSize = some (.word (gcAllocSize k)) ∧
      (WordSemStateFiniteExact.hasSpace (.word (gcAllocSize k) : WordLocW width) {t with store := st} = some false ∧
        conf.gcKind ≠ .none ∧ DataSem.noThunksInRefs s.refs →
        ∀ roots2 dups n2 r2 s2,
          roots2.Perm (dups ++ s.stack.flatMap DataSem.extractStack ++ [theGlobal s.global]) ∧
          (∀ v, v ∈ dups → v ∈ s.stack.flatMap DataSem.extractStack ++ [theGlobal s.global]) ∧
          DataSem.sizeOfValues s.limits roots2 s.refs .ln = (n2, r2, s2) →
            s.limits.heapLimit < n2 + k) ∧
      stateRel conf l1 l2 {s with space := 0} {t with stack := stack, store := st, memory := m} none locs := by
  obtain ⟨moved, wl, m, st, stack, run, encRun, merge, decoded, temp, allocEq, stackReln, locReln, flatEq, postRel, failed⟩ :=
    stateRelGcCore conf l1 l2 s t locs related premises.2.1 k premises.1
  exact ⟨Classical.choice inferInstance, wl, m, st, Classical.choice inferInstance,
    Classical.choice inferInstance, stack, encRun, decoded, temp, allocEq.trans premises.1, failed, postRel⟩



end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GcLemma
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GcAddCallEnv
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutState
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutEnvs
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.HasSpace
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutLocals
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.SizeValues

@[expose] public section

/-! Generalized allocation simulation for the data-to-word compiler. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace AllocLemmaGenWitnesses
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end AllocLemmaGenWitnesses

/-- Allocation preserves the complete state relation when space is available;
otherwise it preserves the observable state and proves the original heap bound. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "alloc_lemma_gen"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem allocLemma_gen {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat)
    (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target result : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (names : NumSet)
    (cutData : Spt Flapjack.Compiler.Backend.DataSem.Value) (k : Nat)
    (q : Option (WordSemResult width))
    (premises : stateRel conf l1 l2 source target none locs ∧
      DataSem.cutEnv names source.locals = some cutData ∧
      WordSemStateFiniteExact.alloc (gcAllocSize k) (adjustSets names) target = (q, result)) :
    (q = some .notEnoughSpace → result.ffi = source.ffi ∧ optionLe result.stackMax source.stackMax ∧
      (conf.gcKind ≠ .none ∧ DataSem.noThunksInRefs source.refs →
        ∀ (roots2 dups : List Flapjack.Compiler.Backend.DataSem.Value) (n2 : Nat)
          (r2 : Spt (Flapjack.Compiler.Backend.BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (s2 : NumSet),
          roots2.Perm (dups ++ sptToList cutData ++ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global]) ∧
          (∀ v, v ∈ dups → v ∈ sptToList cutData ++ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global]) ∧
          DataSem.sizeOfValues source.limits roots2 source.refs .ln = (n2, r2, s2) →
            source.limits.heapLimit < n2 + k)) ∧
    (q ≠ some .notEnoughSpace →
      stateRel conf l1 l2 {source with locals := cutData, space := k} result none locs ∧
      gcAllocSize k ≠ (-1 : BitVec width) ∧
      result.store.lookup (.temp 29) = target.store.lookup (.temp 29) ∧
      result.code = target.code ∧ result.codeBuffer = target.codeBuffer ∧
      result.dataBuffer = target.dataBuffer ∧ result.compileOracle = target.compileOracle ∧ q = none) := by
  obtain ⟨related, dataCut, allocRun⟩ := premises
  obtain ⟨wordCut, cutRun⟩ := cutEnv_imp_wordCutEnv conf l1 l2 source target locs names cutData ⟨related, dataCut⟩
  obtain ⟨first, second, cutPair, _⟩ := cutEnv_imp_cutEnvs (adjustSets names) target.locals wordCut cutRun
  let t5 := WordSemStateFiniteExact.setStore .allocSize (.word (gcAllocSize k)) target
  have t5rel : stateRel conf l1 l2 source t5 none locs := by
    simpa [t5, stateRel_setStore_allocSize] using related
  have t5cut : wordSemCutEnvs (adjustSets names) t5.locals = some (first, second) := by
    simpa [t5, WordSemStateFiniteExact.setStore] using cutPair
  have t5alloc : t5.store.lookup .allocSize = some (.word (gcAllocSize k)) := by
    simp [t5, WordSemStateFiniteExact.setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  have collect := gcLemma_gen (W1 := Unit) (W2 := Unit) conf l1 l2 source t5 locs names cutData
    (first, second) (some 0) k ⟨dataCut, t5rel, t5alloc, t5cut⟩
  obtain ⟨t2, wl, m, st, _, _, stack, gcRun, decode, popRun, tempRead, allocAfter, failure, postRel⟩ := collect
  let t0 := WordSemStateFiniteExact.callEnv [.loc l1 l2] (some 0)
    (WordSemStateFiniteExact.pushEnv (first, second) none t5)
  change t0.gcFun (wordSemEncStack t0.stack, t0.memory, t0.mdomain, t0.store) = some (wl, m, st) at gcRun
  change wordSemDecStack wl t0.stack = some stack at decode
  change WordSemStateFiniteExact.popEnv {t0 with stack := stack, store := st, memory := m} = some t2 at popRun
  have gcSucc : WordSemStateFiniteExact.gc t0 = some {t0 with stack := stack, store := st, memory := m} := by
    simp [WordSemStateFiniteExact.gc, gcRun, decode]
  let finish (s : WordSemStateFiniteExact width C F) : Option (WordSemResult width) × WordSemStateFiniteExact width C F :=
    match WordSemStateFiniteExact.getStore .allocSize s with
    | none => (some .error, s)
    | some w => match WordSemStateFiniteExact.hasSpace w s with
      | none => (some .error, s)
      | some true => (none, s)
      | some false => (some .notEnoughSpace, WordSemStateFiniteExact.flushState true s)
  have hhead : (match WordSemStateFiniteExact.gc (WordSemStateFiniteExact.pushEnv (first, second) none t5) with
      | none => (some .error, WordSemStateFiniteExact.flushState true target)
      | some s => match WordSemStateFiniteExact.popEnv s with
        | none => (some .error, WordSemStateFiniteExact.flushState true s)
        | some s => finish s) = (q, result) := by
    unfold WordSemStateFiniteExact.alloc at allocRun
    rw [cutPair] at allocRun
    exact allocRun
  have adapted := gcAddCallEnv (first, second) t5 (WordSemStateFiniteExact.flushState true target)
    result l1 l2 finish q hhead
  change (match WordSemStateFiniteExact.gc t0 with
      | none => (some .error, WordSemStateFiniteExact.flushState true target)
      | some s => match WordSemStateFiniteExact.popEnv s with
        | none => (some .error, WordSemStateFiniteExact.flushState true s)
        | some s => finish s) = (q, result) at adapted
  simp only [gcSucc, popRun] at adapted
  have finished : finish t2 = (q, result) := adapted
  have someSpace : ∃ flag, WordSemStateFiniteExact.hasSpace (.word (gcAllocSize k) : WordLocW width) t2 = some flag := by
    have hmem := postRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    obtain ⟨next, trigger, available, nextStore, triggerStore, gap, _, maxMem, bound⟩ :=
      memoryRel_spaceMax conf t2.be (holThe source.tstamps) source.refs 0 t2.store t2.memory t2.mdomain _ hmem
    simp [WordSemStateFiniteExact.hasSpace, WordSemStateFiniteExact.getStore, nextStore, triggerStore]
  have allocStore : WordSemStateFiniteExact.getStore .allocSize t2 = some (.word (gcAllocSize k)) := allocAfter
  simp only [finish, allocStore] at finished
  obtain ⟨flag, spaceRun⟩ := someSpace
  rw [spaceRun] at finished
  have popFields := WordSemStateFiniteExact.popEnvConst _ _ popRun
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, popMax, _⟩ := popFields
  have t2MaxEq : t2.stackMax = wordSemOptionMax (wordSemOptionMax target.stackMax
      (wordSemStackSize (.stackFrame target.localsSize (sptToAList first)
        (wordSemEnvToList second target.permute).1 none :: target.stack)))
      (wordSemOptionAdd (wordSemStackSize (.stackFrame target.localsSize (sptToAList first)
        (wordSemEnvToList second target.permute).1 none :: target.stack)) (some 0)) := by
    simpa [t0, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, t5,
      WordSemStateFiniteExact.setStore] using popMax
  have stackBound : optionLe t2.stackMax source.stackMax := by
    have acc := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have maxBound := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [t2MaxEq]
    have frameEq : wordSemStackSize (.stackFrame target.localsSize (sptToAList first)
        (wordSemEnvToList second target.permute).1 none :: target.stack) =
        wordSemOptionAdd target.localsSize (wordSemStackSize target.stack) := rfl
    rw [frameEq]
    cases ha : target.stackMax <;> cases hb : source.stackMax <;>
      cases hc : wordSemStackSize target.stack <;> cases hd : target.localsSize <;>
      simp [ha, hb, hc, hd, wordSemOptionAdd, wordSemOptionMax, optionLe] at acc maxBound ⊢
    all_goals omega
  have zeroRel : stateRel conf l1 l2 {source with locals := cutData, space := 0} t2 none locs := by
    rcases postRel with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
      htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
    exact ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp,
      hglobal, hzero, hpresent, hstack, hlocs, hacc, stackBound, hsizes, hlocals, hlim, hmem⟩
  cases flag with
  | false =>
    simp only [Prod.mk.injEq] at finished
    obtain ⟨rfl, rfl⟩ := finished
    constructor
    · intro _
      refine ⟨?_, ?_, ?_⟩
      · simpa [WordSemStateFiniteExact.flushState] using postRel.1
      · simpa [WordSemStateFiniteExact.flushState] using stackBound
      · intro good roots dups n2 r2 s2 inputs
        exact failure ⟨spaceRun, good⟩ roots dups n2 r2 s2 inputs
    · simp
  | true =>
    simp only [Prod.mk.injEq] at finished
    obtain ⟨rfl, rfl⟩ := finished
    constructor
    · simp
    · intro _
      have hrel := hasSpace_stateRel conf l1 l2 {source with locals := cutData, space := 0} t2 locs k
        ⟨spaceRun, zeroRel⟩
      have goodDim := zeroRel.2.2.2.2.2.2.1
      have hmem := zeroRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      obtain ⟨next, trigger, available, nextStore, triggerStore, gap, _, _, _⟩ :=
        memoryRel_spaceMax conf t2.be (holThe source.tstamps) source.refs 0 t2.store t2.memory t2.mdomain _ hmem
      have fits : (gcAllocSize k : BitVec width) ≤ wordSemBytesInWord * BitVec.ofNat width available := by
        apply BitVec.le_def.mpr
        have h : (gcAllocSize k : BitVec width).toNat ≤ (trigger - next).toNat := by
          simpa [WordSemStateFiniteExact.hasSpace, WordSemStateFiniteExact.getStore, nextStore, triggerStore] using spaceRun
        rw [gap] at h
        exact h
      have notMax : (gcAllocSize k : BitVec width) ≠ -1 := by
        intro maxEq
        have fitNat := BitVec.le_def.mp fits
        rw [maxEq] at fitNat
        have zero := (wordMaxLeIffAddOneEqZero (wordSemBytesInWord * BitVec.ofNat width available)).mp fitNat
        exact bytesInWordAddOneNeZero (BitVec.ofNat width available) goodDim zero
      refine ⟨?_, notMax, ?_, ?_, ?_, ?_, ?_, rfl⟩
      · simpa using hrel
      · simpa [t5, WordSemStateFiniteExact.setStore, FUPDATE_HOL] using tempRead
      · have h := (WordSemStateFiniteExact.popEnvConst _ _ popRun).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        simpa [t0, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, t5,
          WordSemStateFiniteExact.setStore] using h
      · have h := (WordSemStateFiniteExact.popEnvConst _ _ popRun).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        simpa [t0, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, t5,
          WordSemStateFiniteExact.setStore] using h
      · have h := (WordSemStateFiniteExact.popEnvConst _ _ popRun).2.2.2.2.2.2.2.2.2.2.2.2.2.1
        simpa [t0, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, t5,
          WordSemStateFiniteExact.setStore] using h
      · have h := (WordSemStateFiniteExact.popEnvConst _ _ popRun).2.2.2.2.1
        simpa [t0, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, t5,
          WordSemStateFiniteExact.setStore] using h


/-- Allocation has the original heap-size bound on failure and the full success postcondition. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "alloc_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem allocLemma {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat)
    (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target result : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (names : NumSet)
    (cutData : Spt Flapjack.Compiler.Backend.DataSem.Value) (k : Nat)
    (q : Option (WordSemResult width))
    (premises : stateRel conf l1 l2 source target none locs ∧
      DataSem.cutEnv names source.locals = some cutData ∧
      WordSemStateFiniteExact.alloc (gcAllocSize k) (adjustSets names) target = (q, result)) :
    (q = some .notEnoughSpace → result.ffi = source.ffi ∧ optionLe result.stackMax source.stackMax ∧
      (conf.gcKind ≠ .none ∧ DataSem.noThunksInRefs source.refs →
        source.limits.heapLimit < DataSem.sizeOfHeap (cutLocals names source) + k)) ∧
    (q ≠ some .notEnoughSpace →
      stateRel conf l1 l2 {source with locals := cutData, space := k} result none locs ∧
      gcAllocSize k ≠ (-1 : BitVec width) ∧
      result.store.lookup (.temp 29) = target.store.lookup (.temp 29) ∧
      result.code = target.code ∧ result.codeBuffer = target.codeBuffer ∧
      result.dataBuffer = target.dataBuffer ∧ result.compileOracle = target.compileOracle ∧ q = none) := by
  have gen := allocLemma_gen conf l1 l2 source target result locs names cutData k q premises
  constructor
  · intro qbad
    obtain ⟨ffi, stack, bound⟩ := gen.1 qbad
    refine ⟨ffi, stack, ?_⟩
    intro good
    have bound := bound good
    let roots := sptToList cutData ++ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global]
    obtain ⟨n, r, seen, hn⟩ : ∃ n r seen, DataSem.sizeOfValues source.limits roots source.refs .ln = (n, r, seen) := by
      cases h : DataSem.sizeOfValues source.limits roots source.refs .ln with
      | mk n rest => cases rest with | mk r seen => exact ⟨n, r, seen, rfl⟩
    have hbound := bound roots [] n r seen ⟨by simp [roots], by simp, hn⟩
    have sizeEq : DataSem.sizeOfHeap (cutLocals names source) = n := by
      simp only [cutLocals, premises.2.1, DataSem.sizeOfHeap, DataSem.stackToValues]
      rw [sizeOfValues_global]
      simpa [roots, List.append_assoc] using congrArg Prod.fst hn
    simpa [sizeEq] using hbound
  · exact gen.2

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

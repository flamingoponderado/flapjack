module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.InitStoreOk
public import Flapjack.Compiler.Backend.DataToWord.ConfOk
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.BitLemmas
public import Flapjack.Compiler.Backend.GcShared.Filter
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.HeapExpand
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.SmallNumber
public import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListMemory
public import Flapjack.Compiler.Backend.StackRemove.Proofs.WordAddressArithmetic

@[expose] public section

/-! `state_rel_init` (`data_to_word_gcProofScript.sml:4608-4675`): the initial
data state is related to any word state set up by the stack initialization. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.GcCombined

namespace StateRelInitWitnesses

/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end StateRelInitWitnesses

/-- The expanded empty heap splits at its own length, with no reference in the
first part and an empty second part. Flapjack helper. -/
theorem heapSplit_heapExpand {α β : Type} (n : Nat) :
    heapSplit n (heapExpand n : List (HeapElement α β)) = some (heapExpand n, []) := by
  unfold heapExpand
  split
  · subst n; simp [heapSplit]
  · simp [heapSplit, elLength, show n ≠ 0 by omega, show n - 1 + 1 = n by omega]

/-- The expanded empty heap splits at offset zero. Flapjack helper. -/
theorem heapSplit_zero_heapExpand {α β : Type} (n : Nat) :
    heapSplit 0 (heapExpand n : List (HeapElement α β)) = some ([], heapExpand n) := by
  unfold heapExpand
  split <;> simp [heapSplit]

/-- The expanded empty heap contains no data element. Flapjack helper. -/
theorem not_dataElement_mem_heapExpand {α β : Type} (n : Nat) (xs : List (HeapAddress α))
    (len : Nat) (data : β) :
    HeapElement.dataElement xs len data ∉ (heapExpand n : List (HeapElement α β)) := by
  unfold heapExpand
  split <;> simp

/-- The abstract invariant of the empty initial heap, for unused space `sp`
and `sp1` covering the whole heap. Flapjack helper for `state_rel_init`. -/
theorem absMlInv_init {width : Nat} [NeZero width] (c : Config) (be : Bool) (limit sp sp1 : Nat)
    (gens : GenState) (total : sp + sp1 = limit) (beEq : c.be = be)
    (kind : gcKindInv c 0 sp sp1 gens (heapExpand limit : ValueHeap width)) :
    absMlInv c [] .ln ([], (heapExpand limit : ValueHeap width), be, 0, sp, sp1, gens) limit 0 := by
  refine ⟨?_, ⟨Flapjack.Compiler.Backend.heapLength_heapExpand limit, ?_, ?_⟩, kind, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro ptr value h; simp at h
  · unfold heapExpand; split <;> simp [isForwardPointer]
  · rintro xs len data ptr value ⟨h, -⟩
    exact absurd h (not_dataElement_mem_heapExpand _ _ _ _)
  · intro nonzero
    unfold heapExpand
    rw [if_neg (by omega)]
    simp [heapLookup, total]
  · rw [Flapjack.Compiler.Backend.heapLength_heapExpand]; omega
  · exact ⟨[], _, heapSplit_zero_heapExpand limit, by simp⟩
  · let empty : HolFiniteMapExact Nat Nat := ⟨fun _ => none, ⟨[], by simp⟩⟩
    refine ⟨empty, empty, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_, beEq, blocksUnique_empty, .nil, ?_⟩ <;>
      simp [empty, mapDomain]

/-- The generational invariant of the empty initial heap. Flapjack helper. -/
theorem gcKindInv_init_generational {width : Nat} [NeZero width] (c : Config) (limit : Nat)
    (sizes : List Nat) (kind : c.gcKind = .generational sizes) :
    gcKindInv c 0 0 limit (.genState 0 (sizes.map fun _ => 0))
      (heapExpand limit : ValueHeap width) := by
  unfold gcKindInv
  rw [kind]
  refine ⟨⟨?_, ?_⟩, heapExpand limit, [], by simpa using heapSplit_heapExpand limit, ?_, by simp⟩
  · simp
  · intro start mem
    simp only [List.mem_map] at mem
    obtain ⟨_, _, rfl⟩ := mem
    refine ⟨[], _, heapSplit_zero_heapExpand limit, by simp⟩
  · intro element mem
    unfold heapExpand at mem
    split at mem <;> simp at mem
    subst mem; simp [isRef]

/-- Bounds on a heap limit below `max_heap_limit`. Flapjack helper. -/
theorem maxHeapLimit_bounds {width : Nat} [NeZero width] (c : Config) (limit : Nat)
    (good : goodDimindex width) (bounded : limit ≤ maxHeapLimit width c) :
    limit ≤ 2 ^ width / 2 ^ shiftLength c ∧ (limit + 3) * (width / 8) + 1 < 2 ^ width := by
  unfold maxHeapLimit at bounded
  refine ⟨le_trans bounded (Nat.min_le_left _ _), ?_⟩
  have second := le_trans bounded (Nat.min_le_right _ _)
  rcases good with rfl | rfl <;>
    simp [Flapjack.wordShiftAmount] at second ⊢ <;> omega

/-- The memory relation for the empty initial heap and no roots, the core of
HOL's `state_rel_init` proof. Flapjack helper. -/
theorem memoryRel_init {width : Nat} [NeZero width] {cw dw : Nat} [NeZero cw] [NeZero dw]
    (c : Config) (be : Bool) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (cb : WordSemBuffer width cw) (db : WordSemBuffer width dw)
    (good : goodDimindex width) (conf : confOk width c) (beEq : c.be = be)
    (init : initStoreOk c store m dm cb db) :
    memoryRel c be 0 .ln 0 store m dm [] := by
  obtain ⟨limit, curr, bounded, globals, globReal, genStart, currHeap, otherHeap, nextFree,
    endOfHeap, triggerGC, heapLen, -, -, -, -, -, -, words, aligned⟩ := init
  obtain ⟨shiftLt, shiftLe, lenNz, lenLt⟩ := conf
  obtain ⟨heapBound, spaceBound⟩ := maxHeapLimit_bounds c limit good bounded
  have bytesEq : (wordSemBytesInWord : BitVec width) = StackRemove.bytesInWord width := rfl
  have otherAligned : holByteAligned (curr + StackRemove.bytesInWord width *
      BitVec.ofNat width limit) = true := by
    have h := (alignedAddSub _ curr _ (StackRemove.WordAddressArithmetic.byteAlignedBytesInWordMult (BitVec.ofNat width limit) good)).1
    unfold holByteAligned at aligned ⊢
    rw [h, aligned]
  have heaps : SetSep.star (wordHeap curr (heapExpand limit : ValueHeap width) c)
      (wordHeap (curr + StackRemove.bytesInWord width * BitVec.ofNat width limit)
        (heapExpand limit : ValueHeap width) c)
      (SetSep.fun2Set (m, fun addr => dm addr = true)) := by
    rw [wordHeap_heapExpand, wordHeap_heapExpand, ← StackRemove.Proofs.WordListMemory.wordListExistsAdd]
    exact words
  have store_part : ∀ (sp sp1 : Nat) (gens : GenState), sp + sp1 = limit →
      store.lookup .triggerGC = some (.word (curr + StackRemove.bytesInWord width *
        BitVec.ofNat width (0 + sp))) →
      genStartsInStore c gens (store.lookup .genStart) →
      heapInMemoryStore (heapExpand limit : ValueHeap width) 0 sp sp1 gens c store m dm limit := by
    intro sp sp1 gens total trig gs
    refine ⟨by rw [Flapjack.Compiler.Backend.heapLength_heapExpand]; exact heapBound,
      by rw [Flapjack.Compiler.Backend.heapLength_heapExpand]; omega, shiftLe, lenNz, lenLt, shiftLt, ⟨_, globals⟩,
      curr, _, aligned, otherAligned, currHeap, ?_, ?_, trig, ?_, ?_, ?_, gs, heaps⟩
    · rw [otherHeap, endOfHeap, bytesEq]
    · rw [nextFree]; simp
    · rw [endOfHeap, bytesEq, show 0 + sp + sp1 = limit by omega]
    · rw [heapLen, bytesEq]
    · refine ⟨0, globals, ?_⟩
      rw [globReal]; simp
  rcases kind : c.gcKind with _ | _ | sizes
  · refine ⟨heapExpand limit, limit, 0, limit, 0, .genState 0 [], ?_, ?_, spaceBound,
      Nat.zero_le _⟩
    · refine store_part limit 0 _ (by omega) ?_ ?_
      · rw [triggerGC, kind, bytesEq]; simp
      · rw [genStart]; simp [genStartsInStore, kind]
    · refine ⟨[], absMlInv_init c be limit limit 0 _ (by omega) beEq ?_, by simp⟩
      simp [gcKindInv, kind]
  · refine ⟨heapExpand limit, limit, 0, limit, 0, .genState 0 [], ?_, ?_, spaceBound,
      Nat.zero_le _⟩
    · refine store_part limit 0 _ (by omega) ?_ ?_
      · rw [triggerGC, kind, bytesEq]; simp
      · rw [genStart]; simp [genStartsInStore, kind]
    · refine ⟨[], absMlInv_init c be limit limit 0 _ (by omega) beEq ?_, by simp⟩
      simp [gcKindInv, kind]
  · refine ⟨heapExpand limit, limit, 0, 0, limit, .genState 0 (sizes.map fun _ => 0), ?_, ?_,
      spaceBound, Nat.zero_le _⟩
    · refine store_part 0 limit _ (by omega) ?_ ?_
      · rw [triggerGC, kind]; simp
      · rw [genStart]
        simp only [genStartsInStore, kind, GcKind.generational.injEq]
        rintro _ rfl
        refine ⟨by simp, ?_⟩
        intro x xs h
        cases sizes with
        | nil => simp at h
        | cons _ _ => simp at h; simp [← h.1]
    · exact ⟨[], absMlInv_init c be limit 0 limit _ (by omega) beEq
        (gcKindInv_init_generational c limit sizes kind), by simp⟩

/-- Intersection with the empty tree is empty. Flapjack helper. -/
theorem sptInter_ln_right {α β : Type} (s : Spt α) : sptInter s (.ln : Spt β) = .ln := by
  cases s <;> simp [sptInter]

/-- HOL `state_rel_init`: the initial data state, with HOL's `T` timestamps,
is related to a word state whose store, memory and buffers satisfy
`init_store_ok`. HOL's `t.store ' HeapLength` is `holFapply`, `bytes_in_word`
is `wordSemBytesInWord`, `w2n` is `BitVec.toNat` and `dimword (:α)` is
`2 ^ width`. Source and target share HOL's `'c` and `'ffi` as `C` and `F`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_init"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_init {width : Nat} [NeZero width] {C : Type} {F : Type}
    (t : WordSemStateFiniteExact width C F) (ffi : HolFfiState F) (c : Config)
    (code : Spt (Nat × DataLang.Prog)) (cc : DataSem.Compiler C) (co : DataSem.CompileOracle C)
    (l1 l2 : Nat) (lim : DataSem.Limits)
    (premises : t.ffi = ffi ∧ t.handler = 0 ∧ t.gcFun = WordGcFunctions.wordGcFun c ∧
      codeRel c code t.code ∧
      codeOracleRel c cc co t.store t.compile t.compileOracle t.codeBuffer t.dataBuffer ∧
      goodDimindex width ∧
      sptLookup 0 t.locals = some (.loc l1 l2) ∧
      t.stack = [] ∧
      t.stackMax = some 1 ∧
      t.localsSize = some 0 ∧
      t.stackLimit = lim.stackLimit ∧
      c.lenSize = lim.lengthLimit ∧
      c.be = t.be ∧
      (lim.arch64Bit = true ↔ width = 64) ∧
      lim.heapLimit * (wordSemBytesInWord : BitVec width).toNat < 2 ^ width ∧
      holFapply t.store .heapLength =
        .word (wordSemBytesInWord * BitVec.ofNat width lim.heapLimit) ∧
      lim.hasFpOps = c.hasFpOps ∧
      lim.hasFpTops = c.hasFpTern ∧
      confOk width c ∧
      initStoreOk c t.store t.memory t.mdomain t.codeBuffer t.dataBuffer) :
    stateRel c l1 l2 (DataSem.initialState ffi code co cc true lim t.stackSize t.clock)
      t none [] := by
  obtain ⟨hffi, hhandler, hgc, hcode, horacle, good, hloc, hstack, hmax, hlsize, hslimit,
    hlen, hbe, harch, hheap, hheapLen, hfp, hfpt, conf, init⟩ := premises
  have mem := memoryRel_init c t.be t.store t.memory t.mdomain t.codeBuffer t.dataBuffer
    good conf hbe init
  obtain ⟨limit, curr, -, globals, -, -, -, -, -, -, -, heapLen, -⟩ := init
  have heapLookup : t.store.lookup .heapLength =
      some (.word (wordSemBytesInWord * BitVec.ofNat width lim.heapLimit)) := by
    rw [← hheapLen, holFapply, heapLen]
  have globalsApply : holFapply t.store .globals = .word 0 := by
    rw [holFapply, globals]
  have numbered := impMemoryRel_number c t.be 0 .ln 0 t.store t.memory t.mdomain [] 0
    ⟨good, small_int_0 width good, mem⟩
  unfold stateRel
  refine ⟨hffi, rfl, hhandler, hgc, hcode, horacle, good, conf.1, by simp [DataSem.initialState],
    by simp [globals], fun _ => hloc, by simp [DataSem.initialState],
    by simp [hstack, DataSem.initialState], by simp [hstack], ?_, by simp [hmax, DataSem.initialState, BackendProps.optionLe], rfl, hlsize, ?_, ?_⟩
  · rw [hstack, hlsize, hmax]; simp [wordSemStackSize, BackendProps.optionLe]
  · refine ⟨hslimit.symm, hlen.symm, ?_, ?_, hheap, hfp, hfpt⟩
    · cases h : lim.arch64Bit <;> simp_all [DataSem.initialState]
    · rw [heapLookup]; rfl
  · simpa [DataSem.initialState, globalsApply, hstack, theGlobal, joinEnv, flatStack, adjustSet,
      sptFromAList, sptInter_ln_right, sptToAList, sptFoldi, smallnum_eq_inlined, holThe] using numbered

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

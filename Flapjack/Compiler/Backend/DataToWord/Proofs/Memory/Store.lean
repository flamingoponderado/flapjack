module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Heap
public import Flapjack.Compiler.Backend.GcCombined
public import Flapjack.Misc.Alignment

@[expose] public section

/-! The data-to-word heap assertion tied to the word-machine store. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.GcCombined

/-- Relate a generation state to the stored generation-start word. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gen_starts_in_store_def"
  (words_as_type_indexed_bitvec)]
def genStartsInStore {width : Nat} [NeZero width] (conf : Config) :
    GenState → Option (WordLocW width) → Prop
  | .genState _ starts, some (.word w) =>
      ∀ sizes, conf.gcKind = .generational sizes →
        starts.length = sizes.length ∧
          ∀ x xs, starts = x :: xs → w = StackRemove.bytesInWord width * BitVec.ofNat width x
  | _, _ => False

/-- A related generation start is always stored as a word. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gen_starts_in_store_IMP"
  (words_as_type_indexed_bitvec)]
theorem genStartsInStoreImp {width : Nat} [NeZero width] (conf : Config)
    (gens : GenState) (value : Option (WordLocW width)) :
    genStartsInStore conf gens value → ∃ w : BitVec width, value = some (.word w) := by
  cases gens
  cases value with
  | none => simp [genStartsInStore]
  | some value => cases value <;> simp [genStartsInStore]

/-- Relate the abstract globals pointer and its concrete address. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "glob_real_inv_def"
  (words_as_type_indexed_bitvec)]
def globRealInv {width : Nat} [NeZero width] (conf : Config) (curr : BitVec width)
    (globals globreal : Option (WordLocW width)) : Prop :=
  ∃ w : BitVec width, globals = some (.word w) ∧
    globreal = some (.word (curr + ((w >>> shiftLength conf) <<< wordShiftAmount width)))

/-- The abstract heap occupies the current and alternate word-machine heaps,
with the original store, address bounds, alignment and generation conditions.
Address/store words and abstract heap payload words are independently typed. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_in_memory_store_def"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
noncomputable def heapInMemoryStore {addressWidth : Nat} {valueWidth : Nat}
    [NeZero addressWidth] [NeZero valueWidth]
    (heap : List (HeapElement (WordLocW valueWidth) (HeapTag × List (WordLocW valueWidth))))
    (a sp sp1 : Nat) (gens : GenState) (conf : Config)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW addressWidth))
    (memory : BitVec addressWidth → WordLocW valueWidth) (domain : BitVec addressWidth → Bool)
    (limit : Nat) : Prop :=
  heapLength heap ≤ 2 ^ addressWidth / 2 ^ shiftLength conf ∧
  (heapLength heap + 3) * (addressWidth / 8) < 2 ^ addressWidth ∧
  wordShiftAmount addressWidth ≤ shiftLength conf ∧ conf.lenSize ≠ 0 ∧
  conf.lenSize + 7 < addressWidth ∧ shiftLength conf < addressWidth ∧
  (∃ value, store.lookup .globals = some value) ∧
  ∃ curr other : BitVec addressWidth,
    holByteAligned curr = true ∧ holByteAligned other = true ∧
    store.lookup .currHeap = some (.word curr) ∧
    store.lookup .otherHeap = some (.word other) ∧
    store.lookup .nextFree = some (.word (curr + StackRemove.bytesInWord addressWidth * BitVec.ofNat addressWidth a)) ∧
    store.lookup .triggerGC = some (.word (curr + StackRemove.bytesInWord addressWidth * BitVec.ofNat addressWidth (a + sp))) ∧
    store.lookup .endOfHeap = some (.word (curr + StackRemove.bytesInWord addressWidth * BitVec.ofNat addressWidth (a + sp + sp1))) ∧
    store.lookup .heapLength = some (.word (StackRemove.bytesInWord addressWidth * BitVec.ofNat addressWidth limit)) ∧
    globRealInv conf curr (store.lookup .globals) (store.lookup .globReal) ∧
    genStartsInStore conf gens (store.lookup .genStart) ∧
    SetSep.star (wordHeap curr heap conf) (wordHeap other (heapExpand limit) conf)
      (SetSep.fun2Set (memory, fun addr => domain addr = true))

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

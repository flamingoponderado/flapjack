module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith.Sep
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Store
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Heap
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Abstract

@[expose] public section

/-! `AnyArith_thm`: splitting the free heap space reserved by `AllocVar`
(Flapjack-only helper following the HOL proof's `heap_lookup_SPLIT` step). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- The part of the memory that `AnyArith_code` leaves untouched. -/
def splitFrame {width : Nat} [NeZero width] (c : Config) (curr other : BitVec width)
    (ha hb : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (n k limit : Nat) : ((BitVec width × WordLocW width) → Prop) → Prop :=
  let b := StackRemove.bytesInWord width
  let u := curr + b * BitVec.ofNat width (heapLength ha)
  SetSep.star (wordHeap curr ha c)
    (SetSep.star (Misc.wordListExists (u + b + b * BitVec.ofNat width n) k)
      (SetSep.star (wordHeap (u + b + b * BitVec.ofNat width n + b * BitVec.ofNat width k) hb c)
        (wordHeap (other + b) (heapExpand (limit - 1)) c)))

theorem wordListExists_split3 {width : Nat} [NeZero width] {β : Type} (a : BitVec width) (n k : Nat) :
    Misc.wordListExists (β := β) a (n + k + 1) =
      SetSep.star (Misc.wordListExists a 1)
        (SetSep.star (Misc.wordListExists (a + StackRemove.bytesInWord width) n)
          (Misc.wordListExists (a + StackRemove.bytesInWord width +
            StackRemove.bytesInWord width * BitVec.ofNat width n) k)) := by
  rw [show n + k + 1 = 1 + (n + k) by omega, StackRemove.Proofs.WordListMemory.wordListExistsAdd,
    StackRemove.Proofs.WordListMemory.wordListExistsAdd]
  simp

/-- Decomposition of the memory relation once `AllocVar` has reserved `n + 1`
words (HOL: the `heap_lookup_SPLIT`, `word_list_exists_ADD` and
`word_heap_non_empty_limit` steps of `AnyArith_thm`). -/
theorem heap_split {width : Nat} [NeZero width] {c : Config} {be : Bool} {ts : Nat}
    {refs : Spt (BvlSem.Ref DataSem.Value)} {space : Nat}
    {store : HolFiniteMapExact WordStoreHOL (WordLocW width)}
    {m : BitVec width → WordLocW width} {dm : BitVec width → Bool}
    {vars : List (DataSem.Value × WordLocW width)} {n : Nat}
    (mem : memoryRel c be ts refs space store m dm vars) (hsp : space = n + 1) :
    ∃ (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
      (limit a sp sp1 : Nat) (gens : GcCombined.GenState)
      (ha hb : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
      (k : Nat) (curr other : BitVec width) (x0 ow : WordLocW width) (xs : List (WordLocW width)),
      heapInMemoryStore heap a sp sp1 gens c store m dm limit ∧
      wordMlInv (heap, be, a, sp, sp1, gens) limit ts c refs vars ∧
      (limit + 3) * (width / 8) + 1 < 2 ^ width ∧ space ≤ sp ∧
      heap = ha ++ .unused (n + k) :: hb ∧ a = heapLength ha ∧ sp + sp1 = n + 1 + k ∧
      limit ≠ 0 ∧ xs.length = n ∧
      store.lookup .currHeap = some (.word curr) ∧ store.lookup .otherHeap = some (.word other) ∧
      store.lookup .nextFree = some (.word (curr + StackRemove.bytesInWord width *
        BitVec.ofNat width (heapLength ha))) ∧
      SetSep.star
        (Misc.wordList (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength ha) +
          StackRemove.bytesInWord width) xs)
        (SetSep.star (SetSep.one (curr + StackRemove.bytesInWord width *
            BitVec.ofNat width (heapLength ha), x0))
          (SetSep.star (SetSep.one (other, ow)) (splitFrame c curr other ha hb n k limit)))
        (SetSep.fun2Set (m, fun x => dm x = true)) := by
  obtain ⟨heap, limit, a, sp, sp1, gens, hims, wml, lim, spLe⟩ := mem
  have hims0 := hims
  have wml0 := wml
  obtain ⟨roots, abs, _⟩ := wml
  have usi := abs.2.2.2.1
  have hok := abs.2.1
  have look : heapLookup a heap = some (.unused (sp + sp1 - 1)) := usi.1 (by omega)
  obtain ⟨ha, hb, hheap, ha_len⟩ := heapLookup_split heap a _ look
  have hlen : heapLength heap = limit := hok.1
  obtain ⟨k, hk⟩ : ∃ k, sp + sp1 - 1 = n + k := ⟨sp + sp1 - 1 - n, by omega⟩
  rw [hk] at hheap
  have limNZ : limit ≠ 0 := by
    rw [← hlen, hheap]; simp [heapLength, elLength]
  obtain ⟨_, _, _, _, _, _, _, curr, other, _, _, hcurr, hother, hnext, _, _, _, _, _, H⟩ := hims
  rw [hheap, wordHeapAppend, wordHeap, wordEl, wordListExists_split3,
    Gc.wordHeap_nonEmptyLimit limNZ] at H
  set b := StackRemove.bytesInWord width
  set u := curr + b * BitVec.ofNat width (heapLength ha)
  have hbAddr : u + b * BitVec.ofNat width (elLength (HeapElement.unused (α := WordLocW width)
      (β := HeapTag × List (WordLocW width)) (n + k))) =
      u + b + b * BitVec.ofNat width n + b * BitVec.ofNat width k := by
    simp only [elLength, BitVec.ofNat_add]
    rw [show (1#width : BitVec width) = 1 from rfl]; ring
  rw [hbAddr, show (wordSemBytesInWord : BitVec width) = b from rfl] at H
  rw [SetSep.starComm _ (SetSep.sepExists _), starExists_left] at H
  obtain ⟨ow, H⟩ := H
  set A := wordHeap curr ha c
  set Wn := Misc.wordListExists (β := WordLocW width) (u + b) n
  set Wk := Misc.wordListExists (β := WordLocW width) (u + b + b * BitVec.ofNat width n) k
  set B := wordHeap (valueWidth := width) (u + b + b * BitVec.ofNat width n + b * BitVec.ofNat width k) hb c
  set O := wordHeap (valueWidth := width) (other + b) (heapExpand (limit - 1)) c
  rw [show SetSep.star (SetSep.star (SetSep.one (other, ow)) O)
      (SetSep.star A (SetSep.star (SetSep.star (Misc.wordListExists u 1) (SetSep.star Wn Wk)) B)) =
      SetSep.star (Misc.wordListExists u 1) (SetSep.star Wn (SetSep.star (SetSep.one (other, ow))
        (SetSep.star A (SetSep.star Wk (SetSep.star B O))))) by ac_rfl] at H
  obtain ⟨xs1, l1, H⟩ := starWordListExists_left _ _ _ _ H
  obtain ⟨x0, rfl⟩ : ∃ x0, xs1 = [x0] := by
    match xs1, l1 with
    | [x0], _ => exact ⟨x0, rfl⟩
  rw [wordList_single, show SetSep.star (SetSep.one (u, x0)) (SetSep.star Wn
      (SetSep.star (SetSep.one (other, ow)) (SetSep.star A (SetSep.star Wk (SetSep.star B O))))) =
      SetSep.star Wn (SetSep.star (SetSep.one (u, x0))
      (SetSep.star (SetSep.one (other, ow)) (SetSep.star A (SetSep.star Wk (SetSep.star B O))))) by
      ac_rfl] at H
  obtain ⟨xs, lxs, H⟩ := starWordListExists_left _ _ _ _ H
  refine ⟨heap, limit, a, sp, sp1, gens, ha, hb, k, curr, other, x0, ow, xs, hims0, wml0,
    lim, spLe, hheap, ha_len, by omega, limNZ, lxs, hcurr, hother, ?_, H⟩
  rw [hnext, ha_len]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith

module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalList
public import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListExists

@[expose] public section

/-! Relating encoded heap elements to their concrete word lists. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.StackRemove.WordListExists

/-- An encoded heap element has a concrete word-list representation that can
be reused at any address and memory with the same domain. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_el_eq_word_list"
  (words_as_type_indexed_bitvec)]
theorem wordEl_eq_wordList {addressWidth : Nat} {valueWidth : Nat}
    [NeZero addressWidth] [NeZero valueWidth]
    (element : HeapElement (WordLocW valueWidth) (HeapTag × List (WordLocW valueWidth)))
    (curr : BitVec addressWidth) (frame : ((BitVec addressWidth × WordLocW valueWidth) → Prop) → Prop)
    (memory : BitVec addressWidth → WordLocW valueWidth) (domain : BitVec addressWidth → Prop)
    (conf : Config)
    (separated : SetSep.star (wordEl curr element conf) frame (SetSep.fun2Set (memory, domain))) :
    ∃ xs : List (WordLocW valueWidth),
      SetSep.star (Misc.wordList curr xs) frame (SetSep.fun2Set (memory, domain)) ∧
      elLength element = xs.length ∧
      ∀ (frame1 : ((BitVec addressWidth × WordLocW valueWidth) → Prop) → Prop)
        (curr1 : BitVec addressWidth) (memory1 : BitVec addressWidth → WordLocW valueWidth),
        SetSep.star (Misc.wordList curr1 xs) frame1 (SetSep.fun2Set (memory1, domain)) →
        SetSep.star (wordEl curr1 element conf) frame1 (SetSep.fun2Set (memory1, domain)) := by
  cases element with
  | unused len =>
    rcases separated with ⟨cells, rest, partition, element, framed⟩
    obtain ⟨xs, words, length⟩ : ∃ xs : List (WordLocW valueWidth),
        Misc.wordList curr xs cells ∧ xs.length = len + 1 := by
      simpa [wordEl, Misc.wordListExists, SetSep.sepExists, starCond] using element
    refine ⟨xs, ⟨cells, rest, partition, words, framed⟩, ?_, ?_⟩
    · simpa [elLength] using length.symm
    · intro frame1 curr1 memory1 assertion
      rcases assertion with ⟨cells1, rest1, split1, words1, framed1⟩
      refine ⟨cells1, rest1, split1, ?_, framed1⟩
      change Misc.wordListExists curr1 (len + 1) cells1
      exact ⟨xs, (starCond _ _ _).mpr ⟨words1, length⟩⟩
  | forwardPointer index old len =>
    rcases separated with ⟨cells, rest, partition, element, framed⟩
    rcases element with ⟨head, tail, split, headWord, tailExists⟩
    obtain ⟨xs, words, length⟩ : ∃ xs : List (WordLocW valueWidth),
        Misc.wordList (curr + StackRemove.bytesInWord addressWidth) xs tail ∧ xs.length = len := by
      simpa [Misc.wordListExists, SetSep.sepExists, starCond] using tailExists
    let value : WordLocW valueWidth := .word (BitVec.ofNat valueWidth index <<< (2 : Nat))
    refine ⟨value :: xs, ⟨cells, rest, partition, ⟨head, tail, split, headWord, words⟩, framed⟩, ?_, ?_⟩
    · simp [elLength, length]
    · intro frame1 curr1 memory1 assertion
      rcases assertion with ⟨cells1, rest1, split1, ⟨head1, tail1, split2, word1, words1⟩, framed1⟩
      refine ⟨cells1, rest1, split1, ⟨head1, tail1, split2, word1, ?_⟩, framed1⟩
      exact ⟨xs, (starCond _ _ _).mpr ⟨words1, length⟩⟩
  | dataElement addresses len data =>
    rcases data with ⟨tag, payload⟩
    cases encoded : wordPayload (headerWidth := valueWidth) addresses len tag payload conf with
    | mk header result =>
      rcases result with ⟨words, valid⟩
      rcases separated with ⟨cells, rest, partition, element, framed⟩
      obtain ⟨wordsHeap, conditions⟩ := (starCond _ _ _).mp (by simpa [wordEl, encoded] using element)
      have length := wordPayloadImp addresses len tag payload conf header words (by simpa [conditions.2.2] using encoded)
      refine ⟨.word header :: words, ⟨cells, rest, partition, wordsHeap, framed⟩, ?_, ?_⟩
      · simp [elLength, length]
      · intro frame1 curr1 memory1 assertion
        rcases assertion with ⟨cells1, rest1, split1, words1, framed1⟩
        refine ⟨cells1, rest1, split1, ?_, framed1⟩
        simpa [wordEl, encoded] using (starCond _ _ _).mpr ⟨words1, conditions⟩

private theorem starSwap {α : Type} (p q r : (α → Prop) → Prop) :
    SetSep.star p (SetSep.star q r) = SetSep.star q (SetSep.star p r) := by
  rw [SetSep.starAssoc, SetSep.starComm p q, ← SetSep.starAssoc]

/-- A whole encoded heap has a reusable word-list representation of exactly
the abstract heap length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_heap_eq_word_list_strong"
  (words_as_type_indexed_bitvec)]
theorem wordHeap_eq_wordList_strong {width : Nat} [NeZero width]
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr : BitVec width) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Prop) (conf : Config)
    (separated : SetSep.star (wordHeap curr heap conf) frame (SetSep.fun2Set (memory, domain))) :
    ∃ xs : List (WordLocW width),
      SetSep.star (Misc.wordList curr xs) frame (SetSep.fun2Set (memory, domain)) ∧
      heapLength heap = xs.length ∧
      ∀ (curr1 : BitVec width) (frame1 : ((BitVec width × WordLocW width) → Prop) → Prop)
        (memory1 : BitVec width → WordLocW width),
        SetSep.star (Misc.wordList curr1 xs) frame1 (SetSep.fun2Set (memory1, domain)) →
        SetSep.star (wordHeap curr1 heap conf) frame1 (SetSep.fun2Set (memory1, domain)) := by
  induction heap generalizing curr frame memory with
  | nil =>
    refine ⟨[], ?_, by simp [heapLength], ?_⟩
    · simpa [wordHeap, Misc.wordList] using separated
    · intro curr1 frame1 memory1 assertion
      simpa [wordHeap, Misc.wordList] using assertion
  | cons head tail ih =>
    let next := curr + StackRemove.bytesInWord width * BitVec.ofNat width (elLength head)
    have initial : SetSep.star (wordEl curr head conf)
        (SetSep.star (wordHeap next tail conf) frame) (SetSep.fun2Set (memory, domain)) := by
      simpa only [wordHeap, ← SetSep.starAssoc, next] using separated
    obtain ⟨xs, first, length, restoreHead⟩ :=
      wordEl_eq_wordList head curr (SetSep.star (wordHeap next tail conf) frame) memory domain conf initial
    have rotated := first
    rw [starSwap] at rotated
    obtain ⟨ys, second, tailLength, restoreTail⟩ :=
      ih next (SetSep.star (Misc.wordList curr xs) frame) memory rotated
    have nextEq : next = curr + StackRemove.bytesInWord width * BitVec.ofNat width xs.length := by
      simp [next, length]
    refine ⟨xs ++ ys, ?_, ?_, ?_⟩
    · rw [StackRemove.StackHeap.wordListAppend, ← SetSep.starAssoc]
      rw [← nextEq, starSwap]
      exact second
    · simp only [heapLength, List.map_cons, List.sum_cons, List.length_append]
      rw [length, ← tailLength]
      rfl
    · intro curr1 frame1 memory1 assertion
      rw [StackRemove.StackHeap.wordListAppend, ← SetSep.starAssoc, starSwap] at assertion
      have tailRestored := restoreTail
        (curr1 + StackRemove.bytesInWord width * BitVec.ofNat width xs.length)
        (SetSep.star (Misc.wordList curr1 xs) frame1) memory1 assertion
      rw [starSwap] at tailRestored
      have headRestored := restoreHead (SetSep.star
        (wordHeap (curr1 + StackRemove.bytesInWord width * BitVec.ofNat width xs.length) tail conf) frame1)
        curr1 memory1 tailRestored
      simpa only [wordHeap, ← SetSep.starAssoc, length] using headRestored

/-- Every represented heap occupies a concrete list of its abstract length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_heap_eq_word_list"
  (words_as_type_indexed_bitvec)]
theorem wordHeap_eq_wordList {width : Nat} [NeZero width]
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr : BitVec width) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Prop) (conf : Config)
    (separated : SetSep.star (wordHeap curr heap conf) frame (SetSep.fun2Set (memory, domain))) :
    ∃ xs : List (WordLocW width),
      SetSep.star (Misc.wordList curr xs) frame (SetSep.fun2Set (memory, domain)) ∧
      heapLength heap = xs.length := by
  obtain ⟨xs, assertion, length, _⟩ := wordHeap_eq_wordList_strong heap curr frame memory domain conf separated
  exact ⟨xs, assertion, length⟩

/-- A separated word list in a functional memory cannot wrap around and
reuse its starting address. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_list_IMP_limit"
  (words_as_type_indexed_bitvec)]
theorem wordList_imp_limit {width : Nat} [NeZero width] {β : Type}
    (curr : BitVec width) (values : List β) (frame : ((BitVec width × β) → Prop) → Prop)
    (memory : BitVec width → β) (domain : BitVec width → Prop)
    (separated : SetSep.star (Misc.wordList curr values) frame (SetSep.fun2Set (memory, domain)))
    (good : goodDimindex width) : values.length ≤ 2 ^ width / (width / 8) := by
  let period := 2 ^ width / (width / 8)
  have positive : 0 < period := by
    dsimp [period]
    rcases good with rfl | rfl <;> decide
  have cycle : StackRemove.bytesInWord width * BitVec.ofNat width period = 0 := by
    dsimp [period]
    rcases good with rfl | rfl <;> decide
  by_contra tooLong
  have greater : period < values.length := by omega
  cases values with
  | nil => simp at greater
  | cons value values =>
    have bound : period - 1 < values.length := by simp only [List.length_cons] at greater; omega
    rcases separated with ⟨cells, frameHeap, outer, listHeap, framed⟩
    rcases listHeap with ⟨head, tail, inner, singleton, listTail⟩
    have memberHead : head (curr, value) := by rw [singleton]
    have memberTail := StackRemove.StackHeap.wordListNth
      (curr + StackRemove.bytesInWord width) values tail (period - 1) bound listTail
    have number : BitVec.ofNat width (period - 1) + 1 = BitVec.ofNat width period := by
      change BitVec.ofNat width (period - 1) + BitVec.ofNat width 1 = BitVec.ofNat width period
      rw [← BitVec.ofNat_add]
      congr 1
      omega
    have address : curr + StackRemove.bytesInWord width +
        StackRemove.bytesInWord width * BitVec.ofNat width (period - 1) = curr := by
      calc
        _ = curr + StackRemove.bytesInWord width * (BitVec.ofNat width (period - 1) + 1) := by
          simp only [BitVec.mul_add]
          ac_rfl
        _ = curr := by rw [number, cycle]; simp
    rw [address] at memberTail
    have headGraph : SetSep.fun2Set (memory, domain) (curr, value) := by
      rw [← outer.1, ← inner.1]
      exact Or.inl (Or.inl memberHead)
    have tailGraph : SetSep.fun2Set (memory, domain) (curr, values[period - 1]) := by
      rw [← outer.1, ← inner.1]
      exact Or.inl (Or.inr memberTail)
    have same : value = values[period - 1] :=
      ((SetSep.fun2SetThm memory domain curr value).mp headGraph).1.symm.trans
        ((SetSep.fun2SetThm memory domain curr values[period - 1]).mp tailGraph).1
    rw [same] at memberHead
    exact inner.2 _ ⟨memberHead, memberTail⟩

/-- A represented heap fits in the machine address space measured in words. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_heap_IMP_limit"
  (words_as_type_indexed_bitvec)]
theorem wordHeap_imp_limit {width : Nat} [NeZero width]
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr : BitVec width) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Prop) (conf : Config)
    (separated : SetSep.star (wordHeap curr heap conf) frame (SetSep.fun2Set (memory, domain)))
    (good : goodDimindex width) : heapLength heap ≤ 2 ^ width / (width / 8) := by
  obtain ⟨xs, assertion, length⟩ := wordHeap_eq_wordList heap curr frame memory domain conf separated
  rw [length]
  exact wordList_imp_limit curr xs frame memory domain assertion good

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Memcpy
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PointerAddress
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MoveForward
public import Flapjack.Compiler.Backend.GcShared.ForwardPtr
public import Flapjack.Compiler.Backend.CopyingGc
public import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListExists

@[expose] public section

/-! Concrete data-element copying for the copying-collector simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private theorem exposeCell {α : Type} (p w q s d f : (α → Prop) → Prop) :
    SetSep.star (SetSep.star (SetSep.star p (SetSep.star (SetSep.star w q) s)) d) f =
      SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star f p) s) w) d) q := by
  simp only [← SetSep.starAssoc]
  rw [star_swap_first q s, star_swap_first q d, SetSep.starComm q f,
    star_swap_first d f, star_swap_first s f, star_swap_first w f,
    star_swap_first p f, star_swap_first w s]

private theorem exposeCopy {α : Type} (r w d z : (α → Prop) → Prop) :
    SetSep.star (SetSep.star r w) (SetSep.star d z) =
      SetSep.star (SetSep.star (SetSep.star r z) w) d := by
  simp only [← SetSep.starAssoc]
  rw [SetSep.starComm d z, star_swap_first w z]

private theorem exposeWrite {α : Type} (r a x d : (α → Prop) → Prop) :
    SetSep.star (SetSep.star r (SetSep.star a x)) d =
      SetSep.star a (SetSep.star (SetSep.star r x) d) := by
  simp only [← SetSep.starAssoc]
  rw [star_swap_first r a]

private theorem reassemble {α : Type} (p a e s d z f : (α → Prop) → Prop) :
    SetSep.star (SetSep.star (SetSep.star (SetSep.star p (SetSep.star (SetSep.star a e) s)) d) z) f =
      SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star f p) s) z) e) d) a := by
  simp only [← SetSep.starAssoc]
  rw [SetSep.starComm z f, star_swap_first d f, star_swap_first s f, star_swap_first e f,
    star_swap_first a f, star_swap_first p f, SetSep.starComm d z, star_swap_first e s,
    star_swap_first a s, star_swap_first e z, star_swap_first a z, star_swap_first a e,
    SetSep.starComm a d]

private theorem starMono {α : Type} {p p' q q' : (α → Prop) → Prop}
    (hp : ∀ h, p h → p' h) (hq : ∀ h, q h → q' h) (heap : α → Prop)
    (assertion : SetSep.star p q heap) : SetSep.star p' q' heap := by
  obtain ⟨left, right, split, pl, qr⟩ := assertion
  exact ⟨left, right, split, hp left pl, hq right qr⟩

private theorem starEmptyRight {α : Type} (p : (α → Prop) → Prop) : SetSep.star p SetSep.emp = p := by
  rw [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft]

theorem updateAddr_data {width : Nat} [NeZero width] (conf : Config)
    (index forwarded : Nat) (value : WordLocW width) :
    updateAddr conf (BitVec.ofNat width forwarded) (getAddr conf index value) =
      getAddr conf forwarded value := by
  have shiftTwo : 2 ≤ shiftLength conf := by simp [shiftLength]; omega
  have shiftEq : ((BitVec.ofNat width forwarded <<< (2 : Nat)) >>> (2 : Nat)) <<< shiftLength conf =
      BitVec.ofNat width forwarded <<< shiftLength conf := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    by_cases h : i < shiftLength conf
    · simp [h]
    · have h1 : 2 + (i - shiftLength conf) < width := by omega
      have h2 : i - shiftLength conf < width := by omega
      have h3 : ¬2 + (i - shiftLength conf) < 2 := by omega
      simp [h, h1, h2, h3]
  calc
    updateAddr conf (BitVec.ofNat width forwarded) (getAddr conf index value) =
        updateAddr conf ((BitVec.ofNat width forwarded <<< (2 : Nat)) >>> (2 : Nat))
          (getAddr conf index value) := by simp only [updateAddr, shiftEq]
    _ = getAddr conf forwarded value := updateAddr_forward conf index forwarded value

/-- Expose a data element's exact source word list and payload checks while
preserving the surrounding heap, free-space list and frame. This is local
separation infrastructure for the data-element collector case. -/
theorem wordHeap_dataCell {width : Nat} [NeZero width] (conf : Config)
    (before after : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (addresses : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width)) (curr pa : BitVec width) (xs : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (separated : SetSep.star
      (SetSep.star (wordHeap curr (before ++ .dataElement addresses len (tag, payload) :: after) conf)
        (Misc.wordList pa xs)) frame (SetSep.fun2Set (memory, fun address => domain address = true))) :
    ∃ (header : BitVec width) (words : List (WordLocW width)),
      wordPayload addresses len tag payload conf = (header, words, true) ∧
      words.length = len ∧ words.length < 2 ^ (width - 4) ∧
      decodeLength conf header = BitVec.ofNat width words.length ∧
      SetSep.star (SetSep.star
        (SetSep.star (SetSep.star frame (wordHeap curr before conf))
          (wordHeap (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength before) +
            StackRemove.bytesInWord width * BitVec.ofNat width (len + 1)) after conf))
        (Misc.wordList (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength before))
          (.word header :: words))) (Misc.wordList pa xs)
        (SetSep.fun2Set (memory, fun address => domain address = true)) := by
  generalize payloadEq : wordPayload (headerWidth := width) addresses len tag payload conf = result
  rcases result with ⟨header, words, valid⟩
  rw [wordHeapAppend] at separated
  simp only [wordHeap, wordEl, payloadEq, elLength] at separated
  rw [exposeCell] at separated
  obtain ⟨lists, bound, decoded, validEq⟩ :=
    (StackRemove.WordListExists.starCond _ _ _).mp separated
  subst valid
  exact ⟨header, words, rfl, wordPayloadImp _ _ _ _ _ _ _ payloadEq, bound, decoded, lists⟩

/-- The data-element case of the copying collector move simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_move_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGcMove_dataElement {width : Nat} [NeZero width] (conf : Config)
    (ptr len : Nat) (value : WordLocW width) (addresses : List (HeapAddress (WordLocW width)))
    (tag : HeapTag) (payload : List (WordLocW width)) (a n limit a1 n1 : Nat)
    (heap heap1 h1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr pa pa1 i1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (x1 : HeapAddress (WordLocW width)) (w : WordLocW width) (c1 : Bool)
    (found : heapLookup ptr heap = some (.dataElement addresses len (tag, payload)))
    (abstractRun : CopyingGc.gcMove (.pointer ptr value, [], a, n, heap, true, limit) =
      (x1, h1, a1, n1, heap1, true))
    (heapBound : heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (separated : SetSep.star (SetSep.star (wordHeap curr heap conf) (Misc.wordList pa xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (wordRun : wordGcMove conf (wordAddr conf (.pointer ptr value), BitVec.ofNat width a, pa,
      curr, memory, domain) = (w, i1, pa1, memory1, c1)) (length : xs.length = n) :
    ∃ xs1,
      SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap1 conf) (wordHeap pa h1 conf))
        (Misc.wordList pa1 xs1)) frame (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      w = wordAddr conf x1 ∧ heapLength heap1 = heapLength heap ∧ c1 = true ∧
      i1 = BitVec.ofNat width a1 ∧ n1 = xs1.length ∧
      pa1 = pa + wordSemBytesInWord * BitVec.ofNat width (heapLength h1) := by
  obtain ⟨before, after, heapEq, ptrEq⟩ := heapLookup_split heap ptr _ found
  have forward (ok : Bool) : gcForwardPtr ptr heap a value ok =
      (before ++ .forwardPointer a value len :: after, ok) := by
    rw [heapEq, ptrEq]
    exact gcForwardPtr_thm before after addresses len (tag, payload) a value ok
  simp only [CopyingGc.gcMove, found, Bool.true_and, forward, List.nil_append,
    Prod.mk.injEq, Bool.and_eq_true, decide_eq_true_eq] at abstractRun
  obtain ⟨rfl, rfl, rfl, rfl, rfl, space, _⟩ := abstractRun
  obtain ⟨header, words, encoded, wordLen, wordBound, decoded, cell⟩ :=
    wordHeap_dataCell conf before after addresses len tag payload curr pa xs memory domain frame
      (by simpa only [← heapEq] using separated)
  let src := curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr
  have read : memory src = .word header ∧ domain src = true := by
    have graph : SetSep.fun2Set (memory, fun address => domain address = true) (src, .word header) := by
      rcases cell with ⟨sourceAndFrame, free, outSplit, sourceAndFrameAssert, _⟩
      rcases sourceAndFrameAssert with ⟨rest, source, sourceSplit, _, sourceAssert⟩
      have entry := StackRemove.StackHeap.wordListNth
        (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength before))
        (.word header :: words) source 0 (by simp) sourceAssert
      rw [← outSplit.1, ← sourceSplit.1]
      apply Or.inl
      apply Or.inr
      simpa [src, ptrEq] using entry
    exact (SetSep.fun2SetThm memory _ _ _).mp graph
  have ptrBound : ptr * 2 ^ shiftLength conf < 2 ^ width := by
    have ptrInHeap := heapLookup_less heap ptr (.dataElement addresses len (tag, payload)) found
    have below : ptr < 2 ^ width / 2 ^ shiftLength conf := Nat.lt_of_lt_of_le ptrInHeap heapBound
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right below (Nat.two_pow_pos _)) (Nat.div_mul_le_self _ _)
  have low : getAddr conf ptr value &&& (1 : BitVec width) ≠ 0 := by
    simpa only [BitVec.and_comm] using getAddr_and_one_ne_zero conf ptr value
  have address : ptrToAddr conf curr (getAddr conf ptr value) = src := by
    simpa only [src, wordSemBytesInWord, StackRemove.bytesInWord, BitVec.mul_comm] using
      ptrToAddr_getAddr conf curr ptr value ptrBound
  have notForward : wordSemIsFwdPtr (.word header) = false :=
    wordPayload_not_fwdPtr conf addresses len tag payload header words true encoded
  have copySize : len + 1 ≤ xs.length := by omega
  have widthPos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  have expLt : width - 4 < width := by omega
  have powLt : 2 ^ (width - 4) < 2 ^ width := Nat.pow_lt_pow_right (by decide : 1 < 2) expLt
  have copyBound : (WordLocW.word header :: words).length < 2 ^ width := by
    simp only [List.length_cons, wordLen]; omega
  have splitXs : xs = xs.take (len + 1) ++ xs.drop (len + 1) := (List.take_append_drop _ _).symm
  rw [splitXs, StackRemove.StackHeap.wordListAppend, exposeCopy] at cell
  have takeLen : (xs.take (len + 1)).length = (WordLocW.word header :: words).length := by
    simp [List.length_take, Nat.min_eq_left copySize, wordLen]
  simp only [wordAddr, wordGcMove, if_neg low, address, read.1, read.2, wordSemTheWord,
    wordSemIsWordLoc, notForward, Bool.false_eq_true, ↓reduceIte, Bool.true_and,
    decoded] at wordRun
  have countEq : BitVec.ofNat width words.length + 1 =
      BitVec.ofNat width (WordLocW.word header :: words).length := by
    simp [BitVec.ofNat_add]
  rw [countEq] at wordRun
  generalize copyRun : memcpy (BitVec.ofNat width (WordLocW.word header :: words).length)
    src pa memory domain = copyResult at wordRun
  rcases copyResult with ⟨copyEnd, copyMemory, copyOk⟩
  simp only [Prod.mk.injEq] at wordRun
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
  have copied := memcpyCorrect (.word header :: words) src copyOk pa memory copyMemory domain copyEnd
    (xs.take (len + 1)) _ copyRun takeLen copyBound (by
      simpa only [src, ptrEq] using cell)
  obtain ⟨copied, endEq, copyGood⟩ := copied
  rw [show Misc.wordList src (.word header :: words) =
      SetSep.star (SetSep.one (src, WordLocW.word header))
        (Misc.wordList (src + StackRemove.bytesInWord width) words) from rfl,
    exposeWrite] at copied
  have written := SetSep.writeFun2Set (.word (BitVec.ofNat width a <<< (2 : Nat))) src (.word header)
    _ copyMemory (fun address => domain address = true) copied
  have updateGraph : SetSep.fun2Set
      (gcUpdate src (.word (BitVec.ofNat width a <<< (2 : Nat))) copyMemory,
        fun address => domain address = true) =
      SetSep.fun2Set ((fun key => @ite _ (key = src) (Classical.propDecidable _)
        (.word (BitVec.ofNat width a <<< (2 : Nat))) (copyMemory key)),
        fun address => domain address = true) := by
    funext entry
    rcases entry with ⟨key, val⟩
    simp only [SetSep.fun2SetThm, gcUpdate]
    by_cases h : key = src
    · subst key
      simp only [ite_true]
    · have h' : src ≠ key := Ne.symm h
      simp only [h, h', ite_false]
  refine ⟨xs.drop (len + 1), ?_, ?_, ?_, copyGood, ?_, ?_, ?_⟩
  · rw [updateGraph]
    simp only [wordHeapAppend, wordHeap, wordEl, encoded, elLength, starEmptyRight]
    have pureEq : SetSep.star (Misc.wordList pa (.word header :: words))
        (SetSep.cond (words.length < 2 ^ (width - 4) ∧
          decodeLength conf header = BitVec.ofNat width words.length ∧ True)) =
        Misc.wordList pa (.word header :: words) := by
      funext h
      apply propext
      simp only [StackRemove.WordListExists.starCond, wordBound, decoded, and_self, and_true]
    rw [pureEq, reassemble]
    have takeEq : (xs.take (len + 1)).length = len + 1 := by
      simp [List.length_take, Nat.min_eq_left copySize]
    have endEq' : copyEnd = pa + StackRemove.bytesInWord width * BitVec.ofNat width (len + 1) := by
      simpa [List.length_cons, wordLen, wordSemBytesInWord, StackRemove.bytesInWord,
        BitVec.mul_comm] using endEq
    rw [endEq', ← ptrEq]
    simp only [takeEq, src, ← ptrEq] at written
    simp only [← SetSep.starAssoc] at written ⊢
    have promote : ∀ h, Misc.wordList
        (curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr + StackRemove.bytesInWord width)
        words h → Misc.wordListExists
          (curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr + StackRemove.bytesInWord width)
          len h := by
      intro h assertion
      exact ⟨words, (StackRemove.WordListExists.starCond _ _ _).mpr ⟨assertion, wordLen⟩⟩
    refine starMono (fun _ h => h) ?_ _ written
    intro h h1
    refine starMono (fun _ h => h) ?_ _ h1
    intro h h2
    refine starMono (fun _ h => h) ?_ _ h2
    intro h h3
    refine starMono (fun _ h => h) ?_ _ h3
    intro h h4
    exact starMono promote (fun _ h => h) _ h4
  · simp only [wordAddr, updateAddr_data]
  · rw [heapEq]
    simp [heapLength, elLength]
  · simp [wordLen, BitVec.ofNat_add, BitVec.add_assoc]
  · simp only [List.length_drop]
    omega
  · simpa [heapLength, elLength, wordLen, wordSemBytesInWord, StackRemove.bytesInWord,
      BitVec.mul_comm] using endEq

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

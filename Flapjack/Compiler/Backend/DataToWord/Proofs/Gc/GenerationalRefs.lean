module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.HeapWordList
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalInvariant
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PayloadSwap

@[expose] public section

/-! Major collector reference-scan simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

instance generationalRefsInst1 {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩
instance generationalRefsInst2 {α : Type} : Std.Commutative (SetSep.star (α := α)) := ⟨SetSep.starComm⟩

/-- Expose the reference header and its pointer list from the represented heap.
This local factoring of the reference-scan proof has no separate HOL original. -/
theorem refScan_dataCell {width : Nat} [NeZero width] (conf : Config)
    (before after : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (roots : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width)) (base free : BitVec width) (xs : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (mutable : isMutTag tag)
    (separated : SetSep.star
      (SetSep.star (wordHeap base (before ++ .dataElement roots len (tag, payload) :: after) conf)
        (Misc.wordList free xs)) frame (SetSep.fun2Set (memory, fun address => domain address = true))) :
    ∃ header : BitVec width,
      wordPayload roots len tag payload conf = (header, roots.map (wordAddr conf), true) ∧
      roots.length = len ∧ roots.length < 2 ^ (width - 4) ∧
      decodeLength conf header = BitVec.ofNat width roots.length ∧
      memory (base + wordSemBytesInWord * BitVec.ofNat width (heapLength before)) = .word header ∧
      domain (base + wordSemBytesInWord * BitVec.ofNat width (heapLength before)) = true ∧
      SetSep.star (SetSep.star (Misc.wordList free xs)
        (Misc.wordList (base + wordSemBytesInWord * BitVec.ofNat width (heapLength before) + wordSemBytesInWord)
          (roots.map (wordAddr conf))))
        (SetSep.star (SetSep.one (base + wordSemBytesInWord * BitVec.ofNat width (heapLength before), .word header))
          (SetSep.star (SetSep.star frame (wordHeap base before conf))
            (wordHeap (base + wordSemBytesInWord * BitVec.ofNat width (heapLength before) +
              wordSemBytesInWord * BitVec.ofNat width (len + 1)) after conf)))
        (SetSep.fun2Set (memory, fun address => domain address = true)) := by
  obtain ⟨header, words, encoded, wordLen, bound, decoded, cell⟩ :=
    wordHeap_dataCell conf before after roots len tag payload base free xs memory domain frame separated
  obtain ⟨_, mapped, _⟩ := isMutTag_wordPayloadImp roots len tag payload conf header words true encoded mutable
  subst words
  simp only [List.length_map] at wordLen bound decoded
  let addr := base + wordSemBytesInWord * BitVec.ofNat width (heapLength before)
  let left := SetSep.star frame (wordHeap base before conf)
  let right := wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) after conf
  have reassembled : SetSep.star (SetSep.one (addr, WordLocW.word header))
      (SetSep.star (SetSep.star (Misc.wordList free xs)
        (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf))))
        (SetSep.star left right)) (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    simp only [Misc.wordList] at cell
    change SetSep.star (SetSep.star (SetSep.star left right)
      (SetSep.star (SetSep.one (addr, WordLocW.word header))
        (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf)))))
      (Misc.wordList free xs) _ at cell
    have reorder : SetSep.star (SetSep.star (SetSep.star left right)
        (SetSep.star (SetSep.one (addr, WordLocW.word header))
          (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf)))))
        (Misc.wordList free xs) =
      SetSep.star (SetSep.one (addr, WordLocW.word header))
        (SetSep.star (SetSep.star (Misc.wordList free xs)
          (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf))))
          (SetSep.star left right)) := by ac_rfl
    rw [reorder] at cell
    exact cell
  have read : memory addr = .word header ∧ domain addr = true := by
    rcases reassembled with ⟨one, rest, partition, singleton, _⟩
    have member : SetSep.fun2Set (memory, fun address => domain address = true) (addr, .word header) := by
      rw [← partition.1]
      exact Or.inl (by rw [singleton])
    exact (SetSep.fun2SetThm memory _ _ _).mp member
  refine ⟨header, encoded, wordLen, bound, decoded, read.1, read.2, ?_⟩
  have reorder : SetSep.star (SetSep.one (addr, WordLocW.word header))
      (SetSep.star (SetSep.star (Misc.wordList free xs)
        (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf)))) (SetSep.star left right)) =
    SetSep.star (SetSep.star (Misc.wordList free xs)
      (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf))))
      (SetSep.star (SetSep.one (addr, WordLocW.word header)) (SetSep.star left right)) := by ac_rfl
  rw [← reorder]
  exact reassembled

/-- The first pending reference is a concrete mutable header whose payload
length and address come from the abstract scan state. This is local
infrastructure for the nonempty scan case. -/
theorem refScan_headRead {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width)))
    (state : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width))
    (tail : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr p : BitVec width) (xs : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (pending : state.r2 = .dataElement roots len (tag, payload) :: tail)
    (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (refs : (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement genConf.isRef) = true)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (wordHeapParts conf p state xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true))) :
    ∃ header : BitVec width,
      wordPayload roots len tag payload conf = (header, roots.map (wordAddr conf), true) ∧
      roots.length = len ∧ roots.length < 2 ^ (width - 4) ∧
      decodeLength conf header = BitVec.ofNat width roots.length ∧
      memory (p + wordSemBytesInWord * BitVec.ofNat width
        (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + xs.length)) = .word header ∧
      domain (p + wordSemBytesInWord * BitVec.ofNat width
        (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + xs.length)) = true ∧
      let addr := p + wordSemBytesInWord * BitVec.ofNat width
        (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + xs.length)
      let base := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + xs.length)
      let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
      SetSep.star (SetSep.star (SetSep.star (wordHeap curr state.heap conf) (Misc.wordList free xs))
        (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf))))
        (SetSep.star (SetSep.one (addr, .word header))
          (SetSep.star (SetSep.star (SetSep.star (wordHeap p (state.h1 ++ state.h2) conf) frame)
            (wordHeap base (state.r4 ++ state.r3) conf))
            (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) (tail ++ state.r1) conf)))
        (SetSep.fun2Set (memory, fun address => domain address = true)) := by
  have refTrue : genConf.isRef (tag, payload) = true := by
    have h := (List.all_eq_true.mp refs) (.dataElement roots len (tag, payload)) (by simp [pending])
    simpa [isRefElement] using h
  have mutable := (refClass tag payload).mp refTrue
  let base := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + xs.length)
  let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
  let before := state.r4 ++ state.r3
  let after := tail ++ state.r1
  let rest := SetSep.star (wordHeap curr state.heap conf)
    (SetSep.star (wordHeap p (state.h1 ++ state.h2) conf) frame)
  have arrangement : SetSep.star
      (SetSep.star (wordHeap base (before ++ .dataElement roots len (tag, payload) :: after) conf)
        (Misc.wordList free xs)) rest (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    simp only [wordHeapParts] at separated
    have refHeap : state.r4 ++ state.r3 ++ state.r2 ++ state.r1 =
        before ++ .dataElement roots len (tag, payload) :: after := by
      simp [before, after, pending, List.append_assoc]
    rw [refHeap] at separated
    change SetSep.star (SetSep.star (wordHeap curr state.heap conf)
      (SetSep.star (SetSep.star (wordHeap p (state.h1 ++ state.h2) conf) (Misc.wordList free xs))
        (wordHeap base (before ++ .dataElement roots len (tag, payload) :: after) conf))) frame _ at separated
    have reorder : SetSep.star (SetSep.star (wordHeap curr state.heap conf)
        (SetSep.star (SetSep.star (wordHeap p (state.h1 ++ state.h2) conf) (Misc.wordList free xs))
          (wordHeap base (before ++ .dataElement roots len (tag, payload) :: after) conf))) frame =
      SetSep.star (SetSep.star (wordHeap base (before ++ .dataElement roots len (tag, payload) :: after) conf)
        (Misc.wordList free xs)) rest := by dsimp [rest]; ac_rfl
    rwa [reorder] at separated
  obtain ⟨header, encoded, rootLen, bound, decoded, read, present, cell⟩ :=
    refScan_dataCell conf before after roots len tag payload base free xs memory domain rest mutable arrangement
  have address : base + wordSemBytesInWord * BitVec.ofNat width (heapLength before) =
      p + wordSemBytesInWord * BitVec.ofNat width
        (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + xs.length) := by
    simp only [base, before, heapLength_append, BitVec.ofNat_add, BitVec.mul_add]
    ac_rfl
  refine ⟨header, encoded, rootLen, bound, decoded, by simpa [address] using read,
    by simpa [address] using present, ?_⟩
  let addr := base + wordSemBytesInWord * BitVec.ofNat width (heapLength before)
  have rearranged : SetSep.star (SetSep.star (SetSep.star (wordHeap curr state.heap conf)
      (Misc.wordList free xs)) (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf))))
      (SetSep.star (SetSep.one (addr, .word header))
        (SetSep.star (SetSep.star (SetSep.star (wordHeap p (state.h1 ++ state.h2) conf) frame)
          (wordHeap base before conf))
          (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) after conf)))
      (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    change SetSep.star (SetSep.star (Misc.wordList free xs)
      (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf))))
      (SetSep.star (SetSep.one (addr, .word header))
        (SetSep.star (SetSep.star rest (wordHeap base before conf))
          (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) after conf))) _ at cell
    have reorder : SetSep.star (SetSep.star (Misc.wordList free xs)
        (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf))))
        (SetSep.star (SetSep.one (addr, .word header))
          (SetSep.star (SetSep.star rest (wordHeap base before conf))
            (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) after conf))) =
      SetSep.star (SetSep.star (SetSep.star (wordHeap curr state.heap conf)
        (Misc.wordList free xs)) (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf))))
        (SetSep.star (SetSep.one (addr, .word header))
          (SetSep.star (SetSep.star (SetSep.star (wordHeap p (state.h1 ++ state.h2) conf) frame)
            (wordHeap base before conf))
            (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) after conf))) := by
      dsimp [rest]
      ac_rfl
    rwa [reorder] at cell
  simpa only [addr, address, base, free, before, after] using rearranged

/-- A nonempty reference segment begins strictly before the end of the
original heap. This arithmetic fact factors the nonempty scan case. -/
theorem refScan_prefix_lt_heap {α β : Type} (state : GcState α β)
    (head : HeapElement α β) (tail : List (HeapElement α β))
    (pending : state.r2 = head :: tail) (invariant : genLenInv state) :
    heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + state.n < heapLength state.heap := by
  have positive : 0 < elLength head := by cases head <;> simp [elLength]
  simp [genLenInv, heapLength, List.map_append, List.sum_append, pending] at invariant ⊢
  omega

/-- The word-level scan's current and end addresses differ whenever the
abstract reference segment is nonempty and the original heap fits in memory. -/
theorem refScan_addresses_ne {width : Nat} [NeZero width]
    (state : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (head : HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))
    (tail : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (p : BitVec width) (freeCount : Nat) (pending : state.r2 = head :: tail)
    (invariant : genLenInv state) (bytesBound : heapLength state.heap * (width / 8) < 2 ^ width)
    (good : goodDimindex width) :
    p + wordSemBytesInWord * BitVec.ofNat width
        (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + freeCount) ≠
      p + wordSemBytesInWord * BitVec.ofNat width
        (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3 ++ state.r2) + freeCount) := by
  have positive : 0 < heapLength state.r2 := by
    rw [pending]
    have pos : 0 < elLength head := by cases head <;> simp [elLength]
    simp only [heapLength, List.map_cons, List.sum_cons]
    omega
  have leHeap : heapLength state.r2 ≤ heapLength state.heap := by
    simp [genLenInv, heapLength, List.map_append, List.sum_append] at invariant ⊢
    omega
  have stepBound : heapLength state.r2 * (width / 8) < 2 ^ width :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ leHeap) bytesBound
  have bytesPositive : 0 < width / 8 := by rcases good with rfl | rfl <;> decide
  have stepBound' : (width / 8) * heapLength state.r2 < 2 ^ width := by
    simpa only [Nat.mul_comm] using stepBound
  have nonzero : wordSemBytesInWord * BitVec.ofNat width (heapLength state.r2) ≠ 0 := by
    intro eq
    have natEq := congrArg BitVec.toNat eq
    simp [wordSemBytesInWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt stepBound'] at natEq
    rcases natEq with tooSmall | empty
    · omega
    · omega
  intro equal
  apply nonzero
  apply add_left_cancel (a := p + wordSemBytesInWord * BitVec.ofNat width
    (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + freeCount))
  calc
    _ = p + wordSemBytesInWord * BitVec.ofNat width
        (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3 ++ state.r2) + freeCount) := by
      simp only [heapLength_append, BitVec.ofNat_add, BitVec.mul_add]
      ac_rfl
    _ = _ := by rw [← equal]; simp

/-- A nonempty reference scan reads its represented header and executes the
source word-list step before recursively scanning the tail. This local
transition lemma has no separate HOL original. -/
theorem refScan_wordStep {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width))) (k : Nat)
    (state : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width))
    (tail : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr p i pa ib pb : BitVec width) (xs : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (pending : state.r2 = .dataElement roots len (tag, payload) :: tail)
    (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (refs : (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement genConf.isRef) = true)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (wordHeapParts conf p state xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (countBound : state.r2.length ≤ k) (invariant : genLenInv state)
    (bytesBound : heapLength state.heap * (width / 8) < 2 ^ width) (good : goodDimindex width) :
    let addr := p + wordSemBytesInWord * BitVec.ofNat width
      (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + xs.length)
    let last := p + wordSemBytesInWord * BitVec.ofNat width
      (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3 ++ state.r2) + xs.length)
    wordGenGcMoveRefs conf k (addr, last, i, pa, ib, pb, curr, memory, domain) =
      (let (next, i1, pa1, ib1, pb1, memory1, c1) := wordGenGcMoveList conf
        (addr + wordSemBytesInWord, BitVec.ofNat width roots.length, i, pa, ib, pb, curr, memory, domain)
       let (final, i2, pa2, ib2, pb2, memory2, c2) := wordGenGcMoveRefs conf (k - 1)
        (next, last, i1, pa1, ib1, pb1, curr, memory1, domain)
       (final, i2, pa2, ib2, pb2, memory2, c1 && c2)) := by
  obtain ⟨header, _, _, _, decoded, read, present, _⟩ :=
    refScan_headRead conf genConf state roots len tag payload tail curr p xs memory domain frame
      pending refClass refs separated
  have notLast := refScan_addresses_ne state _ tail p xs.length pending invariant bytesBound good
  have nonzero : k ≠ 0 := by simp [pending] at countBound; omega
  dsimp only
  rw [wordGenGcMoveRefs, ite_eq_right notLast, ite_eq_right nonzero]
  simp only [read, present, wordSemIsWordLoc, wordSemTheWord, Bool.true_and, decoded]

/-- Run the established major-collector root-list simulation on the first
reference payload while retaining all surrounding scan regions in the frame.
This is local factoring of the nonempty reference-scan proof. -/
theorem refScan_moveRoots {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width)))
    (state middle : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots moved : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width))
    (tail : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr p k1 i1 pa1 ib1 pb1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (c1 : Bool)
    (pending : state.r2 = .dataElement roots len (tag, payload) :: tail)
    (abstractRun : GenGc.gcMoveList genConf state roots = (moved, middle)) (middleOk : middle.ok = true)
    (heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t) (lenBound : conf.lenSize + 5 ≤ width)
    (refs : (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement genConf.isRef) = true)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (wordHeapParts conf p state xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (length : xs.length = state.n) (good : goodDimindex width)
    (wordRun : wordGenGcMoveList conf
      (p + wordSemBytesInWord * BitVec.ofNat width
          (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + xs.length) + wordSemBytesInWord,
       BitVec.ofNat width roots.length, BitVec.ofNat width state.a,
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)),
       BitVec.ofNat width (state.a + state.n),
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + state.n),
       curr, memory, domain) = (k1, i1, pa1, ib1, pb1, memory1, c1)) :
    ∃ (header : BitVec width)
      (left right : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
      (xs1 : List (WordLocW width)),
      wordPayload roots len tag payload conf = (header, roots.map (wordAddr conf), true) ∧
      roots.length = len ∧ middle.h2 = state.h2 ++ left ∧ middle.r4 = right ++ state.r4 ∧
      (let addr := p + wordSemBytesInWord * BitVec.ofNat width
          (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + xs.length)
       let base := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + xs.length)
       let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
       let rootFrame := SetSep.star (SetSep.one (addr, .word header))
         (SetSep.star (SetSep.star (SetSep.star (wordHeap p (state.h1 ++ state.h2) conf) frame)
           (wordHeap base (state.r4 ++ state.r3) conf))
           (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) (tail ++ state.r1) conf))
       SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr middle.heap conf)
         (wordHeap free left conf)) (wordHeap pb1 right conf)) (Misc.wordList pa1 xs1))
         (Misc.wordList (addr + wordSemBytesInWord) (moved.map (wordAddr conf)))) rootFrame
         (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
       heapLength middle.heap = heapLength state.heap ∧ c1 = true ∧ i1 = BitVec.ofNat width middle.a ∧
       ib1 = BitVec.ofNat width (middle.a + middle.n) ∧ middle.n = xs1.length ∧
       state.n = heapLength left + middle.n + heapLength right ∧
       k1 = (addr + wordSemBytesInWord) + BitVec.ofNat width roots.length * wordSemBytesInWord ∧
       pa1 = free + wordSemBytesInWord * BitVec.ofNat width (heapLength left) ∧
       pb1 = pa1 + wordSemBytesInWord * BitVec.ofNat width middle.n ∧
       (right ++ middle.r3 ++ middle.r2 ++ middle.r1).all (isRefElement genConf.isRef) = true) := by
  obtain ⟨header, encoded, rootsLen, rootsBound, _, _, _, lists⟩ :=
    refScan_headRead conf genConf state roots len tag payload tail curr p xs memory domain frame
      pending refClass refs separated
  obtain ⟨left, right, leftEq, rightEq, clearRun⟩ :=
    gcMoveList_withNilLemma genConf roots moved state middle abstractRun middleOk
  have clearRefs : (({ state with h2 := [], r4 := [] }).r4 ++
      ({ state with h2 := [], r4 := [] }).r3 ++ ({ state with h2 := [], r4 := [] }).r2 ++
      ({ state with h2 := [], r4 := [] }).r1).all (isRefElement genConf.isRef) = true := by
    simp only at refs ⊢
    simp only [List.nil_append, List.all_append, Bool.and_eq_true] at refs ⊢
    exact ⟨⟨refs.1.1.2, refs.1.2⟩, refs.2⟩
  have rootBound : roots.length < 2 ^ width := by
    have widthPos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
    have exponent : width - 4 < width := by omega
    have boundPow : 2 ^ (width - 4) < 2 ^ width := Nat.pow_lt_pow_right (by decide : 1 < 2) exponent
    omega
  let addr := p + wordSemBytesInWord * BitVec.ofNat width
    (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + xs.length)
  let base := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + xs.length)
  let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
  let rootFrame := SetSep.star (SetSep.one (addr, WordLocW.word header))
    (SetSep.star (SetSep.star (SetSep.star (wordHeap p (state.h1 ++ state.h2) conf) frame)
      (wordHeap base (state.r4 ++ state.r3) conf))
      (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) (tail ++ state.r1) conf))
  have freeEnd : free + wordSemBytesInWord * BitVec.ofNat width state.n =
      p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + state.n) := by
    simp only [free, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
  have wordRun' : wordGenGcMoveList conf
      (addr + wordSemBytesInWord, BitVec.ofNat width roots.length, BitVec.ofNat width state.a, free,
       BitVec.ofNat width (state.a + state.n), free + wordSemBytesInWord * BitVec.ofNat width state.n,
       curr, memory, domain) = (k1, i1, pa1, ib1, pb1, memory1, c1) := by
    rw [freeEnd]
    exact wordRun
  obtain ⟨xs1, memoryResult, heapLen, success, indexEq, limitEq, xsLen, accounting, lastEq, paEq, pbEq, refsOut⟩ :=
    wordGenGcMoveList_thm conf genConf roots { state with h2 := [], r4 := [] }
      { middle with h2 := left, r4 := right } moved curr free (addr + wordSemBytesInWord) k1 i1 pa1 ib1 pb1
      xs memory memory1 domain rootFrame c1 clearRun middleOk rfl rfl heapBound refClass lenBound lists wordRun'
      clearRefs length good rootBound
  exact ⟨header, left, right, xs1, encoded, rootsLen, leftEq, rightEq,
    memoryResult, heapLen, success, indexEq, limitEq, xsLen, accounting, lastEq, paEq, pbEq, refsOut⟩

/-- The post-root-move state restores the reference-scan length and
classification invariants for the recursive call. This is local factoring of
the source proof's nonempty reference case. -/
theorem refScan_advanceInvariant {α β : Type} (conf : GenGc.Config β)
    (state middle : GcState α β) (roots moved : List (HeapAddress α))
    (len : Nat) (payload : β) (tail right : List (HeapElement α β))
    (pending : state.r2 = .dataElement roots len payload :: tail)
    (abstractRun : GenGc.gcMoveList conf state roots = (moved, middle)) (middleOk : middle.ok = true)
    (rightEq : middle.r4 = right ++ state.r4) (invariant : genLenInv state)
    (refs : (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement conf.isRef) = true)
    (newRefs : (right ++ middle.r3 ++ middle.r2 ++ middle.r1).all (isRefElement conf.isRef) = true) :
    let next := { middle with r2 := tail, r3 := middle.r3 ++ [HeapElement.dataElement moved len payload] }
    genLenInv next ∧ next.h1 = state.h1 ∧ next.r2 = tail ∧
      (next.r4 ++ next.r3 ++ next.r2 ++ next.r1).all (isRefElement conf.isRef) = true := by
  obtain ⟨h1Eq, r1Eq, r2Eq, r3Eq⟩ := genMoveList_const conf roots moved state middle abstractRun
  have midInv := genMoveList_lenInv conf roots moved state middle abstractRun middleOk invariant
  have headRef : conf.isRef payload = true := by
    have h := (List.all_eq_true.mp refs) (.dataElement roots len payload) (by simp [pending])
    simpa [isRefElement] using h
  have oldRefs : state.r4.all (isRefElement conf.isRef) = true := by
    apply List.all_eq_true.mpr
    intro element member
    exact (List.all_eq_true.mp refs) element (by simp [member])
  constructor
  · simp only [genLenInv] at midInv ⊢
    simp [heapLength, List.map_append, List.sum_append, elLength, r2Eq, pending] at midInv ⊢
    omega
  constructor
  · exact h1Eq
  constructor
  · rfl
  · simp only [rightEq, List.all_append, List.all_cons, isRefElement, Bool.and_eq_true] at newRefs oldRefs ⊢
    simp only [r2Eq, pending, List.all_cons, isRefElement, Bool.and_eq_true] at newRefs
    aesop

/-- After moving a reference's roots, the same header and the rewritten root
words reconstruct its exact heap-element assertion. This is local factoring
of the nonempty reference-scan proof. -/
theorem refScan_movedElement {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width)))
    (state middle : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots moved : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width)) (header addr : BitVec width)
    (abstractRun : GenGc.gcMoveList genConf state roots = (moved, middle))
    (encoded : wordPayload roots len tag payload conf = (header, roots.map (wordAddr conf), true))
    (rootsLen : roots.length = len) (bound : roots.length < 2 ^ (width - 4))
    (decoded : decodeLength conf header = BitVec.ofNat width roots.length) :
    wordEl addr (.dataElement moved len (tag, payload)) conf =
      SetSep.star (SetSep.one (addr, WordLocW.word header))
        (Misc.wordList (addr + wordSemBytesInWord) (moved.map (wordAddr conf))) := by
  have movedLen := GenGc.gcMoveList_length genConf roots moved state middle abstractRun
  have encodedMoved : wordPayload moved len tag payload conf = (header, moved.map (wordAddr conf), true) := by
    have original : wordPayload roots roots.length tag payload conf =
        (header, roots.map (wordAddr conf), true) := by simpa only [rootsLen] using encoded
    simpa only [rootsLen] using wordPayload_swap roots moved tag payload conf header original movedLen
  funext cells
  apply propext
  simp only [wordEl, encodedMoved, StackRemove.WordListExists.starCond, Misc.wordList,
    List.length_map, movedLen, bound, decoded, and_self, and_true]
  rfl

/-- Address equations aligning the newly copied regions with the remaining
reference heap after one root-list move. This is local arithmetic factoring
for the recursive reference-scan assertion. -/
theorem refScan_regionAddresses {width : Nat} [NeZero width] {α β : Type}
    (state middle : GcState α β) (left right : List (HeapElement α β))
    (p pa1 pb1 : BitVec width) (xsLength : Nat)
    (freeEq : pa1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)) +
      wordSemBytesInWord * BitVec.ofNat width (heapLength left))
    (refsEq : pb1 = pa1 + wordSemBytesInWord * BitVec.ofNat width middle.n)
    (accounting : state.n = heapLength left + middle.n + heapLength right)
    (length : xsLength = state.n) :
    pa1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2 ++ left)) ∧
    pb1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2 ++ left) + middle.n) ∧
    pb1 + wordSemBytesInWord * BitVec.ofNat width (heapLength right) =
      p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + xsLength) := by
  constructor
  · rw [freeEq]
    simp only [heapLength_append, BitVec.ofNat_add, BitVec.mul_add]
    ac_rfl
  constructor
  · rw [refsEq, freeEq]
    simp only [heapLength_append, BitVec.ofNat_add, BitVec.mul_add]
    ac_rfl
  · rw [refsEq, freeEq, length, accounting]
    simp only [BitVec.ofNat_add, BitVec.mul_add]
    ac_rfl

/-- Reassemble the exact separated regions after moving one reference's
roots into the next scan heap. This separation identity is local to the
nonempty scan proof and has no separate HOL original. -/
theorem refScan_reassembleRegions {width : Nat} [NeZero width] (conf : Config)
    (heap scanned left right before after : List
      (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (moved : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width)) (header : BitVec width)
    (curr p free pa1 pb1 base addr : BitVec width) (xs1 : List (WordLocW width))
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (freeEq : free = p + wordSemBytesInWord * BitVec.ofNat width (heapLength scanned))
    (baseEq : base = pb1 + wordSemBytesInWord * BitVec.ofNat width (heapLength right))
    (addrEq : addr = base + wordSemBytesInWord * BitVec.ofNat width (heapLength before))
    (elementEq : wordEl addr (.dataElement moved len (tag, payload)) conf =
      SetSep.star (SetSep.one (addr, .word header))
        (Misc.wordList (addr + wordSemBytesInWord) (moved.map (wordAddr conf)))) :
    SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap conf)
      (wordHeap free left conf)) (wordHeap pb1 right conf)) (Misc.wordList pa1 xs1))
      (Misc.wordList (addr + wordSemBytesInWord) (moved.map (wordAddr conf))))
      (SetSep.star (SetSep.one (addr, .word header))
        (SetSep.star (SetSep.star (SetSep.star (wordHeap p scanned conf) frame)
          (wordHeap base before conf))
          (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) after conf))) =
    SetSep.star (SetSep.star (wordHeap curr heap conf)
      (SetSep.star (SetSep.star (wordHeap p (scanned ++ left) conf) (Misc.wordList pa1 xs1))
        (wordHeap pb1 (right ++ (before ++ .dataElement moved len (tag, payload) :: after)) conf))) frame := by
  change free = p + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength scanned) at freeEq
  change base = pb1 + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength right) at baseEq
  change addr = base + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength before) at addrEq
  rw [wordHeapAppend scanned left p conf,
    wordHeapAppend right (before ++ .dataElement moved len (tag, payload) :: after) pb1 conf]
  rw [← freeEq, ← baseEq, wordHeapAppend before (.dataElement moved len (tag, payload) :: after) base conf]
  rw [← addrEq]
  simp only [wordHeap, elLength, elementEq]
  simp only [wordSemBytesInWord, StackRemove.bytesInWord]
  ac_rfl

/-- Reconstruct the original separated heap assertion for the recursive
reference scan after the root-list move. This is local factoring of the
source proof's nonempty reference case. -/
theorem refScan_nextMemory {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width)))
    (state middle : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots moved : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width))
    (tail left right : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (header curr p pa1 pb1 : BitVec width) (xs xs1 : List (WordLocW width))
    (memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (abstractRun : GenGc.gcMoveList genConf state roots = (moved, middle))
    (encoded : wordPayload roots len tag payload conf = (header, roots.map (wordAddr conf), true))
    (rootsLen : roots.length = len) (bound : roots.length < 2 ^ (width - 4))
    (decoded : decodeLength conf header = BitVec.ofNat width roots.length)
    (leftEq : middle.h2 = state.h2 ++ left) (rightEq : middle.r4 = right ++ state.r4)
    (freeEq : pa1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)) +
      wordSemBytesInWord * BitVec.ofNat width (heapLength left))
    (refsEq : pb1 = pa1 + wordSemBytesInWord * BitVec.ofNat width middle.n)
    (accounting : state.n = heapLength left + middle.n + heapLength right)
    (length : xs.length = state.n) (length1 : middle.n = xs1.length)
    (separated :
      let addr := p + wordSemBytesInWord * BitVec.ofNat width
        (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + xs.length)
      let base := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + xs.length)
      let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
      SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr middle.heap conf)
        (wordHeap free left conf)) (wordHeap pb1 right conf)) (Misc.wordList pa1 xs1))
        (Misc.wordList (addr + wordSemBytesInWord) (moved.map (wordAddr conf))))
        (SetSep.star (SetSep.one (addr, .word header))
          (SetSep.star (SetSep.star (SetSep.star (wordHeap p (state.h1 ++ state.h2) conf) frame)
            (wordHeap base (state.r4 ++ state.r3) conf))
            (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) (tail ++ state.r1) conf)))
        (SetSep.fun2Set (memory1, fun address => domain address = true))) :
    let next := { middle with r2 := tail, r3 := middle.r3 ++ [.dataElement moved len (tag, payload)] }
    SetSep.star (SetSep.star (wordHeap curr next.heap conf) (wordHeapParts conf p next xs1)) frame
      (SetSep.fun2Set (memory1, fun address => domain address = true)) := by
  obtain ⟨h1Eq, r1Eq, _, r3Eq⟩ := genMoveList_const genConf roots moved state middle abstractRun
  obtain ⟨paEq, pbEq, baseEq⟩ := refScan_regionAddresses state middle left right p pa1 pb1 xs.length
    freeEq refsEq accounting length
  let addr := p + wordSemBytesInWord * BitVec.ofNat width
    (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + xs.length)
  let base := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + xs.length)
  let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
  have addrEq : addr = base + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.r4 ++ state.r3)) := by
    simp only [addr, base, heapLength_append, BitVec.ofNat_add, BitVec.mul_add]
    ac_rfl
  have elementEq := refScan_movedElement conf genConf state middle roots moved len tag payload header addr
    abstractRun encoded rootsLen bound decoded
  have assembly := refScan_reassembleRegions conf middle.heap (state.h1 ++ state.h2) left right
    (state.r4 ++ state.r3) (tail ++ state.r1) moved len tag payload header curr p free pa1 pb1 base addr xs1 frame
    rfl baseEq.symm addrEq elementEq
  have reconstructed := (congrFun assembly (SetSep.fun2Set (memory1, fun address => domain address = true))).mp separated
  simp only [wordHeapParts]
  simp only [h1Eq, leftEq, rightEq, r3Eq, r1Eq, ← length1]
  simp only [List.append_assoc] at paEq pbEq
  rw [← paEq, ← pbEq]
  simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using reconstructed

/-- The updated scan cursor and original end pointer are exactly the cursor
and end computed from the recursive abstract state. This is local arithmetic
factoring for the nonempty reference-scan proof. -/
theorem refScan_nextPointers {width : Nat} [NeZero width] {α β : Type}
    (state middle : GcState α β) (roots moved : List (HeapAddress α)) (len : Nat) (payload : β)
    (tail left right : List (HeapElement α β)) (p k1 : BitVec width) (xsLength xs1Length : Nat)
    (pending : state.r2 = .dataElement roots len payload :: tail)
    (h1Eq : middle.h1 = state.h1) (h2Eq : middle.h2 = state.h2 ++ left)
    (r4Eq : middle.r4 = right ++ state.r4) (r3Eq : middle.r3 = state.r3)
    (rootsLen : roots.length = len) (accounting : state.n = heapLength left + middle.n + heapLength right)
    (length : xsLength = state.n) (length1 : middle.n = xs1Length)
    (cursor : k1 = (p + wordSemBytesInWord * BitVec.ofNat width
      (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + xsLength) + wordSemBytesInWord) +
      BitVec.ofNat width roots.length * wordSemBytesInWord) :
    let next := { middle with r2 := tail, r3 := middle.r3 ++ [HeapElement.dataElement moved len payload] }
    k1 = p + wordSemBytesInWord * BitVec.ofNat width
      (heapLength (next.h1 ++ next.h2 ++ next.r4 ++ next.r3) + xs1Length) ∧
    p + wordSemBytesInWord * BitVec.ofNat width
      (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3 ++ state.r2) + xsLength) =
      p + wordSemBytesInWord * BitVec.ofNat width
        (heapLength (next.h1 ++ next.h2 ++ next.r4 ++ next.r3 ++ next.r2) + xs1Length) := by
  have cursorCount :
      heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + xsLength + (roots.length + 1) =
        heapLength (middle.h1 ++ middle.h2 ++ middle.r4 ++ (middle.r3 ++ [.dataElement moved len payload])) +
          xs1Length := by
    simp [heapLength, List.map_append, List.sum_append, elLength, h1Eq, h2Eq, r4Eq, r3Eq] at *
    omega
  have endCount :
      heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3 ++ state.r2) + xsLength =
        heapLength (middle.h1 ++ middle.h2 ++ middle.r4 ++
          (middle.r3 ++ [.dataElement moved len payload]) ++ tail) + xs1Length := by
    simp [heapLength, List.map_append, List.sum_append, elLength, h1Eq, h2Eq, r4Eq, r3Eq, pending] at *
    omega
  constructor
  · rw [cursor]
    calc
      _ = p + wordSemBytesInWord * BitVec.ofNat width
          (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + xsLength + (roots.length + 1)) := by
        simp only [BitVec.ofNat_add, BitVec.mul_add]
        ac_rfl
      _ = _ := by rw [cursorCount]
  · rw [endCount]

/-- Unfold the successful abstract nonempty scan into its root move and
recursive call, carrying the original fuel bound to the tail. This local
factoring has no separate HOL original. -/
theorem refScan_abstractStep {α β : Type} (conf : GenGc.Config β) (k : Nat)
    (state middle final : GcState α β) (roots moved : List (HeapAddress α))
    (len : Nat) (payload : β) (tail : List (HeapElement α β))
    (pending : state.r2 = .dataElement roots len payload :: tail)
    (move : GenGc.gcMoveList conf state roots = (moved, middle))
    (run : GenGc.gcMoveRefs conf state = final) (success : final.ok = true)
    (fuel : state.r2.length ≤ k) :
    let next := { middle with r2 := tail, r3 := middle.r3 ++ [HeapElement.dataElement moved len payload] }
    GenGc.gcMoveRefs conf next = final ∧ middle.ok = true ∧ tail.length ≤ k - 1 := by
  have recursive : GenGc.gcMoveRefs conf
      { middle with r2 := tail, r3 := middle.r3 ++ [HeapElement.dataElement moved len payload] } = final := by
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n ok heap heap0 =>
      simp only at pending
      subst r2
      rw [GenGc.gcMoveRefs] at run
      simpa only [move] using run
  have nextOk : (GenGc.gcMoveRefs conf
      { middle with r2 := tail, r3 := middle.r3 ++ [HeapElement.dataElement moved len payload] }).ok = true := by
    rw [recursive]
    exact success
  have middleOk := GenGc.gcMoveRefs_ok conf
    { middle with r2 := tail, r3 := middle.r3 ++ [HeapElement.dataElement moved len payload] } nextOk
  refine ⟨recursive, middleOk, ?_⟩
  simp [pending] at fuel
  omega

/-- Empty-reference case of the original reference-scan simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_move_refs_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMoveRefs_empty {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width))) (k : Nat)
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (curr p : BitVec width) (xs : List (WordLocW width))
    (pb1 pa1 ib1 i1 p1 : BitVec width)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (c1 : Bool)
    (abstractRun : GenGc.gcMoveRefs genConf state = state1) (stateOk : state1.ok = true)
    (heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (heapBytesBound : heapLength state.heap * (width / 8) < 2 ^ width)
    (_refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (_lenBound : conf.lenSize + 5 ≤ width)
    (wordRun : wordGenGcMoveRefs conf k
      (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + xs.length),
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3 ++ state.r2) + xs.length),
       BitVec.ofNat width state.a,
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)),
       BitVec.ofNat width (state.a + state.n),
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + state.n),
       curr, memory, domain) = (p1, i1, pa1, ib1, pb1, memory1, c1))
    (countBound : state.r2.length ≤ k) (invariant : genLenInv state)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (wordHeapParts conf p state xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (refs : (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement genConf.isRef) = true)
    (length : xs.length = state.n) (_good : goodDimindex width) (empty : state.r2 = []) :
    ∃ xs1,
      SetSep.star (SetSep.star (wordHeap curr state1.heap conf) (wordHeapParts conf p state1 xs1)) frame
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      state1.r3 = [] ∧ state1.r2 = [] ∧ heapLength state1.heap = heapLength state.heap ∧
      c1 = true ∧ i1 = BitVec.ofNat width state1.a ∧ ib1 = BitVec.ofNat width (state1.a + state1.n) ∧
      state1.n = xs1.length ∧
      heapLength state.h2 + state.n + heapLength state.r4 =
        heapLength state1.h2 + state1.n + heapLength state1.r4 ∧
      pa1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state1.h1 ++ state1.h2)) ∧
      pb1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state1.h1 ++ state1.h2) + state1.n) ∧
      p1 = p + wordSemBytesInWord * BitVec.ofNat width
        (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3 ++ state.r2) + xs.length) ∧
      genLenInv state1 ∧
      (state1.r4 ++ state1.r3 ++ state1.r2 ++ state1.r1).all (isRefElement genConf.isRef) = true := by
  have abstractEq : GenGc.gcMoveRefs genConf state = { state with r3 := [], r1 := state.r3 ++ state.r1 } := by
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n ok heap heap0 =>
      simp only at empty
      subst r2
      rw [GenGc.gcMoveRefs]
  rw [abstractEq] at abstractRun
  subst state1
  simp only [empty, List.append_nil] at wordRun
  rw [wordGenGcMoveRefs] at wordRun
  simp only [↓reduceIte, Prod.mk.injEq] at wordRun
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := wordRun
  refine ⟨xs, ?_, rfl, empty, rfl, rfl, rfl, rfl, length.symm, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa [wordHeapParts, empty, List.append_assoc] using separated
  · simp [empty]
  · simpa [genLenInv, empty, List.append_assoc] using invariant
  · simpa [empty, List.append_assoc] using refs

/-- Original major collector reference-scan simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_move_refs_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMoveRefs_thm {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width))) (k : Nat)
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (curr p : BitVec width) (xs : List (WordLocW width))
    (pb1 pa1 ib1 i1 p1 : BitVec width)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (c1 : Bool)
    (abstractRun : GenGc.gcMoveRefs genConf state = state1) (stateOk : state1.ok = true)
    (heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (heapBytesBound : heapLength state.heap * (width / 8) < 2 ^ width)
    (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (lenBound : conf.lenSize + 5 ≤ width)
    (wordRun : wordGenGcMoveRefs conf k
      (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + xs.length),
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3 ++ state.r2) + xs.length),
       BitVec.ofNat width state.a,
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)),
       BitVec.ofNat width (state.a + state.n),
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + state.n),
       curr, memory, domain) = (p1, i1, pa1, ib1, pb1, memory1, c1))
    (countBound : state.r2.length ≤ k) (invariant : genLenInv state)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (wordHeapParts conf p state xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (refs : (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement genConf.isRef) = true)
    (length : xs.length = state.n) (good : goodDimindex width) :
    ∃ xs1,
      SetSep.star (SetSep.star (wordHeap curr state1.heap conf) (wordHeapParts conf p state1 xs1)) frame
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      state1.r3 = [] ∧ state1.r2 = [] ∧ heapLength state1.heap = heapLength state.heap ∧
      c1 = true ∧ i1 = BitVec.ofNat width state1.a ∧ ib1 = BitVec.ofNat width (state1.a + state1.n) ∧
      state1.n = xs1.length ∧
      heapLength state.h2 + state.n + heapLength state.r4 =
        heapLength state1.h2 + state1.n + heapLength state1.r4 ∧
      pa1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state1.h1 ++ state1.h2)) ∧
      pb1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state1.h1 ++ state1.h2) + state1.n) ∧
      p1 = p + wordSemBytesInWord * BitVec.ofNat width
        (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3 ++ state.r2) + xs.length) ∧
      genLenInv state1 ∧
      (state1.r4 ++ state1.r3 ++ state1.r2 ++ state1.r1).all (isRefElement genConf.isRef) = true := by
  induction k using Nat.strong_induction_on generalizing state state1 memory memory1 xs pb1 pa1 ib1 i1 p1 c1 with
  | h k ih =>
    cases pending : state.r2 with
    | nil =>
      simpa only [pending] using wordGenGcMoveRefs_empty conf genConf k state state1 memory memory1 domain curr p xs
        pb1 pa1 ib1 i1 p1 frame c1 abstractRun stateOk heapBound heapBytesBound refClass lenBound
        wordRun countBound invariant separated refs length good pending
    | cons head tail =>
      have headRef := (List.all_eq_true.mp refs) head (by simp [pending])
      cases head with
      | unused len => simp [isRefElement] at headRef
      | forwardPointer addr value len => simp [isRefElement] at headRef
      | dataElement roots len data =>
        rcases data with ⟨tag, payload⟩
        generalize move : GenGc.gcMoveList genConf state roots = moveResult
        rcases moveResult with ⟨moved, middle⟩
        obtain ⟨recursive, middleOk, tailBound⟩ :=
          refScan_abstractStep genConf k state middle state1 roots moved len (tag, payload) tail
            pending move abstractRun stateOk countBound
        have step := refScan_wordStep conf genConf k state roots len tag payload tail curr p
          (BitVec.ofNat width state.a)
          (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)))
          (BitVec.ofNat width (state.a + state.n))
          (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + state.n))
          xs memory domain frame pending refClass refs separated countBound invariant heapBytesBound good
        rw [step] at wordRun
        let addr := p + wordSemBytesInWord * BitVec.ofNat width
          (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3) + xs.length)
        let last := p + wordSemBytesInWord * BitVec.ofNat width
          (heapLength (state.h1 ++ state.h2 ++ state.r4 ++ state.r3 ++ state.r2) + xs.length)
        generalize wordMove : wordGenGcMoveList conf
          (addr + wordSemBytesInWord, BitVec.ofNat width roots.length, BitVec.ofNat width state.a,
           p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)),
           BitVec.ofNat width (state.a + state.n),
           p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + state.n),
           curr, memory, domain) = wordMoveResult at wordRun
        rcases wordMoveResult with ⟨nextAddr, midI, midPa, midIb, midPb, midMemory, moveOk⟩
        dsimp only at wordRun
        generalize wordTail : wordGenGcMoveRefs conf (k - 1)
          (nextAddr, last, midI, midPa, midIb, midPb, curr, midMemory, domain) = wordTailResult at wordRun
        rcases wordTailResult with ⟨lastAddr, lastI, lastPa, lastIb, lastPb, lastMemory, tailOk⟩
        simp only [Prod.mk.injEq] at wordRun
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := wordRun
        obtain ⟨header, left, right, xsMid, encoded, rootsLen, leftEq, rightEq,
          memoryResult, heapLen, moveSuccess, indexEq, limitEq, xsLen, accounting,
          cursorEq, paEq, pbEq, refsOut⟩ :=
          refScan_moveRoots conf genConf state middle roots moved len tag payload tail curr p
            nextAddr midI midPa midIb midPb xs memory midMemory domain frame moveOk
            pending move middleOk heapBound refClass lenBound refs separated length good wordMove
        subst moveOk
        simp only [Bool.true_and]
        obtain ⟨header2, encoded2, _, rootBound, decoded, _, _, _⟩ :=
          refScan_headRead conf genConf state roots len tag payload tail curr p xs memory domain frame
            pending refClass refs separated
        have headerEq : header = header2 := by
          have h := congrArg Prod.fst (encoded.symm.trans encoded2)
          simpa using h
        subst header2
        let next := { middle with r2 := tail, r3 := middle.r3 ++ [HeapElement.dataElement moved len (tag, payload)] }
        have nextMemory := refScan_nextMemory conf genConf state middle roots moved len tag payload tail left right
          header curr p midPa midPb xs xsMid midMemory domain frame move encoded rootsLen rootBound decoded
          leftEq rightEq paEq pbEq accounting length xsLen memoryResult
        obtain ⟨nextInvariant, h1Eq, _, nextRefs⟩ :=
          refScan_advanceInvariant genConf state middle roots moved len (tag, payload) tail right
            pending move middleOk rightEq invariant refs refsOut
        obtain ⟨middleH1, _, _, r3Eq⟩ := genMoveList_const genConf roots moved state middle move
        obtain ⟨nextCursor, nextLast⟩ :=
          refScan_nextPointers state middle roots moved len (tag, payload) tail left right p nextAddr
            xs.length xsMid.length pending h1Eq leftEq rightEq r3Eq rootsLen accounting length xsLen cursorEq
        obtain ⟨nextPa, nextPb, _⟩ :=
          refScan_regionAddresses state middle left right p midPa midPb xs.length paEq pbEq accounting length
        have positive : 0 < k := by simp [pending] at countBound; omega
        dsimp only [last] at wordTail
        rw [nextCursor, nextLast, indexEq, limitEq, nextPa, nextPb] at wordTail
        have recursiveWord : wordGenGcMoveRefs conf (k - 1)
            (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (next.h1 ++ next.h2 ++ next.r4 ++ next.r3) + xsMid.length),
             p + wordSemBytesInWord * BitVec.ofNat width (heapLength (next.h1 ++ next.h2 ++ next.r4 ++ next.r3 ++ next.r2) + xsMid.length),
             BitVec.ofNat width next.a,
             p + wordSemBytesInWord * BitVec.ofNat width (heapLength (next.h1 ++ next.h2)),
             BitVec.ofNat width (next.a + next.n),
             p + wordSemBytesInWord * BitVec.ofNat width (heapLength (next.h1 ++ next.h2) + next.n),
             curr, midMemory, domain) = (lastAddr, lastI, lastPa, lastIb, lastPb, lastMemory, tailOk) := by
          simpa only [next, middleH1, leftEq, List.append_assoc] using wordTail
        obtain ⟨xsFinal, finalMemory, finalR3, finalR2, finalHeap, finalOk, finalI, finalIb, finalLen,
          finalAccounting, finalPa, finalPb, finalLast, finalInvariant, finalRefs⟩ :=
          ih (k - 1) (by omega) next state1 midMemory lastMemory xsMid lastPb lastPa lastIb lastI lastAddr tailOk
            recursive stateOk (by simpa [next, heapLen] using heapBound)
            (by simpa [next, heapLen] using heapBytesBound) recursiveWord tailBound nextInvariant
            nextMemory nextRefs xsLen.symm
        refine ⟨xsFinal, finalMemory, finalR3, finalR2, ?_, finalOk, finalI, finalIb, finalLen,
          ?_, finalPa, finalPb, ?_, finalInvariant, finalRefs⟩
        · simpa [next, heapLen] using finalHeap
        · simp only [next, leftEq, rightEq, heapLength_append] at finalAccounting
          omega
        · dsimp only [next] at finalLast
          rw [← nextLast] at finalLast
          simpa only [pending] using finalLast

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

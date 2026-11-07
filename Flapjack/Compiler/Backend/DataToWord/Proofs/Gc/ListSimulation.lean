import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.RootsSimulation

/-! Simulation of copying collector roots stored in word memory. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.CopyingGc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private theorem starEmptyRight {α : Type} (p : (α → Prop) → Prop) : SetSep.star p SetSep.emp = p := by
  rw [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft]

private theorem prepareWrite {α : Type} (h c free one tail frame : (α → Prop) → Prop) :
    SetSep.star (SetSep.star (SetSep.star h c) free) (SetSep.star one (SetSep.star tail frame)) =
      SetSep.star one (SetSep.star (SetSep.star (SetSep.star h free) tail) (SetSep.star c frame)) := by
  simp only [← SetSep.starAssoc]
  rw [star_swap_first free one, star_swap_first c one, star_swap_first h one,
    star_swap_first c free, star_swap_first c tail]

private theorem finishWrite {α : Type} (h t free roots one copied frame : (α → Prop) → Prop) :
    SetSep.star (SetSep.star (SetSep.star (SetSep.star h t) free) roots)
        (SetSep.star one (SetSep.star copied frame)) =
      SetSep.star (SetSep.star (SetSep.star (SetSep.star h (SetSep.star copied t)) free)
        (SetSep.star one roots)) frame := by
  simp only [← SetSep.starAssoc]
  rw [star_swap_first roots one, star_swap_first roots copied, star_swap_first free one,
    star_swap_first free copied, star_swap_first t one, star_swap_first t copied,
    star_swap_first one copied, star_swap_first one t, star_swap_first one free]

/-- The original collector move-list theorem, including the root words in
memory and the exact machine-word pointer advancement. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_move_list_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGcMoveList_thm {width : Nat} [NeZero width] (conf : Config)
    (roots : List (HeapAddress (WordLocW width))) :
    ∀ (a n : Nat) (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
      (limit : Nat) (pa : BitVec width) (roots1 : List (HeapAddress (WordLocW width)))
      (h1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
      (a1 n1 : Nat) (heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
      (pa1 : BitVec width) (memory memory1 : BitVec width → WordLocW width)
      (xs : List (WordLocW width)) (i1 : BitVec width) (c1 : Bool)
      (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
      (k k1 curr : BitVec width) (domain : BitVec width → Bool),
      gcMoveList (roots, [], a, n, heap, true, limit) = (roots1, h1, a1, n1, heap1, true) →
      heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf →
      wordGcMoveList conf (k, BitVec.ofNat width roots.length, BitVec.ofNat width a, pa, curr, memory, domain) =
        (k1, i1, pa1, memory1, c1) →
      SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap conf) (Misc.wordList pa xs))
        (Misc.wordList k (roots.map (wordAddr conf)))) frame
        (SetSep.fun2Set (memory, fun address => domain address = true)) →
      xs.length = n → roots.length < 2 ^ width →
      ∃ xs1,
        SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap1 conf)
          (wordHeap pa h1 conf)) (Misc.wordList pa1 xs1)) (Misc.wordList k (roots1.map (wordAddr conf)))) frame
          (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
        heapLength heap1 = heapLength heap ∧ c1 = true ∧ i1 = BitVec.ofNat width a1 ∧ n1 = xs1.length ∧
        k1 = k + BitVec.ofNat width roots.length * wordSemBytesInWord ∧
        pa1 = pa + BitVec.ofNat width (heapLength h1) * wordSemBytesInWord := by
  induction roots with
  | nil =>
    intro a n heap limit pa roots1 h1 a1 n1 heap1 pa1 memory memory1 xs i1 c1 frame k k1 curr domain
      abstractRun _ wordRun separated length _
    simp only [gcMoveList, Prod.mk.injEq] at abstractRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl, _⟩ := abstractRun
    simp only [List.length_nil, wordGcMoveList_zero, Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
    refine ⟨xs, ?_, rfl, rfl, rfl, length.symm, ?_, ?_⟩
    · simpa [wordHeap, starEmptyRight] using separated
    · simp
    · simp [heapLength]
  | cons root roots ih =>
    intro a n heap limit pa roots1 h1 a1 n1 heap1 pa1 memory memory1 xs i1 c1 frame k k1 curr domain
      abstractRun bound wordRun separated length rootBound
    simp only [gcMoveList] at abstractRun
    generalize headRun : gcMove (root, [], a, n, heap, true, limit) = headResult at abstractRun
    rcases headResult with ⟨root', copied, a', n', heap', status⟩
    rw [gcMoveList_alt roots copied a' n' heap' status limit () () () () () ()] at abstractRun
    generalize tailRun : gcMoveList (roots, [], a', n', heap', status, limit) = tailResult at abstractRun
    rcases tailResult with ⟨roots', copied', a'', n'', heap'', status'⟩
    simp only [Prod.mk.injEq] at abstractRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := abstractRun
    have statusTrue : status = true :=
      (gcMoveList_ok roots roots' [] copied' heap' heap'' a' n' limit a'' n'' 0 status () tailRun).1
    subst status
    have countBound : roots.length + 1 < 2 ^ width := by simpa using rootBound
    have nonzero : BitVec.ofNat width (roots.length + 1) ≠ 0 := by
      intro eq
      have eq' := congrArg BitVec.toNat eq
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound] at eq'
    have minus : BitVec.ofNat width (roots.length + 1) - 1 = BitVec.ofNat width roots.length := by
      rw [BitVec.ofNat_add]
      simp
    have headSep : SetSep.star (SetSep.star (wordHeap curr heap conf) (Misc.wordList pa xs))
        (SetSep.star (SetSep.one (k, wordAddr conf root))
          (SetSep.star (Misc.wordList (k + StackRemove.bytesInWord width) (roots.map (wordAddr conf))) frame))
        (SetSep.fun2Set (memory, fun address => domain address = true)) := by
      simpa only [List.map_cons, Misc.wordList, ← SetSep.starAssoc] using separated
    have read : memory k = wordAddr conf root ∧ domain k = true := by
      rcases headSep with ⟨left, right, outer, _, oneAndRest⟩
      rcases oneAndRest with ⟨one, rest, inner, oneEq, _⟩
      have graph : SetSep.fun2Set (memory, fun address => domain address = true) (k, wordAddr conf root) := by
        rw [← outer.1, ← inner.1]
        exact Or.inr (Or.inl (by rw [oneEq]))
      exact (SetSep.fun2SetThm memory _ _ _).mp graph
    simp only [List.length_cons] at wordRun
    rw [wordGcMoveList_of_ne conf nonzero, minus, read.1] at wordRun
    generalize wordHeadRun : wordGcMove conf (wordAddr conf root, BitVec.ofNat width a, pa, curr, memory, domain) =
      wordHeadResult at wordRun
    rcases wordHeadResult with ⟨wordRoot, iHead, paHead, memoryHead, okHead⟩
    generalize wordTailRun : wordGcMoveList conf (k + wordSemBytesInWord, BitVec.ofNat width roots.length,
      iHead, paHead, curr, gcUpdate k wordRoot memoryHead, domain) = wordTailResult at wordRun
    rcases wordTailResult with ⟨kTail, iTail, paTail, memoryTail, okTail⟩
    simp only [wordHeadRun, wordTailRun, read.2, Bool.true_and, Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := wordRun
    obtain ⟨freeHead, headSep, rootEq, heapLen, headOk, indexEq, freeLen, paEq⟩ :=
      wordGcMove_thm conf root root' a n limit a' n' heap heap' copied curr pa paHead iHead xs
        memory memoryHead domain _ wordRoot okHead headRun bound headSep wordHeadRun length
    rw [prepareWrite] at headSep
    have written := SetSep.writeFun2Set wordRoot k (wordAddr conf root) _ memoryHead
      (fun address => domain address = true) headSep
    have updateGraph : SetSep.fun2Set (gcUpdate k wordRoot memoryHead, fun address => domain address = true) =
        SetSep.fun2Set ((fun key => @ite _ (key = k) (Classical.propDecidable _) wordRoot (memoryHead key)),
          fun address => domain address = true) := by
      funext entry
      rcases entry with ⟨key, val⟩
      simp only [SetSep.fun2SetThm, gcUpdate]
      by_cases h : key = k
      · subst key
        simp only [ite_true]
      · have h' : k ≠ key := Ne.symm h
        simp only [h, h', ite_false]
    have tailSep : SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap' conf)
        (Misc.wordList paHead freeHead))
        (Misc.wordList (k + StackRemove.bytesInWord width) (roots.map (wordAddr conf))))
        (SetSep.star (SetSep.one (k, wordRoot)) (SetSep.star (wordHeap pa copied conf) frame))
        (SetSep.fun2Set (gcUpdate k wordRoot memoryHead, fun address => domain address = true)) := by
      rw [updateGraph]
      simp only [← SetSep.starAssoc] at written ⊢
      rw [SetSep.starComm frame (SetSep.one (k, wordRoot)),
        star_swap_first (wordHeap pa copied conf) (SetSep.one (k, wordRoot)) frame] at written
      exact written
    have bound' : heapLength heap' ≤ 2 ^ width / 2 ^ shiftLength conf := by simpa [heapLen] using bound
    have wordTailRun' : wordGcMoveList conf (k + StackRemove.bytesInWord width,
        BitVec.ofNat width roots.length, BitVec.ofNat width a', paHead, curr,
        gcUpdate k wordRoot memoryHead, domain) = (kTail, iTail, paTail, memoryTail, okTail) := by
      simpa [indexEq, wordSemBytesInWord, StackRemove.bytesInWord] using wordTailRun
    have tailBound : roots.length < 2 ^ width := by omega
    obtain ⟨freeTail, tailSep, heapLen', tailOk, indexEq', freeLen', kEq', paEq'⟩ :=
      ih a' n' heap' limit paHead roots' copied' a'' n'' heap'' paTail
        (gcUpdate k wordRoot memoryHead) memoryTail freeHead iTail okTail
        (SetSep.star (SetSep.one (k, wordRoot)) (SetSep.star (wordHeap pa copied conf) frame))
        (k + StackRemove.bytesInWord width) kTail curr domain tailRun bound' wordTailRun' tailSep
        freeLen.symm tailBound
    refine ⟨freeTail, ?_, heapLen'.trans heapLen, ?_, indexEq', freeLen', ?_, ?_⟩
    · rw [finishWrite] at tailSep
      rw [wordHeapAppend]
      have paEq'': paHead = pa + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength copied) := by
        simpa [wordSemBytesInWord, StackRemove.bytesInWord] using paEq
      simpa only [paEq'', List.map_cons, Misc.wordList, rootEq] using tailSep
    · simp [headOk, tailOk]
    · rw [kEq']
      simp only [List.length_cons, BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul,
        wordSemBytesInWord, StackRemove.bytesInWord]
      ac_rfl
    · rw [paEq', paEq]
      simp only [heapLength_append, BitVec.ofNat_add, BitVec.add_mul]
      ac_rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

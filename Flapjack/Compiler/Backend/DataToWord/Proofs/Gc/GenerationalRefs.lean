import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.HeapWordList

/-! Major collector reference-scan simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

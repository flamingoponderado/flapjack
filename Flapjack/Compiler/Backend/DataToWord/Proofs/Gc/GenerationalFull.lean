import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalLoop
import Flapjack.Compiler.Backend.StackAlloc.Proofs.WordLemmas

/-! Full major generational collector simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private instance {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩
private instance {α : Type} : Std.Commutative (SetSep.star (α := α)) := ⟨SetSep.starComm⟩

/-- The byte count passed to the concrete collector decodes to the original
heap word count when the original byte-size bound holds. -/
theorem genFull_decodeLength {width : Nat} [NeZero width] (n : Nat)
    (good : goodDimindex width) (bound : n * (width / 8) < 2 ^ width) :
    ((wordSemBytesInWord * BitVec.ofNat width n) >>> wordShiftAmount width : BitVec width) =
      BitVec.ofNat width n ∧
    ((wordSemBytesInWord * BitVec.ofNat width n) >>> wordShiftAmount width : BitVec width).toNat = n := by
  have small : n < 2 ^ width := by
    rcases good with h | h <;> subst width <;> norm_num at bound ⊢ <;> omega
  have bytes : (wordSemBytesInWord : BitVec width).toNat * (BitVec.ofNat width n).toNat < 2 ^ width := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
    rcases good with h | h <;> subst width <;>
      simpa [wordSemBytesInWord, Nat.mul_comm] using bound
  have eq := StackAlloc.bytesInWord_wordShift (n := BitVec.ofNat width n) ⟨good, bytes⟩
  exact ⟨eq, by rw [eq]; simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]⟩

/-- Original full major-collector simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGc_thm {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width)))
    (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (curr new pb1 pa1 ib1 i1 : BitVec width)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (roots1' : List (WordLocW width)) (c1 : Bool)
    (abstractRun : GenGc.genGc genConf (roots, heap) = (roots1, state1)) (stateOk : state1.ok = true)
    (wordRun : wordGenGc conf (roots.map (wordAddr conf), curr, new,
      wordSemBytesInWord * BitVec.ofNat width (heapLength heap), memory, domain) =
        (roots1', i1, pa1, ib1, pb1, memory1, c1))
    (heapBound : heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (byteBound : heapLength heap * (width / 8) < 2 ^ width)
    (dataBound : conf.lenSize + 2 < width)
    (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (lenBound : conf.lenSize + 5 ≤ width) (good : goodDimindex width)
    (separated : SetSep.star (SetSep.star (wordHeap curr heap conf)
      (Misc.wordListExists new (heapLength heap))) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (goodAgain : goodDimindex width) :
    ∃ xs1,
      SetSep.star (SetSep.star (wordHeap curr state1.heap conf) (wordHeapParts conf new state1 xs1)) frame
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      state1.h2 = [] ∧ state1.r4 = [] ∧ state1.r3 = [] ∧ state1.r2 = [] ∧
      roots1' = roots1.map (wordAddr conf) ∧ heapLength state1.heap = heapLength heap ∧ c1 = true ∧
      i1 = BitVec.ofNat width state1.a ∧ ib1 = BitVec.ofNat width (state1.a + state1.n) ∧
      pa1 = new + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h1) ∧
      pb1 = new + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h1 + state1.n) ∧
      roots1' = roots1.map (wordAddr conf) ∧ state1.n = xs1.length ∧ genLenInv state1 ∧
      state1.r1.all (isRefElement genConf.isRef) = true := by
  classical
  let initial : GcState (WordLocW width) (HeapTag × List (WordLocW width)) :=
    { emptyGcState with heap := heap, n := genConf.limit, ok := decide (heapLength heap = genConf.limit) }
  have initialEq : GenGc.genGc genConf (roots, heap) =
      let (rs, mid) := GenGc.gcMoveList genConf initial roots
      (rs, GenGc.gcMoveLoop genConf mid genConf.limit) := by
    rfl
  rw [initialEq] at abstractRun
  generalize rootsRun : GenGc.gcMoveList genConf initial roots = result at abstractRun
  obtain ⟨moved, middle⟩ := result
  simp only [Prod.mk.injEq] at abstractRun
  obtain ⟨rfl, loopRun⟩ := abstractRun
  have middleOk : middle.ok = true :=
    GenGc.gcMoveLoop_ok genConf middle genConf.limit (by simpa [loopRun] using stateOk)
  have initialOk := GenGc.gcMoveList_ok genConf roots moved initial middle rootsRun middleOk
  have limitEq : genConf.limit = heapLength heap := by simpa [initial, eq_comm] using initialOk
  obtain ⟨xs, xsLen, sep⟩ : ∃ xs : List (WordLocW width), xs.length = heapLength heap ∧
      SetSep.star (SetSep.star (wordHeap curr heap conf) (Misc.wordList new xs)) frame
        (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    obtain ⟨left, right, split, ⟨a, b, split', ha, hb⟩, hf⟩ := separated
    obtain ⟨xs, hx, hn⟩ := (show ∃ xs : List (WordLocW width), Misc.wordList new xs b ∧ xs.length = heapLength heap by
      simpa only [Misc.wordListExists, SetSep.sepExists, StackRemove.WordListExists.starCond] using hb)
    exact ⟨xs, hn, left, right, split, ⟨a, b, split', ha, hx⟩, hf⟩
  have decoded := genFull_decodeLength (heapLength heap) good byteBound
  have wordCount : (BitVec.ofNat width (heapLength heap)).toNat = heapLength heap := by
    rw [← decoded.1]
    exact decoded.2
  simp only [wordGenGc, decoded.1, wordCount] at wordRun
  generalize rootWord : wordGenGcMoveRoots conf
      (roots.map (wordAddr conf), 0, new, BitVec.ofNat width (heapLength heap),
        new + wordSemBytesInWord * BitVec.ofNat width (heapLength heap), curr, memory, domain) = result at wordRun
  obtain ⟨rootsW, iMid, paMid, ibMid, pbMid, memoryMid, flagMid⟩ := result
  generalize loopWord : wordGenGcMoveLoop conf (heapLength heap)
      (new, iMid, paMid, ibMid, pbMid, new + wordSemBytesInWord * BitVec.ofNat width (heapLength heap),
        curr, memoryMid, domain) = result at wordRun
  obtain ⟨iOut, paOut, ibOut, pbOut, memoryOut, flagOut⟩ := result
  simp only [Prod.mk.injEq] at wordRun
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, flags⟩ := wordRun
  obtain ⟨xsMid, sepMid, rootsEq, heapEq, midTrue, iEq, ibEq, xsMidLen, accounting,
      paEq, pbEq, refsMid⟩ :=
    wordGenGcMoveRoots_thm conf genConf initial middle roots moved curr new iMid paMid ibMid pbMid xs
      memory memoryMid domain frame rootsW flagMid rootsRun middleOk (by simp [initial, emptyGcState])
      (by simp [initial, emptyGcState]) (by simpa [initial] using heapBound) refClass lenBound
      (by simpa [initial] using sep) (by simpa [initial, emptyGcState, limitEq] using rootWord)
      (by simpa [initial, limitEq] using xsLen) good (by simp [initial, emptyGcState])
  obtain ⟨h1Empty, r1Empty, r2Empty, r3Empty⟩ := genMoveList_const genConf roots moved initial middle rootsRun
  simp only [initial, emptyGcState] at h1Empty r1Empty r2Empty r3Empty heapEq
  simp only [initial, limitEq] at accounting
  have middleInv : genLenInv middle := by
    simp only [genLenInv, h1Empty, r1Empty, r2Empty, r3Empty, List.nil_append, List.append_nil,
      heapEq]
    omega
  have pbNorm : pbMid = new + wordSemBytesInWord *
      BitVec.ofNat width (heapLength middle.h2 + middle.n) := by
    rw [pbEq, paEq, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
  have endCount : heapLength (middle.h1 ++ middle.h2 ++ middle.r4) + middle.n = heapLength heap := by
    simp only [h1Empty, List.nil_append, heapLength_append]
    omega
  have sepLoop : SetSep.star (SetSep.star (wordHeap curr middle.heap conf) (wordHeapParts conf new middle xsMid)) frame
      (SetSep.fun2Set (memoryMid, fun address => domain address = true)) := by
    simp only [wordHeapParts, h1Empty, r1Empty, r2Empty, r3Empty, List.nil_append, List.append_nil, ← xsMidLen]
    rw [paEq, pbNorm] at sepMid
    have rearrange : SetSep.star
        (SetSep.star (SetSep.star (SetSep.star (wordHeap curr middle.heap conf) (wordHeap new middle.h2 conf))
          (wordHeap (new + wordSemBytesInWord * BitVec.ofNat width (heapLength middle.h2 + middle.n)) middle.r4 conf))
          (Misc.wordList (new + wordSemBytesInWord * BitVec.ofNat width (heapLength middle.h2)) xsMid)) frame =
        SetSep.star (SetSep.star (wordHeap curr middle.heap conf)
          (SetSep.star (SetSep.star (wordHeap new middle.h2 conf)
            (Misc.wordList (new + wordSemBytesInWord * BitVec.ofNat width (heapLength middle.h2)) xsMid))
            (wordHeap (new + wordSemBytesInWord * BitVec.ofNat width (heapLength middle.h2 + middle.n)) middle.r4 conf))) frame := by
      ac_rfl
    rwa [rearrange] at sepMid
  have loopRun' : GenGc.gcMoveLoop genConf middle (heapLength heap) = state1 := by
    simpa [limitEq] using loopRun
  have loopWord' : wordGenGcMoveLoop conf (heapLength heap)
      (new + wordSemBytesInWord * BitVec.ofNat width (heapLength middle.h1),
       BitVec.ofNat width middle.a,
       new + wordSemBytesInWord * BitVec.ofNat width (heapLength (middle.h1 ++ middle.h2)),
       BitVec.ofNat width (middle.a + middle.n),
       new + wordSemBytesInWord * BitVec.ofNat width (heapLength (middle.h1 ++ middle.h2) + middle.n),
       new + wordSemBytesInWord * BitVec.ofNat width (heapLength (middle.h1 ++ middle.h2 ++ middle.r4) + middle.n),
       curr, memoryMid, domain) = (iOut, paOut, ibOut, pbOut, memoryOut, flagOut) := by
    rw [iEq, ibEq, paEq, pbNorm] at loopWord
    rw [endCount]
    simpa [h1Empty, heapLength] using loopWord
  obtain ⟨xsFinal, sepFinal, h2Final, r4Final, r3Final, r2Final, heapFinal, flagTrue,
      iFinal, xsFinalLen, invFinal, paFinal, pbFinal, ibFinal, refsFinal⟩ :=
    wordGenGcMoveLoop_thm conf genConf (heapLength heap) middle state1 memoryMid memoryOut domain curr new xsMid
      pbOut paOut ibOut iOut frame flagOut loopRun' stateOk (by simpa [heapEq] using heapBound)
      (by simpa [heapEq] using byteBound) dataBound r3Empty r2Empty refClass lenBound loopWord'
      middleInv sepLoop refsMid xsMidLen.symm goodAgain
  refine ⟨xsFinal, sepFinal, h2Final, r4Final, r3Final, r2Final, rootsEq, ?_, ?_,
    iFinal, ibFinal, paFinal, pbFinal, rootsEq, xsFinalLen, invFinal, refsFinal⟩
  · exact heapFinal.trans heapEq
  · simpa [midTrue, flagTrue] using flags.symm

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

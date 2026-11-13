module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialData

@[expose] public section

/-! Remembered-reference scan for partial generational collection. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

instance partialRefsInst1 {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩
instance partialRefsInst2 {α : Type} : Std.Commutative (SetSep.star (α := α)) := ⟨SetSep.starComm⟩

/-- Expose the first remembered reference's header and roots for the partial
root-list simulation. This is local factoring of the reference-scan proof. -/
theorem partialRefScan_headCell {width : Nat} [NeZero width] (conf : Config)
    (roots : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width))
    (tail old current : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr pa k : BitVec width) (xs : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (mutable : isMutTag tag)
    (separated : SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (Misc.wordList pa xs)) (wordHeap k (.dataElement roots len (tag, payload) :: tail) conf)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true))) :
    ∃ header : BitVec width,
      wordPayload roots len tag payload conf = (header, roots.map (wordAddr conf), true) ∧
      roots.length = len ∧ roots.length < 2 ^ (width - 4) ∧
      decodeLength conf header = BitVec.ofNat width roots.length ∧
      memory k = .word header ∧ domain k = true ∧
      SetSep.star (SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
        (Misc.wordList pa xs)) (Misc.wordList (k + wordSemBytesInWord) (roots.map (wordAddr conf))))
        (SetSep.star (SetSep.one (k, .word header))
          (SetSep.star frame (wordHeap (k + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf)))
        (SetSep.fun2Set (memory, fun address => domain address = true)) := by
  let source := wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf
  let rest := SetSep.star source frame
  have arrangement : SetSep.star (SetSep.star
      (wordHeap k ([] ++ .dataElement roots len (tag, payload) :: tail) conf) (Misc.wordList pa xs)) rest
      (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    have reorder : SetSep.star (SetSep.star (SetSep.star source (Misc.wordList pa xs))
        (wordHeap k (.dataElement roots len (tag, payload) :: tail) conf)) frame =
      SetSep.star (SetSep.star (wordHeap k (.dataElement roots len (tag, payload) :: tail) conf)
        (Misc.wordList pa xs)) rest := by dsimp [rest]; ac_rfl
    change SetSep.star (SetSep.star (SetSep.star source (Misc.wordList pa xs))
      (wordHeap k (.dataElement roots len (tag, payload) :: tail) conf)) frame _ at separated
    rw [reorder] at separated
    simpa only [List.nil_append] using separated
  obtain ⟨header, encoded, rootLen, bound, decoded, read, present, cell⟩ :=
    refScan_dataCell conf [] tail roots len tag payload k pa xs memory domain rest mutable arrangement
  refine ⟨header, encoded, rootLen, bound, decoded, ?_, ?_, ?_⟩
  · simpa [heapLength] using read
  · simpa [heapLength] using present
  · simp only [heapLength, List.map_nil, List.sum_nil, wordHeap] at cell
    simp only [BitVec.mul_zero, BitVec.add_zero] at cell
    have reorder : SetSep.star (SetSep.star (Misc.wordList pa xs)
        (Misc.wordList (k + wordSemBytesInWord) (roots.map (wordAddr conf))))
        (SetSep.star (SetSep.one (k, .word header)) (SetSep.star (SetSep.star rest SetSep.emp)
          (wordHeap (k + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf))) =
      SetSep.star (SetSep.star (SetSep.star source (Misc.wordList pa xs))
        (Misc.wordList (k + wordSemBytesInWord) (roots.map (wordAddr conf))))
        (SetSep.star (SetSep.one (k, .word header))
          (SetSep.star frame (wordHeap (k + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf))) := by
      rw [SetSep.starComm rest SetSep.emp, StackRemove.StackHeap.starEmptyLeft]
      dsimp [rest]
      ac_rfl
    exact (congrFun reorder _).mp cell

/-- The represented nonempty reference list takes one concrete scan step. -/
theorem partialRefScan_wordStep {width : Nat} [NeZero width] (conf : Config) (fuel : Nat)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (roots : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width))
    (tail old current : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr pa k i : BitVec width) (xs : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (mutable : isMutTag tag)
    (separated : SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (Misc.wordList pa xs)) (wordHeap k (.dataElement roots len (tag, payload) :: tail) conf)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (countBound : heapLength (.dataElement roots len (tag, payload) :: tail) ≤ fuel)
    (byteBound : heapLength (.dataElement roots len (tag, payload) :: tail) * (width / 8) < 2 ^ width)
    (good : goodDimindex width) :
    let last := k + wordSemBytesInWord * BitVec.ofNat width (heapLength (.dataElement roots len (tag, payload) :: tail))
    let gs := wordSemBytesInWord * BitVec.ofNat width genConf.genStart
    let rs := wordSemBytesInWord * BitVec.ofNat width genConf.refsStart
    wordGenGcPartialMoveRefList fuel conf (k, i, pa, curr, memory, domain, true, gs, rs, last) =
      (let (next, i1, pa1, memory1, c1) := wordGenGcPartialMoveList conf
        (k + wordSemBytesInWord, BitVec.ofNat width roots.length, i, pa, curr, memory, domain, gs, rs)
       wordGenGcPartialMoveRefList (fuel - 1) conf (next, i1, pa1, curr, memory1, domain, c1, gs, rs, last)) := by
  obtain ⟨header, _, _, _, decoded, read, present, _⟩ :=
    partialRefScan_headCell conf roots len tag payload tail old current curr pa k xs memory domain frame mutable separated
  have positive : 0 < heapLength (.dataElement roots len (tag, payload) :: tail) := by simp [heapLength, elLength]
  have bytesPositive : 0 < width / 8 := by rcases good with rfl | rfl <;> decide
  have bound : (width / 8) * heapLength (.dataElement roots len (tag, payload) :: tail) < 2 ^ width := by
    simpa only [Nat.mul_comm] using byteBound
  have nonzero : wordSemBytesInWord * BitVec.ofNat width (heapLength (.dataElement roots len (tag, payload) :: tail)) ≠ 0 := by
    intro eq
    have natEq := congrArg BitVec.toNat eq
    simp [wordSemBytesInWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at natEq
    rcases natEq with small | empty <;> omega
  have different : k ≠ k + wordSemBytesInWord * BitVec.ofNat width (heapLength (.dataElement roots len (tag, payload) :: tail)) := by
    intro eq
    apply nonzero
    apply add_left_cancel (a := k)
    simpa using eq.symm
  have fuelNonzero : fuel ≠ 0 := by omega
  dsimp only
  rw [wordGenGcPartialMoveRefList, ite_eq_right different, ite_eq_right fuelNonzero]
  simp only [read, present, wordSemIsWordLoc, wordSemTheWord, Bool.true_and, decoded]

/-- Move the first remembered reference's roots while retaining its header
and the remaining references in the separation frame. -/
theorem partialRefScan_moveRoots {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (state middle : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots moved : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width))
    (tail old current refs : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr pa k k1 i1 pa1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (c1 : Bool)
    (run : GenGcPartial.gcMoveList genConf state roots = (moved, middle)) (middleOk : middle.ok = true)
    (h2Empty : state.h2 = []) (r4Empty : state.r4 = []) (limitEq : genConf.limit = heapLength state.heap)
    (heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (ordered : genConf.genStart ≤ genConf.refsStart) (refBound : genConf.refsStart ≤ heapLength state.heap)
    (segment : heapSegment (genConf.genStart, genConf.refsStart) state.heap = some (old, current, refs))
    (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (byteBound : heapLength state.heap * (width / 8) < 2 ^ width) (mutable : isMutTag tag)
    (separated : SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (Misc.wordList pa xs)) (wordHeap k (.dataElement roots len (tag, payload) :: tail) conf)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (wordRun : wordGenGcPartialMoveList conf (k + wordSemBytesInWord, BitVec.ofNat width roots.length,
      BitVec.ofNat width state.a, pa, curr, memory, domain,
      wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
      wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) = (k1, i1, pa1, memory1, c1))
    (length : xs.length = state.n) (good : goodDimindex width) :
    ∃ (header : BitVec width) (xs1 : List (WordLocW width))
      (current1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))),
      wordPayload roots len tag payload conf = (header, roots.map (wordAddr conf), true) ∧
      roots.length = len ∧ roots.length < 2 ^ (width - 4) ∧ decodeLength conf header = BitVec.ofNat width roots.length ∧
      SetSep.star (SetSep.star (SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current1 conf)
        (wordHeap pa middle.h2 conf)) (Misc.wordList pa1 xs1))
        (Misc.wordList (k + wordSemBytesInWord) (moved.map (wordAddr conf))))
        (SetSep.star (SetSep.one (k, .word header))
          (SetSep.star frame (wordHeap (k + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf)))
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      heapLength middle.heap = heapLength state.heap ∧
      heapSegment (genConf.genStart, genConf.refsStart) middle.heap = some (old, current1, refs) ∧
      c1 = true ∧ i1 = BitVec.ofNat width middle.a ∧ middle.n = xs1.length ∧
      state.n = heapLength middle.h2 + middle.n + heapLength middle.r4 ∧
      k1 = (k + wordSemBytesInWord) + BitVec.ofNat width roots.length * wordSemBytesInWord ∧
      pa1 = pa + wordSemBytesInWord * BitVec.ofNat width (heapLength middle.h2) := by
  obtain ⟨header, encoded, rootsLen, rootsBound, decoded, _, _, lists⟩ :=
    partialRefScan_headCell conf roots len tag payload tail old current curr pa k xs memory domain frame mutable separated
  have rootBound : roots.length < 2 ^ width := by
    have widthPos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
    have exponent : width - 4 < width := by omega
    have boundPow : 2 ^ (width - 4) < 2 ^ width := Nat.pow_lt_pow_right (by decide : 1 < 2) exponent
    omega
  let rootFrame := SetSep.star (SetSep.one (k, WordLocW.word header))
    (SetSep.star frame (wordHeap (k + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf))
  obtain ⟨xs1, current1, memoryResult, heapLen, segment1, success, indexEq, xsLen, accounting, cursorEq, paEq⟩ :=
    wordGenGcPartialMoveList_thm conf genConf roots state middle moved old current refs curr pa
      (k + wordSemBytesInWord) k1 i1 pa1 xs memory memory1 domain rootFrame c1 run middleOk h2Empty r4Empty
      limitEq heapBound ordered refBound segment refClass byteBound lists wordRun length good rootBound
  exact ⟨header, xs1, current1, encoded, rootsLen, rootsBound, decoded, memoryResult, heapLen, segment1,
    success, indexEq, xsLen, accounting, cursorEq, paEq⟩

/-- Retain the rewritten reference and newly copied data in the frame while
the recursive scan processes the remaining references. -/
theorem partialRefScan_reframe {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (state middle : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots moved : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width))
    (tail current old : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (header curr pa k pa1 : BitVec width) (xs1 : List (WordLocW width))
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (run : GenGcPartial.gcMoveList genConf state roots = (moved, middle))
    (encoded : wordPayload roots len tag payload conf = (header, roots.map (wordAddr conf), true))
    (rootsLen : roots.length = len) (bound : roots.length < 2 ^ (width - 4))
    (decoded : decodeLength conf header = BitVec.ofNat width roots.length) :
    SetSep.star (SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (wordHeap pa middle.h2 conf)) (Misc.wordList pa1 xs1))
      (Misc.wordList (k + wordSemBytesInWord) (moved.map (wordAddr conf))))
      (SetSep.star (SetSep.one (k, .word header))
        (SetSep.star frame (wordHeap (k + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf))) =
    SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (Misc.wordList pa1 xs1)) (wordHeap (k + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf))
      (SetSep.star (SetSep.star frame (wordHeap pa middle.h2 conf))
        (wordEl k (.dataElement moved len (tag, payload)) conf)) := by
  have element := partialDataScan_movedElement conf genConf state middle roots moved len tag payload header k
    run encoded rootsLen bound decoded
  rw [element]
  ac_rfl

/-- Reference traversal preserves the reference shapes, their total size,
and the size of the underlying heap, even if the traversal fails. -/
theorem partialRefScan_abstractProperties {α β γ : Type} (conf : GenGcPartial.Config γ)
    (refs moved : List (HeapElement α (HeapTag × β))) (state final : GcState α γ)
    (run : GenGcPartial.gcMoveRefList conf state refs = (moved, final))
    (allRefs : ∀ element ∈ refs, isRef element) :
    (∀ element ∈ moved, isRef element) ∧ heapLength moved = heapLength refs ∧
      heapLength final.heap = heapLength state.heap := by
  induction refs generalizing moved state final with
  | nil =>
    simp only [GenGcPartial.gcMoveRefList, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    simp
  | cons head refs ih =>
    cases head with
    | unused len =>
      have impossible := allRefs (.unused len) (by simp)
      simp [isRef] at impossible
    | forwardPointer ptr value len =>
      have impossible := allRefs (.forwardPointer ptr value len) (by simp)
      simp [isRef] at impossible
    | dataElement roots len payload =>
      rcases payload with ⟨tag, payload⟩
      have mutable : isMutTag tag := by simpa [isRef] using allRefs (.dataElement roots len (tag, payload)) (by simp)
      have tailRefs : ∀ element ∈ refs, isRef element := by
        intro element member
        exact allRefs element (by simp [member])
      simp only [GenGcPartial.gcMoveRefList] at run
      generalize headRun : GenGcPartial.gcMoveList conf state roots = result at run
      obtain ⟨roots1, middle⟩ := result
      generalize tailRun : GenGcPartial.gcMoveRefList conf middle refs = result at run
      obtain ⟨tail1, state1⟩ := result
      simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      obtain ⟨tailOk, tailLen, heapLen⟩ := ih tail1 middle state1 tailRun tailRefs
      have headHeap := GenGcPartial.gcMoveList_heapLength roots roots1 conf state middle headRun
      refine ⟨?_, ?_, heapLen.trans headHeap.symm⟩
      · intro element member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact mutable
        · exact tailOk element member
      · simp only [heapLength, List.map_cons, List.sum_cons, elLength]
        exact congrArg (fun n => len + 1 + n) tailLen

/-- Join the recursively scanned references and copied data back into the
two contiguous heap regions required by the caller. -/
theorem partialRefScan_reassemble {width : Nat} [NeZero width] (conf : Config)
    (source copied newly tail : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (moved : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width)) (base pa pa1 pa2 k : BitVec width) (xs2 : List (WordLocW width))
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (paEq : pa1 = pa + wordSemBytesInWord * BitVec.ofNat width (heapLength copied)) :
    SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap base source conf)
      (wordHeap pa1 newly conf)) (Misc.wordList pa2 xs2))
      (wordHeap (k + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf))
      (SetSep.star (SetSep.star frame (wordHeap pa copied conf))
        (wordEl k (.dataElement moved len (tag, payload)) conf)) =
    SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap base source conf)
      (wordHeap pa (copied ++ newly) conf)) (Misc.wordList pa2 xs2))
      (wordHeap k (.dataElement moved len (tag, payload) :: tail) conf)) frame := by
  change pa1 = pa + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength copied) at paEq
  rw [wordHeapAppend copied newly pa conf, ← paEq]
  simp only [wordHeap, elLength, wordSemBytesInWord, StackRemove.bytesInWord]
  ac_rfl

/-- Partial collector remembered-reference traversal simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_partial_move_ref_list_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMoveRefList_thm {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (refs0 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) :
    ∀ (fuel : Nat) (xs : List (WordLocW width))
      (refs1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
      (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
      (pa1 pa : BitVec width) (memory1 memory : BitVec width → WordLocW width) (i1 : BitVec width)
      (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (domain : BitVec width → Bool)
      (curr : BitVec width) (c1 : Bool) (k : BitVec width)
      (old current refs : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))),
      GenGcPartial.gcMoveRefList genConf state refs0 = (refs1, state1) → state1.ok = true →
      state.h2 = [] → state.r4 = [] → heapLength refs0 ≤ fuel →
      genConf.limit = heapLength state.heap → heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf →
      genConf.genStart ≤ genConf.refsStart → genConf.refsStart ≤ heapLength state.heap →
      heapSegment (genConf.genStart, genConf.refsStart) state.heap = some (old, current, refs) →
      heapLength refs0 ≤ heapLength state.heap → (∀ element ∈ refs0, isRef element) →
      (∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t) →
      heapLength state.heap * (width / 8) < 2 ^ width →
      SetSep.star (SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
        (Misc.wordList pa xs)) (wordHeap k refs0 conf)) frame
        (SetSep.fun2Set (memory, fun address => domain address = true)) →
      wordGenGcPartialMoveRefList fuel conf (k, BitVec.ofNat width state.a, pa, curr, memory, domain, true,
        wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
        wordSemBytesInWord * BitVec.ofNat width genConf.refsStart,
        k + wordSemBytesInWord * BitVec.ofNat width (heapLength refs0)) = (i1, pa1, memory1, c1) →
      xs.length = state.n → goodDimindex width → refs0.length < 2 ^ width →
      ∃ xs1 current1,
        SetSep.star (SetSep.star (SetSep.star (SetSep.star
          (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current1 conf)
          (wordHeap pa state1.h2 conf)) (Misc.wordList pa1 xs1)) (wordHeap k refs1 conf)) frame
          (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
        heapSegment (genConf.genStart, genConf.refsStart) state1.heap = some (old, current1, refs) ∧
        heapLength state1.heap = heapLength state.heap ∧ c1 = true ∧ i1 = BitVec.ofNat width state1.a ∧
        state1.n = xs1.length ∧ (∀ element ∈ refs1, isRef element) ∧
        state.n = heapLength state1.h2 + state1.n + heapLength state1.r4 ∧
        pa1 = pa + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h2) := by
  classical
  induction refs0 with
  | nil =>
    intro fuel xs refs1 state state1 pa1 pa memory1 memory i1 frame domain curr c1 k old current refs
      run stateOk h2Empty r4Empty fuelBound limitEq heapBound ordered refBound segment refsBound allRefs refClass byteBound
      separated wordRun length good listBound
    simp only [GenGcPartial.gcMoveRefList, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    simp only [heapLength, List.map_nil, List.sum_nil, BitVec.mul_zero, BitVec.add_zero] at wordRun
    rw [wordGenGcPartialMoveRefList] at wordRun
    simp only [↓reduceIte, Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl⟩ := wordRun
    refine ⟨xs, current, ?_, segment, rfl, rfl, rfl, length.symm, ?_, ?_, ?_⟩
    · have empRight : ∀ (p : ((BitVec width × WordLocW width) → Prop) → Prop), SetSep.star p SetSep.emp = p := by
        intro p
        rw [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft]
      simpa only [h2Empty, wordHeap, empRight] using separated
    · simp
    · simp [h2Empty, r4Empty, heapLength]
    · simp [h2Empty, heapLength]
  | cons head tail ih =>
    intro fuel xs refs1 state state1 pa1 pa memory1 memory i1 frame domain curr c1 k old current refs
      run stateOk h2Empty r4Empty fuelBound limitEq heapBound ordered refBound segment refsBound allRefs refClass byteBound
      separated wordRun length good listBound
    cases head with
    | unused len =>
      have bad := allRefs (.unused len) (by simp)
      simp [isRef] at bad
    | forwardPointer ptr value len =>
      have bad := allRefs (.forwardPointer ptr value len) (by simp)
      simp [isRef] at bad
    | dataElement roots len payload =>
      rcases payload with ⟨tag, payload⟩
      have mutable : isMutTag tag := by simpa [isRef] using allRefs (.dataElement roots len (tag, payload)) (by simp)
      have tailRefs : ∀ element ∈ tail, isRef element := by
        intro element member
        exact allRefs element (by simp [member])
      simp only [GenGcPartial.gcMoveRefList] at run
      generalize headRun : GenGcPartial.gcMoveList genConf state roots = result at run
      obtain ⟨roots1, middle⟩ := result
      generalize tailRun : GenGcPartial.gcMoveRefList genConf middle tail = result at run
      obtain ⟨tail1, final⟩ := result
      simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      have middleOk := partialMoveRefList_okBefore genConf tail middle tail1 final tailRun stateOk
      obtain ⟨left, right, leftEq, rightEq, clearRun⟩ :=
        partialMoveRefList_withNilLemma genConf tail middle tail1 final tailRun stateOk
      have byteBoundRefs : heapLength (.dataElement roots len (tag, payload) :: tail) * (width / 8) < 2 ^ width :=
        lt_of_le_of_lt (Nat.mul_le_mul_right _ refsBound) byteBound
      have step := partialRefScan_wordStep conf fuel genConf roots len tag payload tail old current curr pa k
        (BitVec.ofNat width state.a) xs memory domain frame mutable separated fuelBound byteBoundRefs good
      rw [step] at wordRun
      generalize wordHead : wordGenGcPartialMoveList conf
        (k + wordSemBytesInWord, BitVec.ofNat width roots.length, BitVec.ofNat width state.a, pa,
         curr, memory, domain, wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
         wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) = wordHeadResult at wordRun
      obtain ⟨nextAddr, midI, midPa, midMemory, moveOk⟩ := wordHeadResult
      dsimp only at wordRun
      obtain ⟨header, xsMid, currentMid, encoded, rootsLen, rootsBound, decoded, headMemory, heapLen, segmentMid,
        moveSuccess, indexEq, xsLen, accounting, cursorEq, paEq⟩ :=
        partialRefScan_moveRoots conf genConf state middle roots roots1 len tag payload tail old current refs curr pa k
          nextAddr midI midPa xs memory midMemory domain frame moveOk headRun middleOk h2Empty r4Empty limitEq heapBound
          ordered refBound segment refClass byteBound mutable separated wordHead length good
      subst moveOk
      have nextMemory := (congrFun (partialRefScan_reframe conf genConf state middle roots roots1 len tag payload
        tail currentMid old header curr pa k midPa xsMid frame headRun encoded rootsLen rootsBound decoded) _).mp headMemory
      have nextAddrEq : nextAddr = k + wordSemBytesInWord * BitVec.ofNat width (len + 1) := by
        rw [cursorEq, rootsLen]
        simp only [BitVec.ofNat_add, BitVec.mul_add, BitVec.mul_one]
        ac_rfl
      have lastEq : k + wordSemBytesInWord * BitVec.ofNat width
          (heapLength (.dataElement roots len (tag, payload) :: tail)) =
          nextAddr + wordSemBytesInWord * BitVec.ofNat width (heapLength tail) := by
        rw [nextAddrEq]
        simp only [heapLength, List.map_cons, List.sum_cons, elLength, BitVec.ofNat_add, BitVec.mul_add]
        ac_rfl
      have tailFuel : heapLength tail ≤ fuel - 1 := by
        simp [heapLength, elLength] at fuelBound ⊢
        omega
      have tailBound : heapLength tail ≤ heapLength middle.heap := by
        rw [heapLen]
        simp [heapLength, elLength] at refsBound ⊢
        omega
      have tailCount : tail.length < 2 ^ width := by simp at listBound; omega
      let cleared := { middle with h2 := [], r4 := [] }
      let clearedFinal := { final with h2 := left, r4 := right }
      let nextFrame := SetSep.star (SetSep.star frame (wordHeap pa middle.h2 conf))
        (wordEl k (.dataElement roots1 len (tag, payload)) conf)
      have recursiveWord : wordGenGcPartialMoveRefList (fuel - 1) conf
          (nextAddr, BitVec.ofNat width cleared.a, midPa, curr, midMemory, domain, true,
           wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
           wordSemBytesInWord * BitVec.ofNat width genConf.refsStart,
           nextAddr + wordSemBytesInWord * BitVec.ofNat width (heapLength tail)) = (i1, pa1, memory1, c1) := by
        rw [indexEq, lastEq] at wordRun
        simpa only [cleared] using wordRun
      have recursiveMemory : SetSep.star (SetSep.star (SetSep.star
          (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) currentMid conf)
          (Misc.wordList midPa xsMid)) (wordHeap nextAddr tail conf)) nextFrame
          (SetSep.fun2Set (midMemory, fun address => domain address = true)) := by
        simpa only [nextAddrEq, nextFrame] using nextMemory
      obtain ⟨xsFinal, currentFinal, finalMemory, finalSegment, finalHeap, finalOk, finalI, finalLen,
        finalRefs, finalAccounting, finalPa⟩ :=
        ih (fuel - 1) xsMid tail1 cleared clearedFinal pa1 midPa memory1 midMemory i1 nextFrame domain curr c1
          nextAddr old currentMid refs clearRun stateOk rfl rfl tailFuel
          (by simpa [cleared, heapLen] using limitEq) (by simpa [cleared, heapLen] using heapBound)
          ordered (by simpa [cleared, heapLen] using refBound) (by simpa [cleared] using segmentMid)
          (by simpa [cleared] using tailBound) tailRefs refClass (by simpa [cleared, heapLen] using byteBound)
          recursiveMemory recursiveWord xsLen.symm good tailCount
      have rebuilt := (congrFun (partialRefScan_reassemble conf currentFinal middle.h2 left tail1 roots1 len tag payload
        (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) pa midPa pa1 k xsFinal frame paEq) _).mp
        (by simpa only [clearedFinal, nextAddrEq, nextFrame] using finalMemory)
      refine ⟨xsFinal, currentFinal, ?_, ?_, ?_, finalOk, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [leftEq] using rebuilt
      · simpa only [clearedFinal] using finalSegment
      · simpa only [clearedFinal, cleared, heapLen] using finalHeap
      · simpa only [clearedFinal] using finalI
      · simpa only [clearedFinal] using finalLen
      · intro element member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact mutable
        · exact finalRefs element member
      · simp only [clearedFinal, cleared] at finalAccounting
        simp only [leftEq, rightEq, heapLength_append]
        omega
      · simp only [clearedFinal] at finalPa
        rw [leftEq, heapLength_append, finalPa, paEq]
        simp only [BitVec.ofNat_add, BitVec.mul_add]
        ac_rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

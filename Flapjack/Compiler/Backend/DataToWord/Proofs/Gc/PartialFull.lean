import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialRefs
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalFull

/-! Partial generational collector simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private instance {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩
private instance {α : Type} : Std.Commutative (SetSep.star (α := α)) := ⟨SetSep.starComm⟩

/-- A heap ends in mutable references at the stated boundary. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "ends_with_refs_def"]
def endsWithRefs {α β : Type} (boundary : Nat) (heap : List (HeapElement α (HeapTag × β))) : Prop :=
  ∃ before after, heapSplit boundary heap = some (before, after) ∧ ∀ element ∈ after, isRef element

/-- The final segment of a three-way split contains only references when the
original heap ends with references at the same boundary. -/
theorem partialFull_segmentRefs {α β : Type} (heap : List (HeapElement α (HeapTag × β)))
    (a b : Nat) (old current refs : List (HeapElement α (HeapTag × β)))
    (segment : heapSegment (a, b) heap = some (old, current, refs)) (ending : endsWithRefs b heap) :
    ∀ element ∈ refs, isRef element := by
  obtain ⟨whole, _, endLen, _⟩ := heapSegment_imp heap a b old current refs segment
  obtain ⟨before, after, split, allRefs⟩ := ending
  have canonical : heapSplit b heap = some (old ++ current, refs) := by
    rw [← whole, ← endLen]
    exact heapSplit_append (old ++ current) refs
  rw [canonical] at split
  simp only [Option.some.injEq, Prod.mk.injEq] at split
  obtain ⟨_, rfl⟩ := split
  exact allRefs

/-- Split the original heap around the collected generation and retain the
old and reference regions as a frame for root traversal. -/
theorem partialFull_rootFrame {width : Nat} [NeZero width] (conf : Config)
    (old current refs : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr new : BitVec width) (xs : List (WordLocW width))
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) :
    SetSep.star (SetSep.star (wordHeap curr (old ++ current ++ refs) conf) (Misc.wordList new xs)) frame =
      SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
        (Misc.wordList new xs))
        (SetSep.star (SetSep.star (wordHeap curr old conf)
          (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength (old ++ current))) refs conf)) frame) := by
  rw [wordHeapAppend (old ++ current) refs curr conf, wordHeapAppend old current curr conf]
  simp only [wordSemBytesInWord, StackRemove.bytesInWord]
  ac_rfl

/-- Scanning references leaves their reference classification unchanged. -/
theorem partialRefScan_preservesClassification {α β γ : Type} (conf : GenGcPartial.Config γ)
    (classify : β → Bool) (refs output : List (HeapElement α β)) (state result : GcState α γ)
    (run : GenGcPartial.gcMoveRefList conf state refs = (output, result)) :
    output.all (isRefElement classify) = refs.all (isRefElement classify) := by
  induction refs generalizing output state result with
  | nil => simp [GenGcPartial.gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨rfl, _⟩ := run; rfl
  | cons head tail ih =>
    cases head with
    | unused len => simp [GenGcPartial.gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨rfl, _⟩ := run; rfl
    | forwardPointer ptr value len => simp [GenGcPartial.gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨rfl, _⟩ := run; rfl
    | dataElement roots len payload =>
      simp only [GenGcPartial.gcMoveRefList] at run
      generalize headRun : GenGcPartial.gcMoveList conf state roots = headResult at run
      obtain ⟨roots1, middle⟩ := headResult
      generalize tailRun : GenGcPartial.gcMoveRefList conf middle tail = tailResult at run
      obtain ⟨tail1, final⟩ := tailResult
      simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, _⟩ := run
      simp only [List.all_cons, isRefElement]
      rw [ih tail1 middle final tailRun]

/-- Reference traversal preserves the collector's reference classification. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "partial_gc_move_ref_list_isRef"]
theorem partialGcMoveRefList_isRef {α β : Type} (conf : GenGcPartial.Config β)
    (refs output : List (HeapElement α β)) (state result : GcState α β)
    (run : GenGcPartial.gcMoveRefList conf state refs = (output, result)) :
    output.all (isRefElement conf.isRef) = refs.all (isRefElement conf.isRef) :=
  partialRefScan_preservesClassification conf conf.isRef refs output state result run

/-- Reference traversal leaves the scanned prefix, generation partitions,
and old region unchanged. This is local collector proof infrastructure. -/
theorem partialFull_refListFixed {α β γ : Type} (conf : GenGcPartial.Config γ)
    (refs output : List (HeapElement α β)) (state result : GcState α γ)
    (run : GenGcPartial.gcMoveRefList conf state refs = (output, result)) :
    result.h1 = state.h1 ∧ result.r4 = state.r4 ∧ result.r3 = state.r3 ∧
      result.r2 = state.r2 ∧ result.r1 = state.r1 ∧ result.old = state.old := by
  induction refs generalizing output state result with
  | nil => simp [GenGcPartial.gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons head tail ih =>
    cases head with
    | unused len => simp [GenGcPartial.gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    | forwardPointer ptr value len => simp [GenGcPartial.gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    | dataElement roots len payload =>
      simp only [GenGcPartial.gcMoveRefList] at run
      generalize headRun : GenGcPartial.gcMoveList conf state roots = headResult at run
      obtain ⟨roots1, middle⟩ := headResult
      generalize tailRun : GenGcPartial.gcMoveRefList conf middle tail = tailResult at run
      obtain ⟨tail1, final⟩ := tailResult
      simp only [Prod.mk.injEq] at run
      obtain ⟨_, rfl⟩ := run
      obtain ⟨h1, r4, r3, r2, r1, old⟩ := partialMoveList_fixedFields conf roots roots1 state middle headRun
      obtain ⟨h1', r4', r3', r2', r1', old'⟩ := ih tail1 middle final tailRun
      exact ⟨h1'.trans h1, r4'.trans r4, r3'.trans r3, r2'.trans r2, r1'.trans r1, old'.trans old⟩

/-- A partial copied-data scan preserves the non-data partitions and the
underlying heap's total length. -/
theorem partialFull_dataFixed {α β : Type} (conf : GenGcPartial.Config β) (state : GcState α β) :
    let final := GenGcPartial.gcMoveData conf state
    final.r4 = state.r4 ∧ final.r3 = state.r3 ∧ final.r2 = state.r2 ∧ final.r1 = state.r1 ∧
      final.old = state.old ∧ heapLength final.heap = heapLength state.heap := by
  classical
  induction state using GenGcPartial.gcMoveData.induct conf with
  | case1 state empty =>
    rw [GenGcPartial.gcMoveData]
    simp [empty]
  | case2 state head tail heap over =>
    rw [GenGcPartial.gcMoveData]
    simp [heap, over]
  | case3 state tail roots len payload roots1 middle move heap bounded flag ih =>
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n status origHeap heap0 =>
      simp only at heap
      subst h2
      rw [GenGcPartial.gcMoveData]
      simp only [bounded, ↓reduceIte, move]
      obtain ⟨_, r4Eq, r3Eq, r2Eq, r1Eq, oldEq⟩ :=
        partialMoveList_fixedFields conf roots roots1 _ middle move
      have heapEq := GenGcPartial.gcMoveList_heapLength roots roots1 conf _ middle move
      dsimp only [flag] at ih
      obtain ⟨r4', r3', r2', r1', old', heap'⟩ := ih
      exact ⟨r4'.trans r4Eq, r3'.trans r3Eq, r2'.trans r2Eq, r1'.trans r1Eq,
        old'.trans oldEq, heap'.trans heapEq.symm⟩
  | case4 state head tail heap bounded notData =>
    cases head with
    | unused len => rw [GenGcPartial.gcMoveData]; simp [heap, bounded]
    | forwardPointer ptr value len => rw [GenGcPartial.gcMoveData]; simp [heap, bounded]
    | dataElement roots len payload => exact False.elim (notData roots len payload rfl)

/-- A successful partial collection consists of a valid heap segment,
successful root and reference traversals, and the final copied-data scan. -/
theorem partialFull_abstractSteps {α β : Type} (conf : GenGcPartial.Config β)
    (roots roots1 : List (HeapAddress α)) (heap : List (HeapElement α β)) (result : GcState α β)
    (run : GenGcPartial.partialGc conf (roots, heap) = (roots1, result)) (ok : result.ok = true) :
    ∃ old current refs middle refs1 afterRefs,
      heapSegment (conf.genStart, conf.refsStart) heap = some (old, current, refs) ∧
      GenGcPartial.gcMoveList conf
        { emptyGcState with heap := heap, old := old, r2 := refs, a := conf.genStart, n := heapLength current }
        roots = (roots1, middle) ∧ middle.ok = true ∧
      GenGcPartial.gcMoveRefList conf middle refs = (refs1, afterRefs) ∧ afterRefs.ok = true ∧
      GenGcPartial.gcMoveData conf { afterRefs with r1 := refs1, r2 := [] } = result := by
  classical
  rw [GenGcPartial.partialGc] at run
  cases segment : heapSegment (conf.genStart, conf.refsStart) heap with
  | none =>
    simp only [segment, Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    simp at ok
  | some parts =>
    obtain ⟨old, current, refs⟩ := parts
    simp only [segment] at run
    generalize rootsRun : GenGcPartial.gcMoveList conf
      { emptyGcState with heap := heap, old := old, r2 := refs, a := conf.genStart, n := heapLength current }
      roots = rootsResult at run
    obtain ⟨moved, middle⟩ := rootsResult
    generalize refsRun : GenGcPartial.gcMoveRefList conf middle refs = refsResult at run
    obtain ⟨refs1, afterRefs⟩ := refsResult
    simp only [Prod.mk.injEq] at run
    obtain ⟨rfl, dataRun⟩ := run
    have afterOk : afterRefs.ok = true := by
      have before := partialMoveData_okBefore conf { afterRefs with r1 := refs1, r2 := [] } result dataRun ok
      exact before
    have middleOk := partialMoveRefList_okBefore conf refs middle refs1 afterRefs refsRun afterOk
    exact ⟨old, current, refs, middle, refs1, afterRefs, rfl, rootsRun, middleOk, refsRun, afterOk, dataRun⟩

/-- Connect the original whole-heap assertion to the partial collector's
verified root traversal and retain the remaining heap regions as its frame. -/
theorem partialFull_rootPhase {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap old current refs : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (middle : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (curr new i1 pa1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (w : List (WordLocW width)) (c1 : Bool)
    (segment : heapSegment (genConf.genStart, genConf.refsStart) heap = some (old, current, refs))
    (run : GenGcPartial.gcMoveList genConf
      { emptyGcState with heap := heap, old := old, r2 := refs, a := genConf.genStart, n := heapLength current }
      roots = (roots1, middle)) (ok : middle.ok = true)
    (limitEq : genConf.limit = heapLength heap)
    (heapBound : heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (ordered : genConf.genStart ≤ genConf.refsStart) (refBound : genConf.refsStart ≤ heapLength heap)
    (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (byteBound : heapLength heap * (width / 8) < 2 ^ width)
    (separated : SetSep.star (SetSep.star (wordHeap curr heap conf) (Misc.wordList new xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (wordRun : wordGenGcPartialMoveRoots conf
      (roots.map (wordAddr conf), BitVec.ofNat width genConf.genStart, new, curr, memory, domain,
       wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
       wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) = (w, i1, pa1, memory1, c1))
    (length : xs.length = genConf.refsStart - genConf.genStart) (good : goodDimindex width) :
    ∃ xs1 current1,
      SetSep.star (SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current1 conf)
        (wordHeap new middle.h2 conf)) (Misc.wordList pa1 xs1))
        (SetSep.star (SetSep.star (wordHeap curr old conf)
          (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) refs conf)) frame)
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      w = roots1.map (wordAddr conf) ∧ heapLength middle.heap = heapLength heap ∧
      heapSegment (genConf.genStart, genConf.refsStart) middle.heap = some (old, current1, refs) ∧
      c1 = true ∧ i1 = BitVec.ofNat width middle.a ∧ middle.n = xs1.length ∧
      heapLength current = heapLength middle.h2 + middle.n + heapLength middle.r4 ∧
      pa1 = new + wordSemBytesInWord * BitVec.ofNat width (heapLength middle.h2) := by
  obtain ⟨whole, oldLen, endLen, _⟩ := heapSegment_imp heap _ _ old current refs segment
  have currentLen : heapLength current = genConf.refsStart - genConf.genStart := by
    rw [heapLength_append, oldLen] at endLen
    omega
  have sepRoot : SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (Misc.wordList new xs))
      (SetSep.star (SetSep.star (wordHeap curr old conf)
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) refs conf)) frame)
      (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    rw [← whole, partialFull_rootFrame, endLen] at separated
    exact separated
  let initial : GcState (WordLocW width) (HeapTag × List (WordLocW width)) :=
    { emptyGcState with heap := heap, old := old, r2 := refs, a := genConf.genStart, n := heapLength current }
  obtain ⟨xs1, current1, memoryResult, rootEq, heapEq, segment1, flag, indexEq, xsLen, accounting, paEq⟩ :=
    wordGenGcPartialMoveRoots_thm conf genConf initial middle roots roots1 old current refs curr new i1 pa1 xs
      memory memory1 domain _ w c1 run ok rfl rfl limitEq heapBound ordered refBound segment refClass byteBound
      sepRoot wordRun (by simpa [initial, currentLen] using length) good
  exact ⟨xs1, current1, memoryResult, rootEq, heapEq, segment1, flag, indexEq, xsLen, accounting, paEq⟩

/-- The root phase's framed heap exposes the source reference suffix for the
verified reference-list simulation. -/
theorem partialFull_referenceFrame {width : Nat} [NeZero width] (conf : Config)
    (old current copied refs : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr new pa k : BitVec width) (xs : List (WordLocW width))
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) :
    SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (wordHeap new copied conf)) (Misc.wordList pa xs))
      (SetSep.star (SetSep.star (wordHeap curr old conf) (wordHeap k refs conf)) frame) =
    SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (Misc.wordList pa xs)) (wordHeap k refs conf))
      (SetSep.star (SetSep.star (wordHeap curr old conf) (wordHeap new copied conf)) frame) := by
  ac_rfl

/-- Reassemble the copied data and remembered reference regions after the
reference phase, ready for the partial data scan. -/
theorem partialFull_dataFrame {width : Nat} [NeZero width] (conf : Config)
    (old current copied appended refs : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr new pa pa1 k : BitVec width) (xs : List (WordLocW width))
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (paEq : pa = new + wordSemBytesInWord * BitVec.ofNat width (heapLength copied)) :
    SetSep.star (SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (wordHeap pa appended conf)) (Misc.wordList pa1 xs)) (wordHeap k refs conf))
      (SetSep.star (SetSep.star (wordHeap curr old conf) (wordHeap new copied conf)) frame) =
    SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (wordHeap new (copied ++ appended) conf)) (Misc.wordList pa1 xs))
      (SetSep.star (SetSep.star (wordHeap curr old conf) (wordHeap k refs conf)) frame) := by
  change pa = new + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength copied) at paEq
  rw [wordHeapAppend copied appended new conf, ← paEq]
  ac_rfl

/-- Run the remembered-reference phase after the root phase and combine the
copied-data regions for the subsequent scan. -/
theorem partialFull_referencePhase {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (middle afterRefs : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (old current refs refs1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr new pa pa1 i1 k : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (c1 : Bool)
    (run : GenGcPartial.gcMoveRefList genConf middle refs = (refs1, afterRefs)) (ok : afterRefs.ok = true)
    (limitEq : genConf.limit = heapLength middle.heap)
    (heapBound : heapLength middle.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (ordered : genConf.genStart ≤ genConf.refsStart) (refBound : genConf.refsStart ≤ heapLength middle.heap)
    (segment : heapSegment (genConf.genStart, genConf.refsStart) middle.heap = some (old, current, refs))
    (refsBound : heapLength refs ≤ heapLength middle.heap) (refsFuel : heapLength refs ≤ 2 ^ width)
    (refsCount : refs.length < 2 ^ width) (allRefs : ∀ element ∈ refs, isRef element)
    (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (byteBound : heapLength middle.heap * (width / 8) < 2 ^ width)
    (separated : SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (wordHeap new middle.h2 conf)) (Misc.wordList pa xs))
      (SetSep.star (SetSep.star (wordHeap curr old conf) (wordHeap k refs conf)) frame)
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (wordRun : wordGenGcPartialMoveRefList (2 ^ width) conf
      (k, BitVec.ofNat width middle.a, pa, curr, memory, domain, true,
       wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
       wordSemBytesInWord * BitVec.ofNat width genConf.refsStart,
       k + wordSemBytesInWord * BitVec.ofNat width (heapLength refs)) = (i1, pa1, memory1, c1))
    (length : xs.length = middle.n) (good : goodDimindex width)
    (paEq : pa = new + wordSemBytesInWord * BitVec.ofNat width (heapLength middle.h2)) :
    ∃ left right xs1 current1,
      afterRefs.h2 = middle.h2 ++ left ∧ afterRefs.r4 = right ++ middle.r4 ∧
      SetSep.star (SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current1 conf)
        (wordHeap new afterRefs.h2 conf)) (Misc.wordList pa1 xs1))
        (SetSep.star (SetSep.star (wordHeap curr old conf) (wordHeap k refs1 conf)) frame)
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      heapSegment (genConf.genStart, genConf.refsStart) afterRefs.heap = some (old, current1, refs) ∧
      heapLength afterRefs.heap = heapLength middle.heap ∧ c1 = true ∧ i1 = BitVec.ofNat width afterRefs.a ∧
      afterRefs.n = xs1.length ∧ (∀ element ∈ refs1, isRef element) ∧
      middle.n = heapLength left + afterRefs.n + heapLength right ∧
      pa1 = pa + wordSemBytesInWord * BitVec.ofNat width (heapLength left) := by
  obtain ⟨left, right, leftEq, rightEq, clearRun⟩ :=
    partialMoveRefList_withNilLemma genConf refs middle refs1 afterRefs run ok
  let cleared := { middle with h2 := [], r4 := [] }
  let clearedFinal := { afterRefs with h2 := left, r4 := right }
  let nextFrame := SetSep.star (SetSep.star (wordHeap curr old conf) (wordHeap new middle.h2 conf)) frame
  have inputMemory : SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (Misc.wordList pa xs)) (wordHeap k refs conf)) nextFrame
      (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    rw [partialFull_referenceFrame] at separated
    exact separated
  obtain ⟨xs1, current1, memoryResult, segment1, heapLen, success, indexEq, xsLen, outputRefs, accounting, finalPa⟩ :=
    wordGenGcPartialMoveRefList_thm conf genConf refs (2 ^ width) xs refs1 cleared clearedFinal pa1 pa memory1 memory i1
      nextFrame domain curr c1 k old current refs clearRun ok rfl rfl refsFuel limitEq heapBound ordered refBound segment
      refsBound allRefs refClass byteBound inputMemory wordRun length good refsCount
  have reconstructed := (congrFun (partialFull_dataFrame conf old current1 middle.h2 left refs1 curr new pa pa1 k xs1 frame paEq) _).mp memoryResult
  refine ⟨left, right, xs1, current1, leftEq, rightEq, ?_, segment1, heapLen, success, indexEq, xsLen,
    outputRefs, accounting, finalPa⟩
  simpa only [leftEq] using reconstructed

/-- Establish the copied-data scan invariant from the source heap partition,
reference-size preservation, and the two allocation accounting equations. -/
theorem partialFull_dataInvariant {α β : Type} (state : GcState α β)
    (old current refs refs1 : List (HeapElement α β))
    (segment : heapSegment (heapLength old, heapLength (old ++ current)) state.heap = some (old, current, refs))
    (h1Empty : state.h1 = []) (r4Empty : state.r4 = []) (r3Empty : state.r3 = [])
    (oldEq : state.old = old) (refsLen : heapLength refs1 = heapLength refs)
    (accounting : heapLength current = heapLength state.h2 + state.n) :
    partialLenInv { state with r1 := refs1, r2 := [] } := by
  obtain ⟨whole, _, _, _⟩ := heapSegment_imp state.heap _ _ old current refs segment
  simp only [partialLenInv, h1Empty, r4Empty, r3Empty, oldEq, List.nil_append, List.append_nil]
  rw [← whole]
  simp only [heapLength_append, refsLen]
  omega

/-- Restore the original-generation heap around the updated reference region
after scanning the copied data. -/
theorem partialFull_finalFrame {width : Nat} [NeZero width] (conf : Config)
    (old current refs copied : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr new k pa : BitVec width) (xs : List (WordLocW width))
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (kEq : k = curr + wordSemBytesInWord * BitVec.ofNat width (heapLength (old ++ current))) :
    SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (wordHeap new copied conf)) (Misc.wordList pa xs))
      (SetSep.star (SetSep.star (wordHeap curr old conf) (wordHeap k refs conf)) frame) =
    SetSep.star (SetSep.star (SetSep.star (wordHeap curr (old ++ current ++ refs) conf)
      (wordHeap new copied conf)) (Misc.wordList pa xs)) frame := by
  change k = curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength (old ++ current)) at kEq
  rw [wordHeapAppend (old ++ current) refs curr conf, wordHeapAppend old current curr conf, ← kEq]
  simp only [wordSemBytesInWord, StackRemove.bytesInWord]
  ac_rfl

/-- At the end of the data scan, the copied region and remaining free space
exactly fill the collected generation. -/
theorem partialFull_outputBounds {α β : Type} (state : GcState α β)
    (old current refs : List (HeapElement α β)) (start finish : Nat)
    (segment : heapSegment (start, finish) state.heap = some (old, current, refs))
    (h2Empty : state.h2 = []) (r4Empty : state.r4 = []) (r3Empty : state.r3 = []) (r2Empty : state.r2 = [])
    (oldEq : state.old = old) (refsLen : heapLength state.r1 = heapLength refs)
    (invariant : partialLenInv state) :
    heapLength state.h1 ≤ heapLength current ∧
      heapLength state.h1 + state.n + start = finish := by
  obtain ⟨whole, oldLen, endLen, _⟩ := heapSegment_imp state.heap start finish old current refs segment
  unfold partialLenInv at invariant
  rw [← whole] at invariant
  simp only [h2Empty, r4Empty, r3Empty, r2Empty, oldEq, List.nil_append, List.append_nil,
    heapLength_append, refsLen] at invariant
  simp only [heapLength_append] at endLen
  omega

/-- The generic reference classifier agrees with mutable-tag recognition. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "EVERY_is_Ref_isRef"]
theorem everyIsRefElement_iff {α β : Type} (classify : HeapTag × β → Bool)
    (refs : List (HeapElement α (HeapTag × β)))
    (classEq : ∀ t r, classify (t, r) = true ↔ isMutTag t) :
    refs.all (isRefElement classify) = true ↔ ∀ element ∈ refs, isRef element := by
  rw [List.all_eq_true]
  constructor
  · intro h element member
    have test := h element member
    cases element with
    | unused len => simp [isRefElement] at test
    | forwardPointer ptr value len => simp [isRefElement] at test
    | dataElement roots len payload =>
      rcases payload with ⟨tag, payload⟩
      exact (classEq tag payload).mp test
  · intro h element member
    have test := h element member
    cases element with
    | unused len => simp [isRef] at test
    | forwardPointer ptr value len => simp [isRef] at test
    | dataElement roots len payload =>
      rcases payload with ⟨tag, payload⟩
      exact (classEq tag payload).mpr test

/-- Partial generational collector simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_partial_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartial_thm {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (curr new pa1 i1 : BitVec width) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (roots1' : List (WordLocW width)) (c1 : Bool)
    (abstractRun : GenGcPartial.partialGc genConf (roots, heap) = (roots1, state1)) (stateOk : state1.ok = true)
    (heapBound : heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (byteBound : heapLength heap * (width / 8) < 2 ^ width)
    (limitEq : genConf.limit = heapLength heap)
    (ordered : genConf.genStart ≤ genConf.refsStart) (refBound : genConf.refsStart ≤ heapLength heap)
    (ending : endsWithRefs genConf.refsStart heap)
    (_byteBoundAgain : heapLength heap * (width / 8) < 2 ^ width)
    (dataBound : conf.lenSize + 2 < width)
    (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (wordRun : wordGenGcPartial conf (roots.map (wordAddr conf), curr, new,
      wordSemBytesInWord * BitVec.ofNat width (heapLength heap), memory, domain,
      wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
      wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) = (roots1', i1, pa1, memory1, c1))
    (separated : SetSep.star (SetSep.star (wordHeap curr heap conf)
      (Misc.wordListExists new (genConf.refsStart - genConf.genStart))) frame
      (SetSep.fun2Set (memory, fun address => domain address = true))) (good : goodDimindex width) :
    ∃ xs1 current1 refs1,
      SetSep.star (SetSep.star (SetSep.star (wordHeap curr (state1.old ++ current1 ++ state1.r1) conf)
        (wordHeap new state1.h1 conf))
        (Misc.wordList (new + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h1)) xs1)) frame
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      state1.h2 = [] ∧ state1.r4 = [] ∧ state1.r3 = [] ∧ state1.r2 = [] ∧
      roots1' = roots1.map (wordAddr conf) ∧ heapLength state1.heap = heapLength heap ∧
      heapSegment (genConf.genStart, genConf.refsStart) state1.heap = some (state1.old, current1, refs1) ∧
      c1 = true ∧ i1 = BitVec.ofNat width state1.a ∧
      pa1 = new + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h1) ∧
      state1.n = xs1.length ∧ partialLenInv state1 ∧ heapLength state1.h1 ≤ heapLength current1 ∧
      heapLength state1.h1 + xs1.length + genConf.genStart = genConf.refsStart ∧
      state1.r1.all (isRefElement genConf.isRef) = true := by
  classical
  obtain ⟨old, current, refs, middle, refs1, afterRefs, segment, rootsRun, middleOk, refsRun, afterOk, dataRun⟩ :=
    partialFull_abstractSteps genConf roots roots1 heap state1 abstractRun stateOk
  obtain ⟨whole, oldLen, endLen, refsLen⟩ := heapSegment_imp heap _ _ old current refs segment
  have allRefs := partialFull_segmentRefs heap _ _ old current refs segment ending
  obtain ⟨xs, xsLen, sep⟩ : ∃ xs : List (WordLocW width), xs.length = genConf.refsStart - genConf.genStart ∧
      SetSep.star (SetSep.star (wordHeap curr heap conf) (Misc.wordList new xs)) frame
        (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    obtain ⟨left, right, split, ⟨a, b, split', ha, hb⟩, hf⟩ := separated
    obtain ⟨xs, hx, hn⟩ := (show ∃ xs : List (WordLocW width), Misc.wordList new xs b ∧
        xs.length = genConf.refsStart - genConf.genStart by
      simpa only [Misc.wordListExists, SetSep.sepExists, StackRemove.WordListExists.starCond] using hb)
    exact ⟨xs, hn, left, right, split, ⟨a, b, split', ha, hx⟩, hf⟩
  have startByteBound : genConf.genStart * (width / 8) < 2 ^ width :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (le_trans ordered refBound)) byteBound
  have decoded := (genFull_decodeLength genConf.genStart good startByteBound).1
  simp only [wordGenGcPartial, decoded] at wordRun
  generalize rootWord : wordGenGcPartialMoveRoots conf
    (roots.map (wordAddr conf), BitVec.ofNat width genConf.genStart, new, curr, memory, domain,
      wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
      wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) = rootResult at wordRun
  obtain ⟨rootsW, iMid, paMid, memoryMid, flagMid⟩ := rootResult
  generalize refsWord : wordGenGcPartialMoveRefList (2 ^ width) conf
    (curr + wordSemBytesInWord * BitVec.ofNat width genConf.refsStart, iMid, paMid, curr, memoryMid, domain, flagMid,
      wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
      wordSemBytesInWord * BitVec.ofNat width genConf.refsStart,
      curr + wordSemBytesInWord * BitVec.ofNat width (heapLength heap)) = refsResult at wordRun
  obtain ⟨iRefs, paRefs, memoryRefs, flagRefs⟩ := refsResult
  generalize dataWord : wordGenGcPartialMoveData conf (2 ^ width)
    (new, iRefs, paRefs, curr, memoryRefs, domain,
      wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
      wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) = dataResult at wordRun
  obtain ⟨iFinal, paFinal, memoryFinal, flagFinal⟩ := dataResult
  simp only [Prod.mk.injEq] at wordRun
  obtain ⟨rfl, rfl, rfl, rfl, flags⟩ := wordRun
  obtain ⟨xsMid, currentMid, sepMid, rootsEq, heapMid, segmentMid, flagMidTrue, iMidEq, xsMidLen,
    rootAccounting, paMidEq⟩ :=
    partialFull_rootPhase conf genConf roots roots1 heap old current refs middle curr new iMid paMid xs memory memoryMid
      domain frame rootsW flagMid segment rootsRun middleOk limitEq heapBound ordered refBound refClass byteBound
      sep rootWord xsLen good
  subst flagMid
  let initial : GcState (WordLocW width) (HeapTag × List (WordLocW width)) :=
    { emptyGcState with heap := heap, old := old, r2 := refs, a := genConf.genStart, n := heapLength current }
  obtain ⟨midH1, midR4, midR3, midR2, midR1, midOld⟩ :=
    partialMoveList_fixedFields genConf roots roots1 initial middle rootsRun
  simp only [initial, emptyGcState] at midH1 midR4 midR3 midR2 midR1 midOld
  have heapSmall : heapLength heap < 2 ^ width := by
    rcases good with h | h <;> subst width <;> norm_num at byteBound ⊢ <;> omega
  have refsBound : heapLength refs ≤ heapLength middle.heap := by rw [heapMid, refsLen]; omega
  have refsSmall : heapLength refs < 2 ^ width := by rw [refsLen]; omega
  have refsCount : refs.length < 2 ^ width := lt_of_le_of_lt (length_le_heapLength refs) refsSmall
  have refsEnd : curr + wordSemBytesInWord * BitVec.ofNat width (heapLength heap) =
      (curr + wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) +
        wordSemBytesInWord * BitVec.ofNat width (heapLength refs) := by
    have total : genConf.refsStart + heapLength refs = heapLength heap := by rw [refsLen]; omega
    rw [← total, BitVec.ofNat_add, BitVec.mul_add]
    ac_rfl
  rw [iMidEq, refsEnd] at refsWord
  obtain ⟨left, right, xsRefs, currentRefs, leftEq, rightEq, sepRefs, segmentRefs, heapRefs, flagRefsTrue,
    iRefsEq, xsRefsLen, newRefs, refAccounting, paRefsEq⟩ :=
    partialFull_referencePhase conf genConf middle afterRefs old currentMid refs refs1 curr new paMid paRefs iRefs
      (curr + wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) xsMid memoryMid memoryRefs domain frame flagRefs
      refsRun afterOk (by simpa [heapMid] using limitEq) (by simpa [heapMid] using heapBound) ordered
      (by simpa [heapMid] using refBound) segmentMid refsBound (Nat.le_of_lt refsSmall) refsCount allRefs refClass
      (by simpa [heapMid] using byteBound) sepMid refsWord xsMidLen.symm good paMidEq
  subst flagRefs
  obtain ⟨afterH1, afterR4, afterR3, afterR2, afterR1, afterOld⟩ :=
    partialFull_refListFixed genConf refs refs1 middle afterRefs refsRun
  rw [midH1] at afterH1
  rw [midR4] at afterR4
  rw [midR3] at afterR3
  rw [midR2] at afterR2
  rw [midR1] at afterR1
  rw [midOld] at afterOld
  have rightEmpty : right = [] := by simpa [midR4, afterR4] using rightEq.symm
  have spaceEq : heapLength current = heapLength afterRefs.h2 + afterRefs.n := by
    have nilLen : heapLength ([] : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) = 0 := rfl
    simp only [midR4, rightEmpty, nilLen] at rootAccounting refAccounting
    rw [leftEq, heapLength_append]
    omega
  obtain ⟨_, _, endRefs, _⟩ := heapSegment_imp afterRefs.heap _ _ old currentRefs refs segmentRefs
  have currentSize : heapLength currentRefs = heapLength current := by
    simp only [heapLength_append, oldLen] at endRefs endLen
    omega
  have refsOutputLen : heapLength refs1 = heapLength refs :=
    (partialRefScan_abstractProperties genConf refs refs1 middle afterRefs refsRun allRefs).2.1
  have normalizedSegment : heapSegment (heapLength old, heapLength (old ++ currentRefs)) afterRefs.heap =
      some (old, currentRefs, refs) := by simpa [oldLen, endRefs] using segmentRefs
  have dataInv : partialLenInv { afterRefs with r1 := refs1, r2 := [] } :=
    partialFull_dataInvariant afterRefs old currentRefs refs refs1 normalizedSegment afterH1 afterR4 afterR3 afterOld
      refsOutputLen (by simpa [currentSize] using spaceEq)
  have dataFuel : heapLength afterRefs.h2 + afterRefs.n ≤ 2 ^ width := by
    rw [← spaceEq]
    have : heapLength current ≤ heapLength heap := by
      rw [← whole, heapLength_append, heapLength_append]
      omega
    omega
  have paStart : paRefs = new + wordSemBytesInWord * BitVec.ofNat width (heapLength afterRefs.h2) := by
    rw [paRefsEq, paMidEq, leftEq, heapLength_append, BitVec.ofNat_add, BitVec.mul_add]
    ac_rfl
  let scanState := { afterRefs with r1 := refs1, r2 := [] }
  let scanFrame := SetSep.star (SetSep.star (wordHeap curr old conf)
    (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) refs1 conf)) frame
  have scanMemory : SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) currentRefs conf)
      (wordHeap new (scanState.h1 ++ scanState.h2) conf))
      (Misc.wordList (new + wordSemBytesInWord * BitVec.ofNat width (heapLength (scanState.h1 ++ scanState.h2))) xsRefs)) scanFrame
      (SetSep.fun2Set (memoryRefs, fun address => domain address = true)) := by
    rw [paStart] at sepRefs
    simpa [scanState, scanFrame, afterH1] using sepRefs
  have scanRefs : (scanState.r4 ++ scanState.r3 ++ scanState.r2 ++ scanState.r1).all (isRefElement genConf.isRef) = true := by
    simpa [scanState, afterR4, afterR3] using (everyIsRefElement_iff genConf.isRef refs1 refClass).mpr newRefs
  rw [iRefsEq, paStart] at dataWord
  have scanWord : wordGenGcPartialMoveData conf (2 ^ width)
      (new + wordSemBytesInWord * BitVec.ofNat width (heapLength scanState.h1), BitVec.ofNat width scanState.a,
       new + wordSemBytesInWord * BitVec.ofNat width (heapLength (scanState.h1 ++ scanState.h2)),
       curr, memoryRefs, domain, wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
       wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) = (iFinal, paFinal, memoryFinal, flagFinal) := by
    simpa [scanState, afterH1, heapLength] using dataWord
  obtain ⟨xsFinal, currentFinal, finalMemory, finalH2, finalHeap, finalSegment, finalFlag, finalI, finalLen,
    finalInv, finalAccounting, finalPa, finalRefs⟩ :=
    wordGenGcPartialMoveData_thm conf genConf (2 ^ width) scanState state1 memoryRefs memoryFinal domain curr new xsRefs
      paFinal iFinal old currentRefs refs scanFrame flagFinal dataRun stateOk (by simpa [scanState, heapRefs, heapMid] using limitEq)
      (by simpa [scanState, heapRefs, heapMid] using heapBound) (by simpa [scanState, heapRefs, heapMid] using byteBound)
      ordered (by simpa [scanState, heapRefs, heapMid] using refBound) (by simpa [scanState] using segmentRefs)
      dataBound refClass scanWord (by simpa [scanState] using dataFuel) dataInv scanMemory scanRefs xsRefsLen.symm good
  have fixed := partialFull_dataFixed genConf scanState
  rw [dataRun] at fixed
  obtain ⟨finalR4, finalR3, finalR2, finalR1, finalOld, _⟩ := fixed
  have r4Empty : state1.r4 = [] := by simpa [scanState, afterR4] using finalR4
  have r3Empty : state1.r3 = [] := by simpa [scanState, afterR3] using finalR3
  have r2Empty : state1.r2 = [] := by simpa [scanState] using finalR2
  have r1Eq : state1.r1 = refs1 := by simpa [scanState] using finalR1
  have oldEq : state1.old = old := by simpa [scanState, afterOld] using finalOld
  have finalRefsLen : heapLength state1.r1 = heapLength refs := by rw [r1Eq, refsOutputLen]
  obtain ⟨_, _, endFinal, _⟩ := heapSegment_imp state1.heap _ _ old currentFinal refs finalSegment
  have finalKEq : curr + wordSemBytesInWord * BitVec.ofNat width genConf.refsStart =
      curr + wordSemBytesInWord * BitVec.ofNat width (heapLength (old ++ currentFinal)) := by rw [endFinal]
  have reconstructed := (congrFun (partialFull_finalFrame conf old currentFinal refs1 state1.h1 curr new
    (curr + wordSemBytesInWord * BitVec.ofNat width genConf.refsStart)
    (new + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h1)) xsFinal frame finalKEq) _).mp
    (by simpa [scanFrame, finalH2] using finalMemory)
  obtain ⟨copiedBound, totalEq⟩ := partialFull_outputBounds state1 old currentFinal refs genConf.genStart
    genConf.refsStart finalSegment finalH2 r4Empty r3Empty r2Empty oldEq finalRefsLen finalInv
  refine ⟨xsFinal, currentFinal, refs, ?_, finalH2, r4Empty, r3Empty, r2Empty, rootsEq, ?_, ?_, ?_, finalI, ?_,
    finalLen, finalInv, copiedBound, ?_, ?_⟩
  · simpa only [oldEq, r1Eq] using reconstructed
  · simpa [scanState, heapRefs, heapMid] using finalHeap
  · simpa only [oldEq] using finalSegment
  · simpa [finalFlag] using flags.symm
  · simpa [finalH2] using finalPa
  · simpa [← finalLen] using totalEq
  · simpa [r1Eq] using (everyIsRefElement_iff genConf.isRef refs1 refClass).mpr newRefs

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

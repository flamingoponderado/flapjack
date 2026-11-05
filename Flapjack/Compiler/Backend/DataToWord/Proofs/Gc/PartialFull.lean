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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

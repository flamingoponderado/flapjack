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

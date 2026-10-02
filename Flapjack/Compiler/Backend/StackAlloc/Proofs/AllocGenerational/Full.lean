import Flapjack.Compiler.Backend.StackAlloc.Proofs.AllocGenerational.Partial
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenGcMove
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenGcMoveRootsBitmaps
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenGcMoveLoop

/-!
# Generational allocation: full collector case

Original full-selector case of alloc_correct_lemma_Generational, 4833-5016.
The source inversions below are Flapjack infrastructure with no separately
named HOL declaration. They derive collector success and the normal/halt split
from the original non-error allocation premise. The full case below constructs actual wordGcCode execution from allocation.
-/
namespace Flapjack.Compiler.Backend.StackAlloc.AllocGenerationalFull
open Flapjack Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions

/-- Original non-error allocation obtains a collector result and either returns
it normally or halts with Word 1 after emptyEnv. No success assumption is added. -/
theorem alloc_collector_result {width : Nat} [NeZero width] {C F : Type}
    {w : BitVec width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)}
    (ha : StackSemAllocation.alloc w s = (r, t)) (hr : r ≠ some .error) :
    ∃ collected, StackSemAllocation.gc (setStore .allocSize (.word w) s) = some collected ∧
      ((r = none ∧ t = collected) ∨
       (r = some (.halt (.word 1)) ∧ t = emptyEnv collected)) := by
  obtain ⟨collected, hg⟩ := AllocGenerationalPartial.alloc_collected ha hr
  refine ⟨collected, hg, ?_⟩
  simp only [StackSemAllocation.alloc, hg] at ha
  cases hx : collected.store.lookup .allocSize with
  | none => simp only [hx, Prod.mk.injEq] at ha; exact absurd ha.1.symm hr
  | some amount =>
    simp only [hx] at ha
    cases hy : StackSemAllocation.hasSpace amount collected.store with
    | none => simp only [hy, Prod.mk.injEq] at ha; exact absurd ha.1.symm hr
    | some b =>
      cases b
      · simp only [hy, Prod.mk.injEq] at ha
        exact Or.inr ⟨ha.1.symm, ha.2.symm⟩
      · simp only [hy, Prod.mk.injEq] at ha
        exact Or.inl ⟨ha.1.symm, ha.2.symm⟩

open Classical in
/-- Source full-collector success supplies all three stage flags and the complete
ordered state update. This is an inversion, not a target-run hypothesis. -/
theorem full_collected_pipeline {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {genSizes : List Nat}
    {s collected : StackSemStateFiniteExact width C F}
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes)
    (hp : ¬wordGenGcCanDoPartial genSizes s.store)
    (hs : StackSemAllocation.gc s = some collected) :
        let curr := wordSemTheWord (holFapply s.store .currHeap)
        let other := wordSemTheWord (holFapply s.store .otherHeap)
        let newEnd := other + wordSemTheWord (holFapply s.store .heapLength)
        let len := wordSemTheWord (holFapply s.store .heapLength) >>> wordShiftAmount width
        let (w1, i1, pa1, ib1, pb1, m1, c1) :=
          wordGenGcMove conf (holFapply s.store .globals, 0, other, len, newEnd, curr, s.memory, s.mdomain)
        let (ws2, i2, pa2, ib2, pb2, m2, c2) :=
          wordGenGcMoveRootsBitmaps conf
          (s.stack.drop s.stackSpace, s.bitmaps, i1, pa1, ib1, pb1, curr, m1, s.mdomain)
        let (_i3, pa3, _ib3, pb3, m3, c3) :=
          wordGenGcMoveLoop conf len.toNat (other, i2, pa2, ib2, pb2, newEnd, curr, m2, s.mdomain)
        let a := wordSemTheWord (holFapply s.store .allocSize)
        let s1 := s.store.updateListEq
          [(.currHeap, .word other), (.otherHeap, .word curr),
           (.nextFree, .word pa3), (.genStart, .word (pa3 - other)),
           (.triggerGC, .word (pa3 + newTrig (pb3 - pa3) a genSizes)),
           (.endOfHeap, .word pb3), (.globals, w1), (.globReal, globReal conf other w1),
           (.temp 0, .word 0), (.temp 1, .word 0), (.temp 2, .word 0),
           (.temp 3, .word 0), (.temp 4, .word 0), (.temp 5, .word 0), (.temp 6, .word 0)]
        wordGcFunAssum conf s.store ∧ c1 = true ∧ c2 = true ∧ c3 = true ∧
          collected = { s with
            stack := s.stack.take s.stackSpace ++ ws2
            memory := m3
            store := s1
            regs := HolFiniteMapExact.empty } := by
  obtain ⟨hlen, ha⟩ := AllocGenerationalPartial.collected_guards hgc hk hs
  rw [Generational.gc_full hgc hk (Nat.not_lt_of_ge hlen) ha hp] at hs
  simp only [Generational.gcExpanded, Nat.not_lt_of_ge hlen, if_false, ha,
    not_true_eq_false, hp] at hs
  dsimp only at hs ⊢
  split at hs
  · have hf := ‹True ∧ _›
    exact ⟨ha, hf.2.1, hf.2.2.1, hf.2.2.2, (Option.some.inj hs).symm⟩
  · contradiction

/-- Concrete successful source equations used by the original full target
move/roots/loop code theorems; all success flags come from collection. -/
theorem full_source_pipeline {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {genSizes : List Nat}
    {s collected : StackSemStateFiniteExact width C F}
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes)
    (hp : ¬wordGenGcCanDoPartial genSizes s.store)
    (hs : StackSemAllocation.gc s = some collected) :
    let curr := wordSemTheWord (holFapply s.store .currHeap)
    let other := wordSemTheWord (holFapply s.store .otherHeap)
    let newEnd := other + wordSemTheWord (holFapply s.store .heapLength)
    let len := wordSemTheWord (holFapply s.store .heapLength) >>> wordShiftAmount width
    ∃ root i1 pa1 ib1 pb1 m1 roots i2 pa2 ib2 pb2 m2 i3 pa3 ib3 pb3 m3,
      wordGenGcMove conf (holFapply s.store .globals, 0, other, len, newEnd,
        curr, s.memory, s.mdomain) = (root, i1, pa1, ib1, pb1, m1, true) ∧
      wordGenGcMoveRootsBitmaps conf (s.stack.drop s.stackSpace, s.bitmaps,
        i1, pa1, ib1, pb1, curr, m1, s.mdomain) = (roots, i2, pa2, ib2, pb2, m2, true) ∧
      wordGenGcMoveLoop conf len.toNat (other, i2, pa2, ib2, pb2, newEnd,
        curr, m2, s.mdomain) = (i3, pa3, ib3, pb3, m3, true) ∧
      wordGcFunAssum conf s.store ∧
        let a := wordSemTheWord (holFapply s.store .allocSize)
        let s1 := s.store.updateListEq
          [(.currHeap, .word other), (.otherHeap, .word curr),
           (.nextFree, .word pa3), (.genStart, .word (pa3 - other)),
           (.triggerGC, .word (pa3 + newTrig (pb3 - pa3) a genSizes)),
           (.endOfHeap, .word pb3), (.globals, root), (.globReal, globReal conf other root),
           (.temp 0, .word 0), (.temp 1, .word 0), (.temp 2, .word 0),
           (.temp 3, .word 0), (.temp 4, .word 0), (.temp 5, .word 0), (.temp 6, .word 0)]
        collected = { s with
            stack := s.stack.take s.stackSpace ++ roots
            memory := m3
            store := s1
            regs := HolFiniteMapExact.empty } := by
  dsimp only
  have hf := full_collected_pipeline hgc hk hp hs
  dsimp only at hf
  let curr := wordSemTheWord (holFapply s.store .currHeap)
  let other := wordSemTheWord (holFapply s.store .otherHeap)
  let newEnd := other + wordSemTheWord (holFapply s.store .heapLength)
  let len := wordSemTheWord (holFapply s.store .heapLength) >>> wordShiftAmount width
  generalize hm : wordGenGcMove conf (holFapply s.store .globals, 0, other, len,
    newEnd, curr, s.memory, s.mdomain) = q1 at hf
  obtain ⟨root, i1, pa1, ib1, pb1, m1, c1⟩ := q1
  dsimp only [curr, other, newEnd, len] at hm
  try rw [hm] at hf
  dsimp only at hf
  generalize hr : wordGenGcMoveRootsBitmaps conf (s.stack.drop s.stackSpace,
    s.bitmaps, i1, pa1, ib1, pb1, curr, m1, s.mdomain) = q2 at hf
  obtain ⟨roots, i2, pa2, ib2, pb2, m2, c2⟩ := q2
  dsimp only [curr] at hr
  try rw [hr] at hf
  dsimp only at hf
  generalize hl : wordGenGcMoveLoop conf len.toNat (other, i2, pa2, ib2, pb2,
    newEnd, curr, m2, s.mdomain) = q3 at hf
  obtain ⟨i3, pa3, ib3, pb3, m3, c3⟩ := q3
  dsimp only [curr, other, newEnd, len] at hl
  try rw [hl] at hf
  dsimp only at hf
  obtain ⟨ha, hc1, hc2, hc3, ht⟩ := hf
  subst c1; subst c2; subst c3
  exact ⟨root, i1, pa1, ib1, pb1, m1, roots, i2, pa2, ib2, pb2, m2,
    i3, pa3, ib3, pb3, m3, rfl, hr, hl, ha, ht⟩

open Flapjack.StackSemEvaluate Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- Actual selector execution chooses full code for the original empty-size
case or insufficient partial space. Both cases retain selector loads. -/
theorem evaluate_full_select {width : Nat} [NeZero width] {C F : Type}
    {genSizes : List Nat} {w trig endh : BitVec width}
    (xs ys : List (HolProg width)) (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true)
    (ht : s.store.lookup .triggerGC = some (.word trig))
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (hw : s.regs.lookup 1 = some (.word w))
    (hfull : genSizes = [] ∨ (endh - trig).toNat < w.toNat) :
    evaluate (wordGcPartialOrFull genSizes xs ys, s) =
      evaluate (listSeqHOL ys,
        setVar 7 (.word (endh - trig)) (setVar 7 (.word endh)
          (setVar 8 (.word trig) s))) := by
  cases genSizes with
  | nil =>
    cases ys <;>
      simp [wordGcPartialOrFull, listSeqHOL, evaluate_seq, evaluate_get,
        evaluate_inst, evaluate_skip, subInst, StackSemInst.instHOL,
        StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
        StackSemExpressions.wordExp, wordOpHOL, wordOp, hu, ht, he,
        setVar, fixClock, StackSemRegisterTransfers.storeOfSyntax,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  | cons g gs =>
    have hn : (endh - trig).toNat < w.toNat := by simpa using hfull
    simp only [BitVec.toNat_sub] at hn
    simp [wordGcPartialOrFull, listSeqHOL, evaluate_seq, evaluate_get,
      evaluate_inst, evaluate_ite, subInst, StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
      StackSemExpressions.wordExp, getVar, StackSemStateOps.getVarImm,
      HolRegImm.toWordRegImm, wordSemWordCmp, wordCmpHOL, wordOpHOL, wordOp,
      BitVec.lt_def, hu, ht, he, hw, hn, setVar, fixClock,
      StackSemRegisterTransfers.storeOfSyntax,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- The original negated source partial-selector premise supplies the exact
full-selector branch, with well-formed store loads derived from GC assumptions. -/
theorem evaluate_full_select_from_source {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (genSizes : List Nat) (w : BitVec width)
    (xs ys : List (HolProg width)) (s : StackSemStateFiniteExact width C F)
    (ha : wordGcFunAssum conf (setStore .allocSize (.word w) s).store)
    (hp : ¬wordGenGcCanDoPartial genSizes (setStore .allocSize (.word w) s).store)
    (hu : s.useStore = true) (hw : s.regs.lookup 1 = some (.word w)) :
    let trig := wordSemTheWord (holFapply s.store .triggerGC)
    let endh := wordSemTheWord (holFapply s.store .endOfHeap)
    evaluate (wordGcPartialOrFull genSizes xs ys, s) =
      evaluate (listSeqHOL ys,
        setVar 7 (.word (endh - trig)) (setVar 7 (.word endh)
          (setVar 8 (.word trig) s))) := by
  dsimp only
  obtain ⟨loads, _⟩ := AllocGenerationalPartial.partial_source_loads conf _ ha
  have ht := loads .triggerGC (by simp)
  have he := loads .endOfHeap (by simp)
  simp [setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, holFapply] at ht he
  apply evaluate_full_select xs ys s hu
  · simpa only [holFapply] using ht
  · simpa only [holFapply] using he
  · exact hw
  · by_cases hn : genSizes = []
    · exact Or.inl hn
    · right
      simpa [wordGenGcCanDoPartial, hn, setStore, holFapply,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, wordSemTheWord,
        BitVec.le_def] using hp

open Flapjack.Compiler.Backend.StackRemove (constInst rightShiftInst)

/-- State after the original twenty full-collector setup instructions. -/
def fullSetupState {width : Nat} [NeZero width] {C F : Type}
    (w len other : BitVec width) (ret glob : WordLocW width)
    (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  setVar 8 (.word 0) (setVar 6 (.word 0) (setVar 5 (glob) (setVar 4 (.word 0) (setStore (.temp 3) (.word (len >>> wordShiftAmount width)) (setVar 4 (.word (len >>> wordShiftAmount width)) (setVar 4 (.word len) (setStore (.temp 6) (.word (len + other)) (setStore (.temp 5) (.word (len + other)) (setStore (.temp 4) (.word (len + other)) (setStore (.temp 2) (.word (len + other)) (setStore (.temp 1) (.word (len + other)) (setStore (.temp 0) (.word (len + other)) (setVar 4 (.word (len + other)) (setVar 4 (.word len) (setVar 3 (.word other) (setVar 2 (.word 0) (setVar 1 (.word 0) (setStore .nextFree (ret) (setStore .allocSize (.word w) (s))))))))))))))))))))

/-- Original full setup executes without consuming clock, saving the return
register and initializing all full-collector temporary slots. -/
theorem evaluate_full_setup {width : Nat} [NeZero width] {C F : Type}
    {w len other : BitVec width} {ret glob : WordLocW width}
    (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true) (hr : s.regs.lookup 0 = some ret)
    (hw : s.regs.lookup 1 = some (.word w))
    (hl : s.store.lookup .heapLength = some (.word len))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hg : s.store.lookup .globals = some glob)
    (hshift : wordShiftAmount width < width) :
    evaluate (listSeqHOL [.set .allocSize 1, .set .nextFree 0,
      constInst 1 0, moveHOL 2 1, .get 3 .otherHeap, .get 4 .heapLength,
      addInst 4 3, .set (.temp 0) 4, .set (.temp 1) 4, .set (.temp 2) 4,
      .set (.temp 4) 4, .set (.temp 5) 4, .set (.temp 6) 4,
      .get 4 .heapLength, rightShiftInst 4 (wordShiftAmount width),
      .set (.temp 3) 4, moveHOL 4 1, .get 5 .globals, moveHOL 6 1, moveHOL 8 1], s) =
      (none, fullSetupState w len other ret glob s) := by
  have hm : wordShiftAmount width % 2 ^ width = wordShiftAmount width :=
    Nat.mod_eq_of_lt (Nat.lt_trans hshift Nat.lt_two_pow_self)
  have hn : ¬width ≤ wordShiftAmount width := Nat.not_le_of_gt hshift
  simp [listSeqHOL, evaluate_seq, evaluate_set, evaluate_get, evaluate_inst,
    constInst, rightShiftInst, moveHOL, addInst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, wordOpHOL, wordOp, wordShiftHOL,
    getVar, setVar, setStore, fixClock, fullSetupState,
    StackSemRegisterTransfers.storeOfSyntax, HolFiniteMapExact.lookup_updateEq,
    FUPDATE_HOL, hu, hr, hw, hl, hg, ho, hm, hn]

/-- The checked full move-code theorem on the concrete original setup. Its
source success equation is discharged by full_source_pipeline in assembly. -/
theorem evaluate_full_first_move {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w len other curr : BitVec width}
    {ret glob moved : WordLocW width} {i pa ib pb : BitVec width}
    {m : BitVec width → WordLocW width} (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true) (hr : s.regs.lookup 0 = some ret)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hm : wordGenGcMove conf (glob, 0, other, len >>> wordShiftAmount width,
      other + len, curr, s.memory, s.mdomain) = (moved, i, pa, ib, pb, m, true))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := fullSetupState w len other ret glob s
    ∃ ck r0 r1 r2 r6 t0 t1,
      evaluate (wordGenGcMoveCode conf, { S with clock := S.clock + ck }) =
        (none, { S with
          memory := m
          store := S.store.updateListEq [(.temp 0, t0), (.temp 1, t1),
            (.temp 2, .word pb), (.temp 3, .word ib)]
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2),
            (3, .word pa), (4, .word i), (5, moved), (6, r6)] }) := by
  dsimp only
  apply word_gen_gc_move_code_thm
  refine ⟨hm, hsl, hws, hw2, hlen, hshift, ?_, ?_, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [fullSetupState, getVar, setVar, setStore,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hu, hc, hr, BitVec.add_comm]

open Flapjack.Compiler.Backend.StackRemove (leftShiftInst)

/-- Original straight-line block after the full globals move. -/
def fullRootsSetupState {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (moved other : BitVec width)
    (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=

  setVar 7 (.word 0) (setStore .globReal (.word ((moved >>> shiftLength conf <<< wordShiftAmount width) + other)) (setVar 7 (.word ((moved >>> shiftLength conf <<< wordShiftAmount width) + other)) (setVar 7 (.word (moved >>> shiftLength conf <<< wordShiftAmount width)) (setVar 7 (.word (moved >>> shiftLength conf)) (setVar 9 (.word other) (setVar 7 (.word moved) (setStore .globals (.word moved) (s))))))))

/-- The original globals/GlobReal update and stack-index initialization execute
without consuming clock, before the dynamic frame load and roots collector. -/
theorem evaluate_full_roots_setup {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {moved other : BitVec width}
    (s : StackSemStateFiniteExact width C F) (hu : s.useStore = true)
    (hm : s.regs.lookup 5 = some (.word moved))
    (hc : s.store.lookup .otherHeap = some (.word other))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) :
    evaluate (listSeqHOL [.set .globals 5, moveHOL 7 5, .get 9 .otherHeap,
      rightShiftInst 7 (shiftLength conf), leftShiftInst 7 (wordShiftAmount width),
      addInst 7 9, .set .globReal 7, constInst 7 0], s) =
      (none, fullRootsSetupState conf moved other s) := by
  have hpow : width < 2 ^ width := Nat.lt_two_pow_self
  have hslm : shiftLength conf % 2 ^ width = shiftLength conf :=
    Nat.mod_eq_of_lt (Nat.lt_trans hsl hpow)
  have hwsm : wordShiftAmount width % 2 ^ width = wordShiftAmount width :=
    Nat.mod_eq_of_lt (Nat.lt_trans hws hpow)
  have hsn : ¬width ≤ shiftLength conf := Nat.not_le_of_gt hsl
  have hwn : ¬width ≤ wordShiftAmount width := Nat.not_le_of_gt hws
  simp [listSeqHOL, evaluate_seq, evaluate_set, evaluate_get, evaluate_inst,
    rightShiftInst, leftShiftInst, addInst, constInst, moveHOL,
    StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp, wordOpHOL, wordOp,
    wordShiftHOL, getVar, setVar, setStore, fixClock, fullRootsSetupState,
    StackSemRegisterTransfers.storeOfSyntax, HolFiniteMapExact.lookup_updateEq,
    FUPDATE_HOL, hu, hm, hc, hslm, hwsm, hsn, hwn]

/-- Successful original full roots collection excludes an empty active frame,
discharging the strict dynamic StackLoadAny bound from source success. -/
theorem full_roots_frame_bound {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {curr i pa ib pb i1 pa1 ib1 pb1 : BitVec width}
    {m m1 : BitVec width → WordLocW width} {stack1 : List (WordLocW width)}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i, pa, ib, pb, curr, m, s.mdomain) =
      (stack1, i1, pa1, ib1, pb1, m1, true)) :
    s.stackSpace < s.stack.length := by
  by_contra h
  have hd : s.stack.drop s.stackSpace = [] :=
    List.drop_eq_nil_of_le (Nat.le_of_not_gt h)
  rw [hd] at hm
  rw [wordGenGcMoveRootsBitmaps_unroll _ _ _ _ _ _ _ _ hm] at hm
  simp at hm

/-- Original full frame-load and index move retain the saved state clock and
load the first active-frame word with the original zero offset in register8. -/
theorem evaluate_full_frame_load {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (hu : s.useStack = true)
    (hr8 : s.regs.lookup 8 = some (.word 0))
    (hr7 : s.regs.lookup 7 = some (.word 0)) (hs : s.stackSpace < s.stack.length) :
    evaluate (listSeqHOL [.stackLoadAny 9 8, moveHOL 8 7], s) =
      (none, setVar 8 (.word 0) (setVar 9 (holHd (s.stack.drop s.stackSpace)) s)) := by
  have hl := AllocGenerationalPartial.evaluate_partial_frame_load s hu hr8 hs
  simp only [listSeqHOL, evaluate_seq, hl]
  simp [evaluate_inst, moveHOL, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, setVar, fixClock,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hr7]

/-- Concrete roots entry after full setup, globals move/update and frame load.
This packages the actual states, not a new evaluator or simulation premise. -/
noncomputable def fullRootsInputState {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (w len other moved i pa ib pb : BitVec width)
    (ret glob q0 q1 q2 q6 t0 t1 : WordLocW width)
    (m : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F) :
    StackSemStateFiniteExact width C F :=
  let S := fullSetupState w len other ret glob s
  let M := { S with
    memory := m
    store := S.store.updateListEq [(.temp 0, t0), (.temp 1, t1),
      (.temp 2, .word pb), (.temp 3, .word ib)]
    regs := S.regs.updateListEq [(0, q0), (1, q1), (2, q2),
      (3, .word pa), (4, .word i), (5, .word moved), (6, q6)] }
  setVar 8 (.word 0) (setVar 9 (holHd (s.stack.drop s.stackSpace))
    (fullRootsSetupState conf moved other M))

/-- Full roots code executes on the original concrete entry, preserving the
source stack prefix and returning original temporary-slot/register updates. -/
theorem evaluate_full_roots {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w len other moved curr i pa ib pb i1 pa1 ib1 pb1 : BitVec width}
    {ret glob q0 q1 q2 q6 t0 t1 : WordLocW width}
    {m m1 : BitVec width → WordLocW width} {stack1 : List (WordLocW width)}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i, pa, ib, pb, curr, m, s.mdomain) =
      (stack1, i1, pa1, ib1, pb1, m1, true))
    (hu : s.useStore = true) (hus : s.useStack = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := fullRootsInputState conf w len other moved i pa ib pb
      ret glob q0 q1 q2 q6 t0 t1 m s
    ∃ ck r0 r1 r2 r5 r6 r7 r8 u0 u1,
      evaluate (wordGenGcMoveRootsBitmapsCode conf, { S with clock := S.clock + ck }) =
        (none, { S with
          memory := m1
          stack := s.stack.take s.stackSpace ++ stack1
          clock := S.clock
          store := S.store.updateListEq [(.temp 0, u0), (.temp 1, u1),
            (.temp 2, .word pb1), (.temp 3, .word ib1)]
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
            (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8), (9, .word 0)] }) := by
  have hframe := full_roots_frame_bound s hm
  dsimp only
  have H := word_gen_gc_move_roots_bitmaps_code_thm (conf := conf)
    (init := s.stack.take s.stackSpace) (stack := s.stack.drop s.stackSpace)
    s.bitmaps (fullRootsInputState conf w len other moved i pa ib pb
      ret glob q0 q1 q2 q6 t0 t1 m s)
    i pa ib pb curr m s.mdomain [] stack1 0 i1 pa1 ib1 pb1 m1 []
  have HH := H (by
    refine ⟨hm, hb, hg, hsl, hws, hw2, hlen, hg, hshift, ?_⟩
    simp [fullRootsInputState, fullRootsSetupState, fullSetupState,
      getVar, setVar, setStore, HolFiniteMapExact.lookup_updateListEq,
      FUPDATE_LIST_HOL, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
      hu, hus, hc, List.take_append_drop, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hframe), Nat.mul_comm, hs])
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, r9, u0, u1, heval⟩ := HH
  exact ⟨ck, r0, r1, r2, r5, r6, r7, r8, u0, u1, by simpa using heval⟩

/-- Concrete original full-loop setup, including the bitwise combined stop
condition; all other store/stack/memory fields and clock are preserved. -/
def fullLoopSetupState {width : Nat} [NeZero width] {C F : Type}
    (pa pb other newEnd : BitVec width) (s : StackSemStateFiniteExact width C F) :
    StackSemStateFiniteExact width C F :=
  setVar 7 (.word ((pa - other) ||| (pb - newEnd))) (setVar 6 (.word (pb - newEnd)) (setVar 6 (.word (pb)) (setVar 1 (.word (newEnd)) (setVar 7 (.word (pa - other)) (setVar 7 (.word (pa)) (setVar 8 (.word (other)) (setVar 2 (.word (pb)) (s))))))))

/-- The original eight instructions compute both loop progress differences. -/
theorem evaluate_full_loop_setup {width : Nat} [NeZero width] {C F : Type}
    {pa pb other newEnd : BitVec width} (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true) (hp : s.regs.lookup 3 = some (.word pa))
    (hb : s.store.lookup (.temp 2) = some (.word pb))
    (he : s.store.lookup (.temp 6) = some (.word newEnd))
    (ho : s.store.lookup .otherHeap = some (.word other)) :
    evaluate (listSeqHOL [.get 2 (.temp 2), .get 8 .otherHeap, moveHOL 7 3,
      subInst 7 8, .get 1 (.temp 6), moveHOL 6 2, subInst 6 1, orInst 7 6], s) =
      (none, fullLoopSetupState pa pb other newEnd s) := by
  simp at hb he
  simp [listSeqHOL, evaluate_seq, evaluate_get, evaluate_inst,
    moveHOL, subInst, orInst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, wordOpHOL, wordOp, OrOp.or, BitVec.or_zero, setVar,
    fixClock, fullLoopSetupState, StackSemRegisterTransfers.storeOfSyntax,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hu, hp, hb, he, ho]

/-- Original combined progress test is zero precisely at both heap boundaries.
This is modular word equality, not a natural-number approximation. -/
theorem full_loop_stop {width : Nat} (pa pb other newEnd : BitVec width) :
    ((pa - other) ||| (pb - newEnd)) = 0 ↔ newEnd = pb ∧ other = pa := by
  simp [BitVec.or_eq_zero_iff, BitVec.sub_eq_iff_eq_add]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h2.symm, h1.symm⟩

/-- Apply the checked full-loop code theorem after the original concrete
progress setup. Entry facts are discharged from roots outputs in assembly. -/
theorem evaluate_full_loop {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {k : Nat} {other i pa ib pb newEnd curr i1 pa1 ib1 pb1 : BitVec width}
    {m : BitVec width → WordLocW width} (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMoveLoop conf k (other, i, pa, ib, pb, newEnd, curr,
      s.memory, s.mdomain) = (i1, pa1, ib1, pb1, m, true))
    (hu : s.useStore = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hp : s.regs.lookup 3 = some (.word pa)) (hi : s.regs.lookup 4 = some (.word i))
    (hb : s.store.lookup (.temp 2) = some (.word pb))
    (hib : s.store.lookup (.temp 3) = some (.word ib))
    (he : s.store.lookup (.temp 6) = some (.word newEnd))
    (he4 : s.store.lookup (.temp 4) = some (.word newEnd))
    (h0 : (s.regs.lookup 0).isSome = true) (h5 : (s.regs.lookup 5).isSome = true)
    (ht0 : (s.store.lookup (.temp 0)).isSome = true)
    (ht1 : (s.store.lookup (.temp 1)).isSome = true)
    (ht5 : (s.store.lookup (.temp 5)).isSome = true)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hls : conf.lenSize + 2 < width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := fullLoopSetupState pa pb other newEnd s
    ∃ ck r0 r1 r2 r5 r6 r7 r8 t0 t1 t4 t5 t6,
      evaluate (wordGenGcMoveLoopCode conf, { S with clock := S.clock + ck }) =
        (none, { S with
          memory := m
          store := S.store.updateListEq [(.temp 0, t0), (.temp 1, t1),
            (.temp 2, .word pb1), (.temp 3, .word ib1), (.temp 4, t4),
            (.temp 5, t5), (.temp 6, t6)]
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
            (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8)] }) := by
  simp at ht0 ht1 ht5 hb hib he he4
  dsimp only
  apply word_gen_gc_move_loop_code_thm (conf := conf) (c1 := true)
    k other i pa ib pb newEnd curr s.memory s.mdomain i1 pa1 ib1 pb1 m
    ((pa - other) ||| (pb - newEnd))
  refine ⟨hm, hsl, hws, hw2, hlen, hls, hshift, ?_, ?_, rfl, rfl,
    full_loop_stop pa pb other newEnd, ?_⟩
  · simpa [fullLoopSetupState, setVar] using hc
  · simpa [fullLoopSetupState, setVar] using hu
  · simp [fullLoopSetupState, getVar, setVar, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL, ht0, ht1, ht5, hb, hib, he, he4, h0, h5, hi, hp]

/-- Concrete full-collector heap swap and allocation metadata setup. -/
def fullCleanupState {width : Nat} [NeZero width] {C F : Type}
    (curr other pa pb : BitVec width) (ret : WordLocW width)
    (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  setStore .genStart (.word (pa - other)) (setVar 8 (.word (pa - other)) (setVar 8 (.word pa) (setStore .endOfHeap (.word pb) (setStore .nextFree (.word pa) (setVar 0 (ret) (setStore .otherHeap (.word curr) (setStore .currHeap (.word other) (setVar 2 (.word pb) (setVar 1 (.word other) (setVar 0 (.word curr) (s)))))))))))

/-- Original eleven cleanup instructions swap heaps, restore the saved return
register and install NextFree/EndOfHeap/GenStart before SetNewTrigger. -/
theorem evaluate_full_cleanup_setup {width : Nat} [NeZero width] {C F : Type}
    {curr other pa pb : BitVec width} {ret : WordLocW width}
    (s : StackSemStateFiniteExact width C F) (hu : s.useStore = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hb : s.store.lookup (.temp 2) = some (.word pb))
    (hr : s.store.lookup .nextFree = some ret)
    (hp : s.regs.lookup 3 = some (.word pa)) :
    evaluate (listSeqHOL [.get 0 .currHeap, .get 1 .otherHeap, .get 2 (.temp 2),
      .set .currHeap 1, .set .otherHeap 0, .get 0 .nextFree, .set .nextFree 3,
      .set .endOfHeap 2, moveHOL 8 3, subInst 8 1, .set .genStart 8], s) =
      (none, fullCleanupState curr other pa pb ret s) := by
  simp at hb
  simp [listSeqHOL, evaluate_seq, evaluate_get, evaluate_set, evaluate_inst,
    moveHOL, subInst, StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp, wordOpHOL, wordOp,
    getVar, setVar, setStore, fixClock, fullCleanupState,
    StackSemRegisterTransfers.storeOfSyntax, HolFiniteMapExact.lookup_updateEq,
    FUPDATE_HOL, hu, hc, ho, hb, hr, hp]

/-- Original final full collector temporary clearing state. -/
def fullClearState {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  setStore (.temp 6) (.word 0) (setStore (.temp 5) (.word 0) (setStore (.temp 4) (.word 0) (setStore (.temp 3) (.word 0) (setStore (.temp 2) (.word 0) (setStore (.temp 1) (.word 0) (setStore (.temp 0) (.word 0) (setVar 1 (.word 0) s)))))))

/-- Clear all seven original temporary fields after SetNewTrigger, preserving
all other state components and the return register. -/
theorem evaluate_full_clear {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (hu : s.useStore = true) :
    evaluate (listSeqHOL [constInst 1 0, .set (.temp 0) 1, .set (.temp 1) 1,
      .set (.temp 2) 1, .set (.temp 3) 1, .set (.temp 4) 1,
      .set (.temp 5) 1, .set (.temp 6) 1], s) = (none, fullClearState s) := by
  simp [listSeqHOL, evaluate_seq, evaluate_set, evaluate_inst, constInst,
    StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp, getVar,
    setVar, setStore, fixClock, fullClearState, StackSemRegisterTransfers.storeOfSyntax,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hu]

/-- Actual final full-collector space test, retaining its insufficient-space
Halt Word1 branch and emptyEnv state. No normal-return assumption is added. -/
theorem evaluate_full_space_branch {width : Nat} [NeZero width] {C F : Type}
    {w gap : BitVec width} (s : StackSemStateFiniteExact width C F)
    (hw : s.regs.lookup 1 = some (.word w))
    (hg : s.regs.lookup 2 = some (.word gap)) :
    evaluate (.ite .lower 2 (.reg 1) (.seq (constInst 1 1) (.halt 1)) .skip, s) =
      if gap.toNat < w.toNat then
        (some (.halt (.word 1)), emptyEnv (setVar 1 (.word 1) s))
      else (none, s) := by
  by_cases h : gap.toNat < w.toNat <;>
  simp [evaluate_ite, evaluate_seq, evaluate_inst, evaluate_halt, evaluate_skip,
    constInst, StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp, getVar,
    StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp,
    wordCmpHOL, BitVec.lt_def, hw, hg, setVar, fixClock,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, h]

/-- Original source post-collector allocation branch uses exactly the target
unsigned gap comparison; full collection does not promise sufficient space. -/
theorem alloc_after_full_collection {width : Nat} [NeZero width] {C F : Type}
    {w pa trigger : BitVec width} {s collected : StackSemStateFiniteExact width C F}
    (hg : StackSemAllocation.gc (setStore .allocSize (.word w) s) = some collected)
    (ha : collected.store.lookup .allocSize = some (.word w))
    (hp : collected.store.lookup .nextFree = some (.word pa))
    (ht : collected.store.lookup .triggerGC = some (.word trigger)) :
    StackSemAllocation.alloc w s =
      if (trigger - pa).toNat < w.toNat then
        (some (.halt (.word 1)), emptyEnv collected)
      else (none, collected) := by
  by_cases h : (trigger - pa).toNat < w.toNat
  · have hn : ¬w.toNat ≤ (trigger - pa).toNat := Nat.not_le_of_gt h
    simp only [BitVec.toNat_sub] at h hn
    simp [StackSemAllocation.alloc, hg, ha, StackSemAllocation.hasSpace, hp, ht, hn, h]
  · have hn : w.toNat ≤ (trigger - pa).toNat := Nat.le_of_not_gt h
    simp only [BitVec.toNat_sub] at h hn
    simp [StackSemAllocation.alloc, hg, ha, StackSemAllocation.hasSpace, hp, ht, hn, h]

/-- Halt discards the constant register update, exactly as source emptyEnv.
This is state equality, not merely an observation projection. -/
theorem emptyEnv_setVar {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (r : Nat) (w : WordLocW width) :
    emptyEnv (setVar r w s) = emptyEnv s := by rfl

/-- Final original loads and subtraction compute the same source hasSpace gap. -/
theorem evaluate_full_space_setup {width : Nat} [NeZero width] {C F : Type}
    {w pa trigger : BitVec width} (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true) (hp : s.regs.lookup 3 = some (.word pa))
    (hw : s.store.lookup .allocSize = some (.word w))
    (ht : s.store.lookup .triggerGC = some (.word trigger)) :
    evaluate (listSeqHOL [.get 1 .allocSize, .get 2 .triggerGC, subInst 2 3], s) =
      (none, setVar 2 (.word (trigger - pa)) (setVar 2 (.word trigger)
        (setVar 1 (.word w) s))) := by
  simp [listSeqHOL, evaluate_seq, evaluate_get, evaluate_inst, subInst,
    StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp, wordOpHOL, wordOp,
    setVar, fixClock, StackSemRegisterTransfers.storeOfSyntax,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hu, hp, hw, ht]

/-- Original full collector SetNewTrigger uses end register2 and allocation
pointer register3; all distinctness and concrete setup facts are discharged. -/
theorem evaluate_full_trigger {width : Nat} [NeZero width] {C F : Type}
    {curr other pa pb w : BitVec width} {ret : WordLocW width}
    (genSizes : List Nat) (s : StackSemStateFiniteExact width C F)
    (hg : goodDimindex width) (hu : s.useStore = true)
    (hp : s.regs.lookup 3 = some (.word pa))
    (hw : s.store.lookup .allocSize = some (.word w)) :
    let S := fullCleanupState curr other pa pb ret s
    ∃ r7 r1 r4,
      evaluate (setNewTrigger 2 3 genSizes, S) =
        (none, { S with
          regs := ((S.regs.updateEq (1, r1)).updateEq (7, r7)).updateEq (4, r4)
          store := S.store.updateEq (.triggerGC,
            .word (pa + newTrig (pb - pa) w genSizes)) }) := by
  dsimp only
  apply setNewTrigger_run _ 2 3 pb pa w genSizes hg
  · simpa [fullCleanupState, setVar, setStore] using hu
  · decide
  · simp [fullCleanupState, setVar, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  · simp [fullCleanupState, setVar, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hp]
  · simp [fullCleanupState, setVar, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hw]

/-- Exact roots-output carrier used by the original full loop preparation. -/
noncomputable def fullRootsOutputState {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (w len other moved i0 pa0 ib0 pb0 i pa ib pb : BitVec width)
    (ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 : WordLocW width)
    (m0 m : BitVec width → WordLocW width) (roots : List (WordLocW width))
    (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  let S := fullRootsInputState conf w len other moved i0 pa0 ib0 pb0
    ret glob q0 q1 q2 q6 t0 t1 m0 s
  { S with
    memory := m
    stack := s.stack.take s.stackSpace ++ roots
    clock := S.clock
    store := S.store.updateListEq [(.temp 0, u0), (.temp 1, u1),
      (.temp 2, .word pb), (.temp 3, .word ib)]
    regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa),
      (4, .word i), (5, r5), (6, r6), (7, r7), (8, r8), (9, .word 0)] }

/-- The original full roots result discharges every loop-entry register and
store condition, including untouched Temp4/5/6 from the original setup. -/
theorem evaluate_full_loop_after_roots {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w len other moved curr i0 pa0 ib0 pb0 i pa ib pb i1 pa1 ib1 pb1 : BitVec width}
    {ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 : WordLocW width}
    {m0 m m1 : BitVec width → WordLocW width} {roots : List (WordLocW width)}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMoveLoop conf (len >>> wordShiftAmount width).toNat
      (other, i, pa, ib, pb, other + len, curr, m, s.mdomain) =
      (i1, pa1, ib1, pb1, m1, true))
    (hu : s.useStore = true) (hc : s.store.lookup .currHeap = some (.word curr))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hls : conf.lenSize + 2 < width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let R := fullRootsOutputState conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
      ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 m0 m roots s
    let S := fullLoopSetupState pa pb other (other + len) R
    ∃ ck v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6,
      evaluate (wordGenGcMoveLoopCode conf, { S with clock := S.clock + ck }) =
        (none, { S with
          memory := m1
          store := S.store.updateListEq [(.temp 0, z0), (.temp 1, z1),
            (.temp 2, .word pb1), (.temp 3, .word ib1), (.temp 4, z4),
            (.temp 5, z5), (.temp 6, z6)]
          regs := S.regs.updateListEq [(0, v0), (1, v1), (2, v2), (3, .word pa1),
            (4, .word i1), (5, v5), (6, v6), (7, v7), (8, v8)] }) := by
  dsimp only
  apply evaluate_full_loop
  · exact hm
  all_goals first | assumption | simp [fullRootsOutputState, fullRootsInputState, fullRootsSetupState,
    fullSetupState, setVar, setStore, HolFiniteMapExact.lookup_updateListEq,
    FUPDATE_LIST_HOL, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    hu, BitVec.add_comm]

/-- Complete original clearing and final allocation test, retaining both
result branches. Intermediate executions are constructed by checked components. -/
theorem evaluate_full_clear_space {width : Nat} [NeZero width] {C F : Type}
    {w pa trigger : BitVec width} (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true) (hp : s.regs.lookup 3 = some (.word pa))
    (hw : s.store.lookup .allocSize = some (.word w))
    (ht : s.store.lookup .triggerGC = some (.word trigger)) :
    let C := fullClearState s
    let V := setVar 2 (.word (trigger - pa)) (setVar 2 (.word trigger)
      (setVar 1 (.word w) C))
    evaluate (.seq (listSeqHOL [constInst 1 0, .set (.temp 0) 1, .set (.temp 1) 1,
      .set (.temp 2) 1, .set (.temp 3) 1, .set (.temp 4) 1,
      .set (.temp 5) 1, .set (.temp 6) 1])
      (.seq (listSeqHOL [.get 1 .allocSize, .get 2 .triggerGC, subInst 2 3])
        (.ite .lower 2 (.reg 1) (.seq (constInst 1 1) (.halt 1)) .skip)), s) =
      if (trigger - pa).toNat < w.toNat then
        (some (.halt (.word 1)), emptyEnv C) else (none, V) := by
  dsimp only
  have hclear := evaluate_full_clear s hu
  rw [evaluate_seq_none _ _ _ _ hclear (by rfl)]
  have hspace := evaluate_full_space_setup (w := w) (pa := pa) (trigger := trigger)
    (fullClearState s)
    (by simpa [fullClearState, setStore, setVar] using hu)
    (by simpa [fullClearState, setStore, setVar,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hp)
    (by simpa [fullClearState, setStore, setVar,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hw)
    (by simpa [fullClearState, setStore, setVar,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using ht)
  rw [evaluate_seq_none _ _ _ _ hspace (by rfl)]
  rw [evaluate_full_space_branch (w := w) (gap := trigger - pa) _
    (by simp [setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
    (by simp [setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])]
  simp only [emptyEnv_setVar]

/-- The final suffix as the original instruction list, including Halt on
insufficient space. No regrouped evaluator is used in the result. -/
theorem evaluate_full_clear_space_list {width : Nat} [NeZero width] {C F : Type}
    {w pa trigger : BitVec width} (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true) (hp : s.regs.lookup 3 = some (.word pa))
    (hw : s.store.lookup .allocSize = some (.word w))
    (ht : s.store.lookup .triggerGC = some (.word trigger)) :
    let C := fullClearState s
    let V := setVar 2 (.word (trigger - pa)) (setVar 2 (.word trigger)
      (setVar 1 (.word w) C))
    evaluate (listSeqHOL ([constInst 1 0, .set (.temp 0) 1, .set (.temp 1) 1,
      .set (.temp 2) 1, .set (.temp 3) 1, .set (.temp 4) 1,
      .set (.temp 5) 1, .set (.temp 6) 1] ++
      [.get 1 .allocSize, .get 2 .triggerGC, subInst 2 3] ++
      [.ite .lower 2 (.reg 1) (.seq (constInst 1 1) (.halt 1)) .skip]), s) =
      if (trigger - pa).toNat < w.toNat then
        (some (.halt (.word 1)), emptyEnv C) else (none, V) := by
  dsimp only
  rw [List.append_assoc]
  rw [evaluate_listSeq_append_none _ _ s _ (by simp) (by simp) _
    (evaluate_full_clear s hu)]
  · have hspace := evaluate_full_space_setup (w := w) (pa := pa) (trigger := trigger)
      (fullClearState s)
      (by simpa [fullClearState, setStore, setVar] using hu)
      (by simpa [fullClearState, setStore, setVar,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hp)
      (by simpa [fullClearState, setStore, setVar,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hw)
      (by simpa [fullClearState, setStore, setVar,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using ht)
    rw [evaluate_listSeq_append_none _ _ _ _ (by simp) (by simp) _ hspace]
    · simp only [listSeqHOL]
      rw [evaluate_full_space_branch (w := w) (gap := trigger - pa) _
        (by simp [setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
        (by simp [setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])]
      simp only [emptyEnv_setVar]
    · intro x hx U
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> first
        | exact evaluate_clock_of_leaf _ (Or.inl rfl) U
        | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) U
  · intro x hx U
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | exact evaluate_clock_of_leaf _ (Or.inl rfl) U
      | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) U

/-- Complete original full-collector tail after the loop: heap swap, trigger,
seven temporary clears and normal/Halt space test with complete state. -/
theorem evaluate_full_trigger_cleanup {width : Nat} [NeZero width] {C F : Type}
    {curr other pa pb w : BitVec width} {ret : WordLocW width}
    (genSizes : List Nat) (s : StackSemStateFiniteExact width C F)
    (hg : goodDimindex width) (hu : s.useStore = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hb : s.store.lookup (.temp 2) = some (.word pb))
    (hr : s.store.lookup .nextFree = some ret)
    (hp : s.regs.lookup 3 = some (.word pa))
    (hw : s.store.lookup .allocSize = some (.word w)) :
    let S := fullCleanupState curr other pa pb ret s
    ∃ r7 r1 r4,
      let T := { S with
        regs := ((S.regs.updateEq (1, r1)).updateEq (7, r7)).updateEq (4, r4)
        store := S.store.updateEq (.triggerGC, .word (pa + newTrig (pb - pa) w genSizes)) }
      let C := fullClearState T
      let trigger := pa + newTrig (pb - pa) w genSizes
      let V := setVar 2 (.word (trigger - pa)) (setVar 2 (.word trigger)
        (setVar 1 (.word w) C))
      evaluate (listSeqHOL ([.get 0 .currHeap, .get 1 .otherHeap, .get 2 (.temp 2),
        .set .currHeap 1, .set .otherHeap 0, .get 0 .nextFree, .set .nextFree 3,
        .set .endOfHeap 2, moveHOL 8 3, subInst 8 1, .set .genStart 8] ++
        [setNewTrigger 2 3 genSizes] ++
        [constInst 1 0, .set (.temp 0) 1, .set (.temp 1) 1, .set (.temp 2) 1,
          .set (.temp 3) 1, .set (.temp 4) 1, .set (.temp 5) 1, .set (.temp 6) 1] ++
        [.get 1 .allocSize, .get 2 .triggerGC, subInst 2 3] ++
        [.ite .lower 2 (.reg 1) (.seq (constInst 1 1) (.halt 1)) .skip]), s) =
        if (trigger - pa).toNat < w.toNat then
          (some (.halt (.word 1)), emptyEnv C) else (none, V) := by
  dsimp only
  obtain ⟨r7, r1, r4, htrigger⟩ := evaluate_full_trigger (curr := curr) (other := other)
    (pb := pb) (ret := ret) genSizes s hg hu hp hw
  refine ⟨r7, r1, r4, ?_⟩
  simp only [List.append_assoc]
  rw [evaluate_listSeq_append_none _ _ s _ (by simp) (by simp) _
    (evaluate_full_cleanup_setup s hu hc ho hb hr hp)]
  · simp only [List.cons_append, List.nil_append]
    rw [listSeqHOL]
    rw [evaluate_seq_none _ _ _ _ htrigger (by rfl)]
    apply evaluate_full_clear_space_list
    · simpa [fullCleanupState, setVar, setStore] using hu
    · simp [fullCleanupState, setVar, setStore, HolFiniteMapExact.lookup_updateEq,
        FUPDATE_HOL, hp]
    · simp [fullCleanupState, setVar, setStore, HolFiniteMapExact.lookup_updateEq,
        FUPDATE_HOL, hw]
    · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  · intro x hx U
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | exact evaluate_clock_of_leaf _ (Or.inl rfl) U
      | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) U

/-- Original full setup instruction list, kept separate for clock composition. -/
def fullSetupCode {width : Nat} [NeZero width] : List (HolProg width) :=
  [.set .allocSize 1, .set .nextFree 0,
      constInst 1 0, moveHOL 2 1, .get 3 .otherHeap, .get 4 .heapLength,
      addInst 4 3, .set (.temp 0) 4, .set (.temp 1) 4, .set (.temp 2) 4,
      .set (.temp 4) 4, .set (.temp 5) 4, .set (.temp 6) 4,
      .get 4 .heapLength, rightShiftInst 4 (wordShiftAmount width),
      .set (.temp 3) 4, moveHOL 4 1, .get 5 .globals, moveHOL 6 1, moveHOL 8 1]

/-- Append a continuation to the original full setup without changing its
clock or prepared state. The continuation result is unrestricted. -/
theorem evaluate_full_setup_append {width : Nat} [NeZero width] {C F : Type}
    {w len other : BitVec width} {ret glob : WordLocW width}
    (rest : List (HolProg width)) (hrest : rest ≠ [])
    (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true) (hr : s.regs.lookup 0 = some ret)
    (hw : s.regs.lookup 1 = some (.word w))
    (hl : s.store.lookup .heapLength = some (.word len))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hg : s.store.lookup .globals = some glob)
    (hshift : wordShiftAmount width < width) :
    evaluate (listSeqHOL (fullSetupCode ++ rest), s) =
      evaluate (listSeqHOL rest, fullSetupState w len other ret glob s) := by
  apply evaluate_listSeq_append_none _ _ _ _ (by simp [fullSetupCode]) hrest
  · intro x hx U
    simp only [fullSetupCode, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | exact evaluate_clock_of_leaf _ (Or.inl rfl) U
      | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) U
  · exact evaluate_full_setup s hu hr hw hl ho hg hshift

/-- Original setup and first full collector code as one literal list with
its constructed clock; target evaluation is obtained, never assumed. -/
theorem evaluate_full_move_with_prefix {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w len other curr : BitVec width}
    {ret glob moved : WordLocW width} {i pa ib pb : BitVec width}
    {m : BitVec width → WordLocW width} (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true) (hr : s.regs.lookup 0 = some ret)
    (hw : s.regs.lookup 1 = some (.word w))
    (hl : s.store.lookup .heapLength = some (.word len))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hg : s.store.lookup .globals = some glob)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hm : wordGenGcMove conf (glob, 0, other, len >>> wordShiftAmount width,
      other + len, curr, s.memory, s.mdomain) = (moved, i, pa, ib, pb, m, true))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := fullSetupState w len other ret glob s
    ∃ ck r0 r1 r2 r6 t0 t1,
      evaluate (listSeqHOL (fullSetupCode ++ [wordGenGcMoveCode conf]),
        { s with clock := s.clock + ck }) =
        (none, { S with
          memory := m
          store := S.store.updateListEq [(.temp 0, t0), (.temp 1, t1),
            (.temp 2, .word pb), (.temp 3, .word ib)]
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2),
            (3, .word pa), (4, .word i), (5, moved), (6, r6)] }) := by
  dsimp only
  obtain ⟨ck, r0, r1, r2, r6, t0, t1, hrun⟩ := evaluate_full_first_move
    (w := w) (len := len) (other := other) (ret := ret) s hu hr hc hm hsl hws hw2 hlen hshift
  refine ⟨ck, r0, r1, r2, r6, t0, t1, ?_⟩
  rw [evaluate_full_setup_append [wordGenGcMoveCode conf] (by simp)
    { s with clock := s.clock + ck } hu hr hw hl ho hg hws]
  simpa only [listSeqHOL, fullSetupState, setVar, setStore] using hrun

/-- Compose a normally returning collector prefix with the original tail,
retaining its arbitrary result (including the full allocator Halt branch).
Infrastructure evaluation premises are supplied by constructed stage proofs. -/
theorem evaluate_full_collector_clocks_result {width : Nat} [NeZero width] {C F : Type}
    (xs ys : List (HolProg width)) (hx : xs ≠ []) (hy : ys ≠ [])
    (S T U : StackSemStateFiniteExact width C F) (a b : Nat)
    (r : Option (StackSemResult width))
    (hcl : ∀ x ∈ xs.dropLast, ∀ V : StackSemStateFiniteExact width C F,
      (evaluate (x, V)).2.clock = V.clock)
    (hclock : T.clock = S.clock)
    (hp : evaluate (listSeqHOL xs, { S with clock := S.clock + a }) = (none, T))
    (hq : evaluate (listSeqHOL ys, { T with clock := T.clock + b }) = (r, U)) :
    evaluate (listSeqHOL (xs ++ ys), { S with clock := S.clock + (a + b) }) =
      (r, U) := by
  have he := StackProps.evaluateAddClock b (listSeqHOL xs) _ none T ⟨hp, by simp⟩
  have hpExtended : evaluate (listSeqHOL xs, { S with clock := S.clock + (a + b) }) =
      (none, { T with clock := T.clock + b }) := by
    simpa only [Nat.add_assoc] using he
  rw [AllocGenerationalPartial.evaluate_listSeq_append_collector xs ys _ _ hx hy hcl
    (by simp only; omega) hpExtended]
  exact hq

/-- Original full globals update, frame load and roots index preparation. -/
def fullRootsPrepareCode {width : Nat} [NeZero width] (conf : Config) : List (HolProg width) :=
  [.set .globals 5, moveHOL 7 5, .get 9 .otherHeap,
    rightShiftInst 7 (shiftLength conf), leftShiftInst 7 (wordShiftAmount width),
    addInst 7 9, .set .globReal 7, constInst 7 0, .stackLoadAny 9 8, moveHOL 8 7]

/-- Original full roots preparation followed by any nonempty continuation.
The strict frame bound is derived from source roots success at assembly. -/
theorem evaluate_full_roots_prepare_append {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {moved other : BitVec width}
    (rest : List (HolProg width)) (hrest : rest ≠ [])
    (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true) (hst : s.useStack = true)
    (hglob : s.regs.lookup 5 = some (.word moved))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (h8 : s.regs.lookup 8 = some (.word 0)) (hframe : s.stackSpace < s.stack.length)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) :
    evaluate (listSeqHOL (fullRootsPrepareCode conf ++ rest), s) =
      evaluate (listSeqHOL rest, setVar 8 (.word 0)
        (setVar 9 (holHd (s.stack.drop s.stackSpace)) (fullRootsSetupState conf moved other s))) := by
  apply evaluate_listSeq_append_none _ _ _ _ (by simp [fullRootsPrepareCode]) hrest
  · intro x hx U
    simp only [fullRootsPrepareCode, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | exact evaluate_clock_of_leaf _ (Or.inl rfl) U
      | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) U
  · have hp := evaluate_full_roots_setup s hu hglob ho hsl hws
    have hq := evaluate_full_frame_load (fullRootsSetupState conf moved other s)
      (by simpa [fullRootsSetupState, setVar, setStore] using hst)
      (by simpa [fullRootsSetupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using h8)
      (by simp [fullRootsSetupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
      (by simpa [fullRootsSetupState, setVar, setStore] using hframe)
    change evaluate (listSeqHOL ([.set .globals 5, moveHOL 7 5, .get 9 .otherHeap,
      rightShiftInst 7 (shiftLength conf), leftShiftInst 7 (wordShiftAmount width),
      addInst 7 9, .set .globReal 7, constInst 7 0] ++ [.stackLoadAny 9 8, moveHOL 8 7]), s) = _
    rw [evaluate_listSeq_append_none _ _ s _ (by simp) (by simp) _ hp]
    · simpa only [fullRootsSetupState, setVar, setStore] using hq
    · intro x hx U
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
        | exact evaluate_clock_of_leaf _ (Or.inl rfl) U
        | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) U

/-- Original full globals/frame preparation and roots collector as one actual
instruction list, restoring the original clock and complete roots state. -/
theorem evaluate_full_roots_with_prefix {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w len other moved curr i pa ib pb i1 pa1 ib1 pb1 : BitVec width}
    {ret glob q0 q1 q2 q6 t0 t1 : WordLocW width}
    {m m1 : BitVec width → WordLocW width} {stack1 : List (WordLocW width)}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i, pa, ib, pb, curr, m, s.mdomain) =
      (stack1, i1, pa1, ib1, pb1, m1, true))
    (hu : s.useStore = true) (hus : s.useStack = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let B := fullSetupState w len other ret glob s
    let M := { B with
      memory := m
      store := B.store.updateListEq [(.temp 0, t0), (.temp 1, t1),
        (.temp 2, .word pb), (.temp 3, .word ib)]
      regs := B.regs.updateListEq [(0, q0), (1, q1), (2, q2),
        (3, .word pa), (4, .word i), (5, .word moved), (6, q6)] }
    let S := fullRootsInputState conf w len other moved i pa ib pb
      ret glob q0 q1 q2 q6 t0 t1 m s
    ∃ ck r0 r1 r2 r5 r6 r7 r8 u0 u1,
      evaluate (listSeqHOL (fullRootsPrepareCode conf ++ [wordGenGcMoveRootsBitmapsCode conf]),
        { M with clock := M.clock + ck }) =
        (none, { S with
          memory := m1
          stack := s.stack.take s.stackSpace ++ stack1
          clock := S.clock
          store := S.store.updateListEq [(.temp 0, u0), (.temp 1, u1),
            (.temp 2, .word pb1), (.temp 3, .word ib1)]
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
            (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8), (9, .word 0)] }) := by
  dsimp only
  have hframe := full_roots_frame_bound s hm
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, u0, u1, hrun⟩ := evaluate_full_roots
    (w := w) (len := len) (other := other) (moved := moved) (ret := ret) (glob := glob)
    (q0 := q0) (q1 := q1) (q2 := q2) (q6 := q6) (t0 := t0) (t1 := t1)
    s hm hu hus hc hb hs hsl hws hw2 hlen hg hshift
  refine ⟨ck, r0, r1, r2, r5, r6, r7, r8, u0, u1, ?_⟩
  rw [evaluate_full_roots_prepare_append (moved := moved) (other := other)
    [wordGenGcMoveRootsBitmapsCode conf] (by simp) _
    (by simpa [fullSetupState, setVar, setStore] using hu)
    (by simpa [fullSetupState, setVar, setStore] using hus)
    (by simp [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simpa [fullSetupState, setVar, setStore,
      HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using ho)
    (by simp [fullSetupState, setVar, setStore, HolFiniteMapExact.lookup_updateListEq,
      FUPDATE_LIST_HOL, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
    (by simpa [fullSetupState, setVar, setStore] using hframe) hsl hws]
  simpa only [listSeqHOL, fullRootsInputState, fullRootsSetupState, fullSetupState,
    setVar, setStore] using hrun

/-- Original eight-instruction loop entry preparation. -/
def fullLoopPrepareCode {width : Nat} [NeZero width] : List (HolProg width) :=
  [.get 2 (.temp 2), .get 8 .otherHeap, moveHOL 7 3,
      subInst 7 8, .get 1 (.temp 6), moveHOL 6 2, subInst 6 1, orInst 7 6]

/-- Original loop preparation followed by a nonempty continuation, retaining
exact word progress values and arbitrary continuation result. -/
theorem evaluate_full_loop_setup_append {width : Nat} [NeZero width] {C F : Type}
    {pa pb other newEnd : BitVec width} (rest : List (HolProg width)) (hrest : rest ≠ [])
    (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true) (hp : s.regs.lookup 3 = some (.word pa))
    (hb : s.store.lookup (.temp 2) = some (.word pb))
    (he : s.store.lookup (.temp 6) = some (.word newEnd))
    (ho : s.store.lookup .otherHeap = some (.word other)) :
    evaluate (listSeqHOL (fullLoopPrepareCode ++ rest), s) =
      evaluate (listSeqHOL rest, fullLoopSetupState pa pb other newEnd s) := by
  apply evaluate_listSeq_append_none _ _ _ _ (by simp [fullLoopPrepareCode]) hrest
  · intro x hx U
    simp only [fullLoopPrepareCode, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | exact evaluate_clock_of_leaf _ (Or.inl rfl) U
      | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) U
  · exact evaluate_full_loop_setup s hu hp hb he ho

/-- Original loop preparation and full loop code as one actual list, with
constructed clock and complete resulting memory/store/register state. -/
theorem evaluate_full_loop_with_prefix {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {k : Nat} {other i pa ib pb newEnd curr i1 pa1 ib1 pb1 : BitVec width}
    {m : BitVec width → WordLocW width} (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMoveLoop conf k (other, i, pa, ib, pb, newEnd, curr,
      s.memory, s.mdomain) = (i1, pa1, ib1, pb1, m, true))
    (hu : s.useStore = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hp : s.regs.lookup 3 = some (.word pa)) (hi : s.regs.lookup 4 = some (.word i))
    (hb : s.store.lookup (.temp 2) = some (.word pb))
    (hib : s.store.lookup (.temp 3) = some (.word ib))
    (he : s.store.lookup (.temp 6) = some (.word newEnd))
    (he4 : s.store.lookup (.temp 4) = some (.word newEnd))
    (h0 : (s.regs.lookup 0).isSome = true) (h5 : (s.regs.lookup 5).isSome = true)
    (ht0 : (s.store.lookup (.temp 0)).isSome = true)
    (ht1 : (s.store.lookup (.temp 1)).isSome = true)
    (ht5 : (s.store.lookup (.temp 5)).isSome = true)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hls : conf.lenSize + 2 < width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := fullLoopSetupState pa pb other newEnd s
    ∃ ck r0 r1 r2 r5 r6 r7 r8 t0 t1 t4 t5 t6,
      evaluate (listSeqHOL (fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]),
        { s with clock := s.clock + ck }) =
        (none, { S with
          memory := m
          store := S.store.updateListEq [(.temp 0, t0), (.temp 1, t1),
            (.temp 2, .word pb1), (.temp 3, .word ib1), (.temp 4, t4),
            (.temp 5, t5), (.temp 6, t6)]
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
            (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8)] }) := by
  dsimp only
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, t0, t1, t4, t5, t6, hrun⟩ :=
    evaluate_full_loop s hm hu hc hp hi hb hib he he4 h0 h5 ht0 ht1 ht5
      hsl hws hw2 hlen hls hshift
  refine ⟨ck, r0, r1, r2, r5, r6, r7, r8, t0, t1, t4, t5, t6, ?_⟩
  rw [evaluate_full_loop_setup_append [wordGenGcMoveLoopCode conf] (by simp)
    { s with clock := s.clock + ck } hu hp hb he ho]
  simpa only [listSeqHOL, fullLoopSetupState, setVar] using hrun

/-- The original loop-entry instructions consume no clock before the final
collector instruction. This supplies the concatenation obligation without
assuming clock preservation of the collector itself. -/
theorem full_loop_prefix_clock {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (x : HolProg width)
    (hx : x ∈ (fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]).dropLast)
    (V : StackSemStateFiniteExact width C F) :
    (evaluate (x, V)).2.clock = V.clock := by
  simp only [fullLoopPrepareCode, List.cons_append, List.nil_append,
    List.dropLast_cons_cons, List.dropLast_singleton,
    List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
    | exact evaluate_clock_of_leaf _ (Or.inl rfl) V
    | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) V

/-- Clock obligation for the original full globals-move prefix. -/
theorem full_move_prefix_clock {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (x : HolProg width)
    (hx : x ∈ (fullSetupCode ++ [wordGenGcMoveCode conf]).dropLast)
    (V : StackSemStateFiniteExact width C F) :
    (evaluate (x, V)).2.clock = V.clock := by
  simp only [fullSetupCode, List.cons_append, List.nil_append,
    List.dropLast_cons_cons, List.dropLast_singleton,
    List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
    | exact evaluate_clock_of_leaf _ (Or.inl rfl) V
    | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) V

/-- Clock obligation for the original full roots prefix, including the dynamic
frame load. No clock property of roots collection is assumed here. -/
theorem full_roots_prefix_clock {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (x : HolProg width)
    (hx : x ∈ (fullRootsPrepareCode conf ++ [wordGenGcMoveRootsBitmapsCode conf]).dropLast)
    (V : StackSemStateFiniteExact width C F) :
    (evaluate (x, V)).2.clock = V.clock := by
  simp only [fullRootsPrepareCode, List.cons_append, List.nil_append,
    List.dropLast_cons_cons, List.dropLast_singleton,
    List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
    | exact evaluate_clock_of_leaf _ (Or.inl rfl) V
    | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) V

/-- Compose the three concrete original collector segments backwards from
an arbitrary tail result. The stage evaluation premises are infrastructure:
the full case supplies them from the constructive move/roots/loop proofs. -/
theorem evaluate_full_stages {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (tail : List (HolProg width)) (htail : tail ≠ [])
    (S M R L U : StackSemStateFiniteExact width C F) (a b c d : Nat)
    (r : Option (StackSemResult width))
    (hmclock : M.clock = S.clock) (hrclock : R.clock = M.clock)
    (hlclock : L.clock = R.clock)
    (hm : evaluate (listSeqHOL (fullSetupCode ++ [wordGenGcMoveCode conf]),
      { S with clock := S.clock + a }) = (none, M))
    (hr : evaluate (listSeqHOL (fullRootsPrepareCode conf ++
      [wordGenGcMoveRootsBitmapsCode conf]),
      { M with clock := M.clock + b }) = (none, R))
    (hl : evaluate (listSeqHOL (fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]),
      { R with clock := R.clock + c }) = (none, L))
    (hu : evaluate (listSeqHOL tail, { L with clock := L.clock + d }) = (r, U)) :
    evaluate (listSeqHOL ((fullSetupCode ++ [wordGenGcMoveCode conf]) ++
      ((fullRootsPrepareCode conf ++ [wordGenGcMoveRootsBitmapsCode conf]) ++
      ((fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]) ++ tail))),
      { S with clock := S.clock + (a + (b + (c + d))) }) = (r, U) := by
  have hlt := evaluate_full_collector_clocks_result
    (fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]) tail
    (by simp) htail R L U c d r
    (fun x hx V => full_loop_prefix_clock conf x hx V) hlclock hl hu
  have hrt := evaluate_full_collector_clocks_result
    (fullRootsPrepareCode conf ++ [wordGenGcMoveRootsBitmapsCode conf])
    ((fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]) ++ tail)
    (by simp) (by simp) M R U b (c + d) r
    (fun x hx V => full_roots_prefix_clock conf x hx V) hrclock hr hlt
  exact evaluate_full_collector_clocks_result
    (fullSetupCode ++ [wordGenGcMoveCode conf])
    ((fullRootsPrepareCode conf ++ [wordGenGcMoveRootsBitmapsCode conf]) ++
      ((fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]) ++ tail))
    (by simp) (by simp) S M U a (b + (c + d)) r
    (fun x hx V => full_move_prefix_clock conf x hx V) hmclock hm hrt

/-- Constructive full loop list execution directly from the concrete roots
output, including all original entry instructions. -/
theorem evaluate_full_loop_list_after_roots {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w len other moved curr i0 pa0 ib0 pb0 i pa ib pb i1 pa1 ib1 pb1 : BitVec width}
    {ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 : WordLocW width}
    {m0 m m1 : BitVec width → WordLocW width} {roots : List (WordLocW width)}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMoveLoop conf (len >>> wordShiftAmount width).toNat
      (other, i, pa, ib, pb, other + len, curr, m, s.mdomain) =
      (i1, pa1, ib1, pb1, m1, true))
    (hu : s.useStore = true) (hc : s.store.lookup .currHeap = some (.word curr))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hls : conf.lenSize + 2 < width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let R := fullRootsOutputState conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
      ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 m0 m roots s
    let S := fullLoopSetupState pa pb other (other + len) R
    ∃ ck v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6,
      evaluate (listSeqHOL (fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]),
        { R with clock := R.clock + ck }) =
        (none, { S with
          memory := m1
          store := S.store.updateListEq [(.temp 0, z0), (.temp 1, z1),
            (.temp 2, .word pb1), (.temp 3, .word ib1), (.temp 4, z4),
            (.temp 5, z5), (.temp 6, z6)]
          regs := S.regs.updateListEq [(0, v0), (1, v1), (2, v2), (3, .word pa1),
            (4, .word i1), (5, v5), (6, v6), (7, v7), (8, v8)] }) := by
  dsimp only
  apply evaluate_full_loop_with_prefix
  · exact hm
  all_goals first | assumption | simp [fullRootsOutputState, fullRootsInputState, fullRootsSetupState,
    fullSetupState, setVar, setStore, HolFiniteMapExact.lookup_updateListEq,
    FUPDATE_LIST_HOL, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    hu, BitVec.add_comm]

/-- Complete loop output carrier. Only the original loop's listed temporary
and register fields change; allocation metadata is retained for cleanup. -/
noncomputable def fullLoopOutputState {width : Nat} [NeZero width] {C F : Type}
    (i pa ib pb : BitVec width)
    (v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 : WordLocW width)
    (m : BitVec width → WordLocW width)
    (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  { s with
    memory := m
    store := s.store.updateListEq [(.temp 0, z0), (.temp 1, z1),
      (.temp 2, .word pb), (.temp 3, .word ib), (.temp 4, z4),
      (.temp 5, z5), (.temp 6, z6)]
    regs := s.regs.updateListEq [(0, v0), (1, v1), (2, v2), (3, .word pa),
      (4, .word i), (5, v5), (6, v6), (7, v7), (8, v8)] }

/-- Every original cleanup input survives the loop output except the documented
new progress pointer and Temp2 boundary. This is update infrastructure, with
no separately named HOL original. -/
theorem full_loop_output_cleanup_inputs {width : Nat} [NeZero width] {C F : Type}
    (i pa ib pb : BitVec width)
    (v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 : WordLocW width)
    (m : BitVec width → WordLocW width)
    (s : StackSemStateFiniteExact width C F) :
    let L := fullLoopOutputState i pa ib pb v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 m s
    L.useStore = s.useStore ∧ L.clock = s.clock ∧
    L.store.lookup .currHeap = s.store.lookup .currHeap ∧
    L.store.lookup .otherHeap = s.store.lookup .otherHeap ∧
    L.store.lookup .nextFree = s.store.lookup .nextFree ∧
    L.store.lookup .allocSize = s.store.lookup .allocSize ∧
    L.store.lookup (.temp 2) = some (.word pb) ∧
    L.regs.lookup 3 = some (.word pa) := by
  simp [fullLoopOutputState, HolFiniteMapExact.lookup_updateListEq,
    FUPDATE_LIST_HOL, FUPDATE_HOL]

/-- Original full cleanup executed on the concrete loop output. The source
metadata supplies all premises; no successful tail execution is assumed. -/
theorem evaluate_full_cleanup_after_loop {width : Nat} [NeZero width] {C F : Type}
    {curr other pa pb w : BitVec width} {ret : WordLocW width}
    (genSizes : List Nat) (i ib : BitVec width)
    (v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 : WordLocW width)
    (m : BitVec width → WordLocW width)
    (s : StackSemStateFiniteExact width C F)
    (hg : goodDimindex width) (hu : s.useStore = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hr : s.store.lookup .nextFree = some ret)
    (hw : s.store.lookup .allocSize = some (.word w)) :
    let L := fullLoopOutputState i pa ib pb v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 m s
    let S := fullCleanupState curr other pa pb ret L
    ∃ r7 r1 r4,
      let T := { S with
        regs := ((S.regs.updateEq (1, r1)).updateEq (7, r7)).updateEq (4, r4)
        store := S.store.updateEq (.triggerGC, .word (pa + newTrig (pb - pa) w genSizes)) }
      let C := fullClearState T
      let trigger := pa + newTrig (pb - pa) w genSizes
      let V := setVar 2 (.word (trigger - pa)) (setVar 2 (.word trigger)
        (setVar 1 (.word w) C))
      evaluate (listSeqHOL ([.get 0 .currHeap, .get 1 .otherHeap, .get 2 (.temp 2),
        .set .currHeap 1, .set .otherHeap 0, .get 0 .nextFree, .set .nextFree 3,
        .set .endOfHeap 2, moveHOL 8 3, subInst 8 1, .set .genStart 8] ++
        [setNewTrigger 2 3 genSizes] ++
        [constInst 1 0, .set (.temp 0) 1, .set (.temp 1) 1, .set (.temp 2) 1,
          .set (.temp 3) 1, .set (.temp 4) 1, .set (.temp 5) 1, .set (.temp 6) 1] ++
        [.get 1 .allocSize, .get 2 .triggerGC, subInst 2 3] ++
        [.ite .lower 2 (.reg 1) (.seq (constInst 1 1) (.halt 1)) .skip]), L) =
        if (trigger - pa).toNat < w.toNat then
          (some (.halt (.word 1)), emptyEnv C) else (none, V) := by
  dsimp only
  apply evaluate_full_trigger_cleanup
  · exact hg
  all_goals simp [fullLoopOutputState, HolFiniteMapExact.lookup_updateListEq,
    FUPDATE_LIST_HOL, FUPDATE_HOL, hu, hc, ho, hr, hw]

/-- Original full collector store update order agrees with the source's final
heap swap and seven cleared temporaries. Intermediate collector scratch values
are arbitrary because every scratch field is overwritten before return. -/
theorem full_store_updates {width : Nat} [NeZero width]
    (f : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (w curr other pa pb newEnd len ib1 pb1 ib3 ib2 pb2 : BitVec width)
    (ret root gr t0 t1 u0 u1 z0 z1 z4 z5 z6 : WordLocW width)
    (space : BitVec width) :
    f.updateListEq [(.allocSize, .word w), (.nextFree, ret),
      (.temp 0, .word newEnd), (.temp 1, .word newEnd), (.temp 2, .word newEnd),
      (.temp 4, .word newEnd), (.temp 5, .word newEnd), (.temp 6, .word newEnd),
      (.temp 3, .word len),
      (.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb1), (.temp 3, .word ib1),
      (.globals, root), (.globReal, gr),
      (.temp 0, u0), (.temp 1, u1), (.temp 2, .word pb2), (.temp 3, .word ib2),
      (.temp 0, z0), (.temp 1, z1), (.temp 2, .word pb), (.temp 3, .word ib3),
      (.temp 4, z4), (.temp 5, z5), (.temp 6, z6),
      (.currHeap, .word other), (.otherHeap, .word curr),
      (.nextFree, .word pa), (.endOfHeap, .word pb), (.genStart, .word (pa - other)),
      (.triggerGC, .word (pa + space)),
      (.temp 0, .word 0), (.temp 1, .word 0), (.temp 2, .word 0),
      (.temp 3, .word 0), (.temp 4, .word 0), (.temp 5, .word 0), (.temp 6, .word 0)] =
    (f.updateEq (.allocSize, .word w)).updateListEq
      [(.currHeap, .word other), (.otherHeap, .word curr),
       (.nextFree, .word pa), (.genStart, .word (pa - other)),
       (.triggerGC, .word (pa + space)), (.endOfHeap, .word pb),
       (.globals, root), (.globReal, gr),
       (.temp 0, .word 0), (.temp 1, .word 0), (.temp 2, .word 0),
       (.temp 3, .word 0), (.temp 4, .word 0), (.temp 5, .word 0), (.temp 6, .word 0)] := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  cases key
  case temp n =>
    by_cases h0 : n = 0
    · subst n
      simp [HolFiniteMapExact.lookup_updateListEq,
        FUPDATE_LIST_HOL, FUPDATE_HOL]
    by_cases h1 : n = 1
    · subst n
      simp [HolFiniteMapExact.lookup_updateListEq,
        FUPDATE_LIST_HOL, FUPDATE_HOL]
    by_cases h2 : n = 2
    · subst n
      simp [HolFiniteMapExact.lookup_updateListEq,
        FUPDATE_LIST_HOL, FUPDATE_HOL]
    by_cases h3 : n = 3
    · subst n
      simp [HolFiniteMapExact.lookup_updateListEq,
        FUPDATE_LIST_HOL, FUPDATE_HOL]
    by_cases h4 : n = 4
    · subst n
      simp [HolFiniteMapExact.lookup_updateListEq,
        FUPDATE_LIST_HOL, FUPDATE_HOL]
    by_cases h5 : n = 5
    · subst n
      simp [HolFiniteMapExact.lookup_updateListEq,
        FUPDATE_LIST_HOL, FUPDATE_HOL]
    by_cases h6 : n = 6
    · subst n
      simp [HolFiniteMapExact.lookup_updateListEq,
        FUPDATE_LIST_HOL, FUPDATE_HOL]
    simp at h0 h1 h2 h3 h4 h5 h6
    simp [HolFiniteMapExact.lookup_updateListEq, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_LIST_HOL, FUPDATE_HOL, h0, h1, h2, h3, h4, h5, h6]
  all_goals simp [HolFiniteMapExact.lookup_updateListEq, HolFiniteMapExact.lookup_updateEq,
    FUPDATE_LIST_HOL, FUPDATE_HOL]

set_option maxRecDepth 2048 in
/-- The actual full execution carrier's final store matches the source full
collector store, including the original GlobReal word-address calculation. -/
theorem full_final_store {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (genSizes : List Nat)
    (w len curr other moved i0 pa0 ib0 pb0 i pa ib pb i3 pa3 ib3 pb3 : BitVec width)
    (ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1
      v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 : WordLocW width)
    (m0 m m3 : BitVec width → WordLocW width) (roots : List (WordLocW width))
    (s : StackSemStateFiniteExact width C F) :
    let R := fullRootsOutputState conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
      ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 m0 m roots s
    let L := fullLoopOutputState i3 pa3 ib3 pb3
      v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 m3
      (fullLoopSetupState pa pb other (other + len) R)
    let S := fullCleanupState curr other pa3 pb3 ret L
    (fullClearState { S with
      store := S.store.updateEq (.triggerGC,
        .word (pa3 + newTrig (pb3 - pa3) w genSizes)) }).store =
    (s.store.updateEq (.allocSize, .word w)).updateListEq
      [(.currHeap, .word other), (.otherHeap, .word curr),
       (.nextFree, .word pa3), (.genStart, .word (pa3 - other)),
       (.triggerGC, .word (pa3 + newTrig (pb3 - pa3) w genSizes)),
       (.endOfHeap, .word pb3), (.globals, .word moved),
       (.globReal, globReal conf other (.word moved)),
       (.temp 0, .word 0), (.temp 1, .word 0), (.temp 2, .word 0),
       (.temp 3, .word 0), (.temp 4, .word 0), (.temp 5, .word 0), (.temp 6, .word 0)] := by
  dsimp only
  rw [AllocGenerationalPartial.partial_global_real]
  have h := full_store_updates s.store w curr other pa3 pb3 (len + other)
    (len >>> wordShiftAmount width) ib0 pb0 ib3 ib pb ret (.word moved)
    (.word ((moved >>> shiftLength conf <<< wordShiftAmount width) + other))
    t0 t1 u0 u1 z0 z1 z4 z5 z6 (newTrig (pb3 - pa3) w genSizes)
  simpa only [fullClearState, fullCleanupState, fullLoopOutputState,
    fullLoopSetupState, fullRootsOutputState, fullRootsInputState,
    fullRootsSetupState, fullSetupState, setVar, setStore,
    HolFiniteMapExact.updateListEq, HolFiniteMapExact.updateEq,
    FUPDATE_LIST_HOL, List.foldl_cons, List.foldl_nil] using h

/-- A word global remains a word through every exact full move branch,
including forwarding, reference copying and data copying. Flapjack
infrastructure derived directly from the original executable definition. -/
theorem full_move_preserves_word {width : Nat} [NeZero width]
    (conf : Config) (root i pa ib pb curr : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) :
    wordSemIsWordLoc (wordGenGcMove conf (.word root, i, pa, ib, pb, curr, m, dm)).1 = true := by
  simp only [wordGenGcMove]
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- Recover the concrete word needed by the original globals shifts from the
source move equation; no target execution or word-shaped output is assumed. -/
theorem full_move_output_word {width : Nat} [NeZero width]
    {conf : Config} {root i pa ib pb curr i1 pa1 ib1 pb1 : BitVec width}
    {m m1 : BitVec width → WordLocW width} {dm : BitVec width → Bool}
    {moved : WordLocW width} {ok : Bool}
    (hm : wordGenGcMove conf (.word root, i, pa, ib, pb, curr, m, dm) =
      (moved, i1, pa1, ib1, pb1, m1, ok)) :
    ∃ w : BitVec width, moved = .word w := by
  have hw := full_move_preserves_word conf root i pa ib pb curr m dm
  rw [hm] at hw
  cases moved with
  | word w => exact ⟨w, rfl⟩
  | loc a b => simp [wordSemIsWordLoc] at hw

/-- Literal original full collector suffix, after the loop collector. -/
def fullTailCode {width : Nat} [NeZero width] (genSizes : List Nat) : List (HolProg width) :=
  [.get 0 .currHeap, .get 1 .otherHeap, .get 2 (.temp 2),
    .set .currHeap 1, .set .otherHeap 0, .get 0 .nextFree, .set .nextFree 3,
    .set .endOfHeap 2, moveHOL 8 3, subInst 8 1, .set .genStart 8] ++
  [setNewTrigger 2 3 genSizes] ++
  [constInst 1 0, .set (.temp 0) 1, .set (.temp 1) 1, .set (.temp 2) 1,
    .set (.temp 3) 1, .set (.temp 4) 1, .set (.temp 5) 1, .set (.temp 6) 1] ++
  [.get 1 .allocSize, .get 2 .triggerGC, subInst 2 3] ++
  [.ite .lower 2 (.reg 1) (.seq (constInst 1 1) (.halt 1)) .skip]

/-- Original full collector instruction list, split only at the original three
collector calls for clock composition. Compared with stack_allocScript.sml
568-634; this abbreviation has no separately named HOL original. -/
def fullProgramCode {width : Nat} [NeZero width] (conf : Config)
    (genSizes : List Nat) : List (HolProg width) :=
  (fullSetupCode ++ [wordGenGcMoveCode conf]) ++
    ((fullRootsPrepareCode conf ++ [wordGenGcMoveRootsBitmapsCode conf]) ++
      ((fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]) ++ fullTailCode genSizes))

/-- Construct the original setup, globals move and roots collection as one
actual program from their source equations. No target stage is assumed. -/
theorem evaluate_full_move_roots {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w len other moved curr i0 pa0 ib0 pb0 i pa ib pb : BitVec width}
    {ret glob : WordLocW width}
    {m0 m : BitVec width → WordLocW width} {roots : List (WordLocW width)}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMove conf (glob, 0, other, len >>> wordShiftAmount width,
      other + len, curr, s.memory, s.mdomain) = (.word moved, i0, pa0, ib0, pb0, m0, true))
    (hrts : wordGenGcMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i0, pa0, ib0, pb0, curr, m0, s.mdomain) =
      (roots, i, pa, ib, pb, m, true))
    (hu : s.useStore = true) (hus : s.useStack = true)
    (hr : s.regs.lookup 0 = some ret) (hw : s.regs.lookup 1 = some (.word w))
    (hl : s.store.lookup .heapLength = some (.word len))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hglob : s.store.lookup .globals = some glob)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    ∃ ck q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1,
      evaluate (listSeqHOL ((fullSetupCode ++ [wordGenGcMoveCode conf]) ++
        (fullRootsPrepareCode conf ++ [wordGenGcMoveRootsBitmapsCode conf])),
        { s with clock := s.clock + ck }) =
      (none, fullRootsOutputState conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
        ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 m0 m roots s) := by
  obtain ⟨a, q0, q1, q2, q6, t0, t1, hmove⟩ :=
    evaluate_full_move_with_prefix s hu hr hw hl ho hglob hc hm hsl hws hw2 hlen hshift
  obtain ⟨b, r0, r1, r2, r5, r6, r7, r8, u0, u1, hroots⟩ :=
    evaluate_full_roots_with_prefix (w := w) (len := len) (moved := moved)
      (ret := ret) (glob := glob) (q0 := q0) (q1 := q1) (q2 := q2)
      (q6 := q6) (t0 := t0) (t1 := t1)
      s hrts hu hus hc ho hb hs hsl hws hw2 hlen hg hshift
  let B := fullSetupState w len other ret glob s
  let M := { B with
    memory := m0
    store := B.store.updateListEq [(.temp 0, t0), (.temp 1, t1),
      (.temp 2, .word pb0), (.temp 3, .word ib0)]
    regs := B.regs.updateListEq [(0, q0), (1, q1), (2, q2),
      (3, .word pa0), (4, .word i0), (5, .word moved), (6, q6)] }
  refine ⟨a + b, q0, q1, q2, q6, t0, t1, r0, r1, r2, r5, r6, r7, r8, u0, u1, ?_⟩
  apply evaluate_full_collector_clocks_result
    (fullSetupCode ++ [wordGenGcMoveCode conf])
    (fullRootsPrepareCode conf ++ [wordGenGcMoveRootsBitmapsCode conf])
    (by simp) (by simp) s M _ a b none
  · exact fun x hx V => full_move_prefix_clock conf x hx V
  · rfl
  · exact hmove
  · simpa only [fullRootsOutputState] using hroots

/-- Construct the original full loop and complete cleanup suffix directly
from the roots output and source loop equation, including the Halt branch. -/
theorem evaluate_full_loop_tail_after_roots {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w len other moved curr i0 pa0 ib0 pb0 i pa ib pb i1 pa1 ib1 pb1 : BitVec width}
    {ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 : WordLocW width}
    {m0 m m1 : BitVec width → WordLocW width} {roots : List (WordLocW width)}
    (genSizes : List Nat) (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMoveLoop conf (len >>> wordShiftAmount width).toNat
      (other, i, pa, ib, pb, other + len, curr, m, s.mdomain) =
      (i1, pa1, ib1, pb1, m1, true))
    (hu : s.useStore = true) (hc : s.store.lookup .currHeap = some (.word curr))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hg : goodDimindex width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hls : conf.lenSize + 2 < width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let R := fullRootsOutputState conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
      ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 m0 m roots s
    ∃ ck v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 p7 p1 p4,
      let L := fullLoopOutputState i1 pa1 ib1 pb1
        v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 m1
        (fullLoopSetupState pa pb other (other + len) R)
      let S := fullCleanupState curr other pa1 pb1 ret L
      let T := { S with
        regs := ((S.regs.updateEq (1, p1)).updateEq (7, p7)).updateEq (4, p4)
        store := S.store.updateEq (.triggerGC, .word (pa1 + newTrig (pb1 - pa1) w genSizes)) }
      let C := fullClearState T
      let trigger := pa1 + newTrig (pb1 - pa1) w genSizes
      let V := setVar 2 (.word (trigger - pa1)) (setVar 2 (.word trigger)
        (setVar 1 (.word w) C))
      evaluate (listSeqHOL ((fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]) ++
        fullTailCode genSizes), { R with clock := R.clock + ck }) =
        if (trigger - pa1).toNat < w.toNat then
          (some (.halt (.word 1)), emptyEnv C) else (none, V) := by
  dsimp only
  let R := fullRootsOutputState conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
    ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 m0 m roots s
  let B := fullLoopSetupState pa pb other (other + len) R
  obtain ⟨ck, v0, v1, v2, v5, v6, v7, v8, z0, z1, z4, z5, z6, hloop⟩ :=
    evaluate_full_loop_list_after_roots (w := w) (moved := moved)
      (i0 := i0) (pa0 := pa0) (ib0 := ib0) (pb0 := pb0)
      (ret := ret) (glob := glob) (q0 := q0) (q1 := q1) (q2 := q2) (q6 := q6)
      (t0 := t0) (t1 := t1) (r0 := r0) (r1 := r1) (r2 := r2) (r5 := r5)
      (r6 := r6) (r7 := r7) (r8 := r8) (u0 := u0) (u1 := u1) (m0 := m0)
      (roots := roots) s hm hu hc ho hsl hws hw2 hlen hls hshift
  obtain ⟨p7, p1, p4, htail⟩ := evaluate_full_cleanup_after_loop
    (curr := curr) (other := other) (pa := pa1) (pb := pb1) (w := w) (ret := ret)
    genSizes i1 ib1 v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 m1 B hg
    (by simpa [B, R, fullLoopSetupState, fullRootsOutputState, fullRootsInputState,
      fullRootsSetupState, fullSetupState, setVar, setStore] using hu)
    (by simpa [B, R, fullLoopSetupState, fullRootsOutputState, fullRootsInputState,
      fullRootsSetupState, fullSetupState, setVar, setStore,
      HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hc)
    (by simpa [B, R, fullLoopSetupState, fullRootsOutputState, fullRootsInputState,
      fullRootsSetupState, fullSetupState, setVar, setStore,
      HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using ho)
    (by simp [B, R, fullLoopSetupState, fullRootsOutputState, fullRootsInputState,
      fullRootsSetupState, fullSetupState, setVar, setStore,
      HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
    (by simp [B, R, fullLoopSetupState, fullRootsOutputState, fullRootsInputState,
      fullRootsSetupState, fullSetupState, setVar, setStore,
      HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
  refine ⟨ck, v0, v1, v2, v5, v6, v7, v8, z0, z1, z4, z5, z6, p7, p1, p4, ?_⟩
  let L := fullLoopOutputState i1 pa1 ib1 pb1
    v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 m1 B
  have hloop' : evaluate (listSeqHOL (fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]),
    { R with clock := R.clock + ck }) = (none, L) := hloop
  rw [AllocGenerationalPartial.evaluate_listSeq_append_collector
    (fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]) (fullTailCode genSizes)
    _ L (by simp) (by simp [fullTailCode])
    (fun x hx V => full_loop_prefix_clock conf x hx V)
    (by simp [L, B, fullLoopOutputState, fullLoopSetupState, setVar]) hloop']
  simpa only [fullTailCode, L, B, R] using htail

/-- Pair-valued version of checked collector clock composition, retaining a
conditional normal/Halt outcome without prematurely choosing either branch.
This is untagged execution-composition infrastructure. -/
theorem evaluate_full_collector_clocks_pair {width : Nat} [NeZero width] {C F : Type}
    (xs ys : List (HolProg width)) (hx : xs ≠ []) (hy : ys ≠ [])
    (S T : StackSemStateFiniteExact width C F) (a b : Nat)
    (outcome : Option (StackSemResult width) × StackSemStateFiniteExact width C F)
    (hcl : ∀ x ∈ xs.dropLast, ∀ V : StackSemStateFiniteExact width C F,
      (evaluate (x, V)).2.clock = V.clock)
    (hclock : T.clock = S.clock)
    (hp : evaluate (listSeqHOL xs, { S with clock := S.clock + a }) = (none, T))
    (hq : evaluate (listSeqHOL ys, { T with clock := T.clock + b }) = outcome) :
    evaluate (listSeqHOL (xs ++ ys), { S with clock := S.clock + (a + b) }) = outcome := by
  rcases outcome with ⟨r, U⟩
  exact evaluate_full_collector_clocks_result xs ys hx hy S T U a b r hcl hclock hp hq

/-- Construct execution of the complete original full collector program
from the three source collector equations, retaining the complete normal/Halt
outcome and all existential register and clock values. -/
theorem evaluate_full_program {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w len other moved curr i0 pa0 ib0 pb0 i pa ib pb i3 pa3 ib3 pb3 : BitVec width}
    {ret glob : WordLocW width}
    {m0 m m3 : BitVec width → WordLocW width} {roots : List (WordLocW width)}
    (genSizes : List Nat) (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMove conf (glob, 0, other, len >>> wordShiftAmount width,
      other + len, curr, s.memory, s.mdomain) = (.word moved, i0, pa0, ib0, pb0, m0, true))
    (hrts : wordGenGcMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i0, pa0, ib0, pb0, curr, m0, s.mdomain) =
      (roots, i, pa, ib, pb, m, true))
    (hloop : wordGenGcMoveLoop conf (len >>> wordShiftAmount width).toNat
      (other, i, pa, ib, pb, other + len, curr, m, s.mdomain) =
      (i3, pa3, ib3, pb3, m3, true))
    (hu : s.useStore = true) (hus : s.useStack = true)
    (hr : s.regs.lookup 0 = some ret) (hw : s.regs.lookup 1 = some (.word w))
    (hl : s.store.lookup .heapLength = some (.word len))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hglob : s.store.lookup .globals = some glob)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hls : conf.lenSize + 2 < width) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    ∃ ck q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1,
      let R := fullRootsOutputState conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
        ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 m0 m roots s
      ∃ v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 p7 p1 p4,
      let L := fullLoopOutputState i3 pa3 ib3 pb3
        v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 m3
        (fullLoopSetupState pa pb other (other + len) R)
      let S := fullCleanupState curr other pa3 pb3 ret L
      let T := { S with
        regs := ((S.regs.updateEq (1, p1)).updateEq (7, p7)).updateEq (4, p4)
        store := S.store.updateEq (.triggerGC, .word (pa3 + newTrig (pb3 - pa3) w genSizes)) }
      let C := fullClearState T
      let trigger := pa3 + newTrig (pb3 - pa3) w genSizes
      let V := setVar 2 (.word (trigger - pa3)) (setVar 2 (.word trigger)
        (setVar 1 (.word w) C))
      evaluate (listSeqHOL (fullProgramCode conf genSizes),
        { s with clock := s.clock + ck }) =
        if (trigger - pa3).toNat < w.toNat then
          (some (.halt (.word 1)), emptyEnv C) else (none, V) := by
  obtain ⟨a, q0, q1, q2, q6, t0, t1, hmove⟩ :=
    evaluate_full_move_with_prefix s hu hr hw hl ho hglob hc hm hsl hws hw2 hlen hshift
  obtain ⟨b, r0, r1, r2, r5, r6, r7, r8, u0, u1, hroots⟩ :=
    evaluate_full_roots_with_prefix (w := w) (len := len) (moved := moved)
      (ret := ret) (glob := glob) (q0 := q0) (q1 := q1) (q2 := q2)
      (q6 := q6) (t0 := t0) (t1 := t1)
      s hrts hu hus hc ho hb hs hsl hws hw2 hlen hg hshift
  let B := fullSetupState w len other ret glob s
  let M := { B with
    memory := m0
    store := B.store.updateListEq [(.temp 0, t0), (.temp 1, t1),
      (.temp 2, .word pb0), (.temp 3, .word ib0)]
    regs := B.regs.updateListEq [(0, q0), (1, q1), (2, q2),
      (3, .word pa0), (4, .word i0), (5, .word moved), (6, q6)] }
  let R := fullRootsOutputState conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
    ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 m0 m roots s
  obtain ⟨c, v0, v1, v2, v5, v6, v7, v8, z0, z1, z4, z5, z6, p7, p1, p4, htail⟩ :=
    evaluate_full_loop_tail_after_roots (w := w) (moved := moved)
      (i0 := i0) (pa0 := pa0) (ib0 := ib0) (pb0 := pb0)
      (ret := ret) (glob := glob) (q0 := q0) (q1 := q1) (q2 := q2) (q6 := q6)
      (t0 := t0) (t1 := t1) (r0 := r0) (r1 := r1) (r2 := r2) (r5 := r5)
      (r6 := r6) (r7 := r7) (r8 := r8) (u0 := u0) (u1 := u1) (m0 := m0)
      (roots := roots) genSizes s hloop hu hc ho hg hsl hws hw2 hlen hls hshift
  refine ⟨a + (b + c), q0, q1, q2, q6, t0, t1, r0, r1, r2, r5, r6, r7, r8, u0, u1,
    v0, v1, v2, v5, v6, v7, v8, z0, z1, z4, z5, z6, p7, p1, p4, ?_⟩
  dsimp only
  unfold fullProgramCode
  apply evaluate_full_collector_clocks_pair
    (fullSetupCode ++ [wordGenGcMoveCode conf])
    ((fullRootsPrepareCode conf ++ [wordGenGcMoveRootsBitmapsCode conf]) ++
      ((fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]) ++ fullTailCode genSizes))
    (by simp) (by simp) s M a (b + c)
  · exact fun x hx V => full_move_prefix_clock conf x hx V
  · rfl
  · exact hmove
  · apply evaluate_full_collector_clocks_pair
      (fullRootsPrepareCode conf ++ [wordGenGcMoveRootsBitmapsCode conf])
      ((fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]) ++ fullTailCode genSizes)
      (by simp) (by simp) M R b c
    · exact fun x hx V => full_roots_prefix_clock conf x hx V
    · rfl
    · exact hroots
    · exact htail

/-- The original full cleanup restores register zero before trigger and
allocation checks. All later register changes are disjoint from zero. -/
theorem full_final_return_register {width : Nat} [NeZero width] {C F : Type}
    (curr other pa pb w trigger : BitVec width) (ret p1 p7 p4 : WordLocW width)
    (s : StackSemStateFiniteExact width C F) :
    let S := fullCleanupState curr other pa pb ret s
    let T := { S with
      regs := ((S.regs.updateEq (1, p1)).updateEq (7, p7)).updateEq (4, p4)
      store := S.store.updateEq (.triggerGC, .word trigger) }
    let C := fullClearState T
    let V := setVar 2 (.word (trigger - pa)) (setVar 2 (.word trigger)
      (setVar 1 (.word w) C))
    V.regs.lookup 0 = some ret := by
  simp [fullCleanupState, fullClearState, setVar, setStore,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- The normal full tail retains every non-register, non-store component of
its loop result. Its Halt path empties exactly the original stack/register
fields, preserving the clock and all allocation metadata. -/
theorem full_final_tail_components {width : Nat} [NeZero width] {C F : Type}
    (curr other pa pb w trigger : BitVec width) (ret p1 p7 p4 : WordLocW width)
    (s : StackSemStateFiniteExact width C F) :
    let S := fullCleanupState curr other pa pb ret s
    let T := { S with
      regs := ((S.regs.updateEq (1, p1)).updateEq (7, p7)).updateEq (4, p4)
      store := S.store.updateEq (.triggerGC, .word trigger) }
    let C := fullClearState T
    let V := setVar 2 (.word (trigger - pa)) (setVar 2 (.word trigger)
      (setVar 1 (.word w) C))
    V = { s with regs := V.regs, store := C.store } ∧
    emptyEnv C = emptyEnv { s with store := C.store } := by
  cases s
  constructor <;> rfl

/-- The three full collector stages change only memory, roots stack, store
and registers; the clock and all source/compiled-code override fields survive.
This complete record identity is infrastructure, not a weakened state relation. -/
theorem full_collector_components {width : Nat} [NeZero width] {C F : Type}
    (conf : Config)
    (w len other moved i0 pa0 ib0 pb0 i pa ib pb i3 pa3 ib3 pb3 : BitVec width)
    (ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1
      v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 : WordLocW width)
    (m0 m m3 : BitVec width → WordLocW width) (roots : List (WordLocW width))
    (s : StackSemStateFiniteExact width C F) :
    let R := fullRootsOutputState conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
      ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 m0 m roots s
    let L := fullLoopOutputState i3 pa3 ib3 pb3
      v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 m3
      (fullLoopSetupState pa pb other (other + len) R)
    L = { s with
      memory := m3
      stack := s.stack.take s.stackSpace ++ roots
      store := L.store
      regs := L.regs } := by
  cases s
  rfl

/-- Original source full-collector final store, used only as a local
abbreviation of the source update list. -/
noncomputable def fullSourceStore {width : Nat} [NeZero width] (conf : Config) (genSizes : List Nat)
    (w curr other moved pa pb : BitVec width)
    (f : HolFiniteMapExact WordStoreHOL (WordLocW width)) :
    HolFiniteMapExact WordStoreHOL (WordLocW width) :=
  (f.updateEq (.allocSize, .word w)).updateListEq
    [(.currHeap, .word other), (.otherHeap, .word curr),
     (.nextFree, .word pa), (.genStart, .word (pa - other)),
     (.triggerGC, .word (pa + newTrig (pb - pa) w genSizes)),
     (.endOfHeap, .word pb), (.globals, .word moved),
     (.globReal, globReal conf other (.word moved)),
     (.temp 0, .word 0), (.temp 1, .word 0), (.temp 2, .word 0),
     (.temp 3, .word 0), (.temp 4, .word 0), (.temp 5, .word 0), (.temp 6, .word 0)]

/-- Complete source-shaped final state of the original full program, with
normal return register restoration and exactly the original Halt emptyEnv.
No component of the final state relation is assumed. -/
theorem full_final_state {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (genSizes : List Nat)
    (w len curr other moved i0 pa0 ib0 pb0 i pa ib pb i3 pa3 ib3 pb3 : BitVec width)
    (ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1
      v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 p1 p7 p4 : WordLocW width)
    (m0 m m3 : BitVec width → WordLocW width) (roots : List (WordLocW width))
    (s : StackSemStateFiniteExact width C F) :
    let R := fullRootsOutputState conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
      ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 m0 m roots s
    let L := fullLoopOutputState i3 pa3 ib3 pb3
      v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 m3
      (fullLoopSetupState pa pb other (other + len) R)
    let S := fullCleanupState curr other pa3 pb3 ret L
    let trigger := pa3 + newTrig (pb3 - pa3) w genSizes
    let T := { S with
      regs := ((S.regs.updateEq (1, p1)).updateEq (7, p7)).updateEq (4, p4)
      store := S.store.updateEq (.triggerGC, .word trigger) }
    let C := fullClearState T
    let V := setVar 2 (.word (trigger - pa3)) (setVar 2 (.word trigger)
      (setVar 1 (.word w) C))
    let source := { s with
      memory := m3
      stack := s.stack.take s.stackSpace ++ roots
      store := fullSourceStore conf genSizes w curr other moved pa3 pb3 s.store }
    V = { source with regs := V.regs } ∧
      emptyEnv C = emptyEnv source ∧ V.regs.lookup 0 = some ret := by
  let R := fullRootsOutputState conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
    ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 m0 m roots s
  let L := fullLoopOutputState i3 pa3 ib3 pb3
    v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 m3
    (fullLoopSetupState pa pb other (other + len) R)
  let S := fullCleanupState curr other pa3 pb3 ret L
  let trigger := pa3 + newTrig (pb3 - pa3) w genSizes
  let T := { S with
    regs := ((S.regs.updateEq (1, p1)).updateEq (7, p7)).updateEq (4, p4)
    store := S.store.updateEq (.triggerGC, .word trigger) }
  let C := fullClearState T
  let V := setVar 2 (.word (trigger - pa3)) (setVar 2 (.word trigger)
    (setVar 1 (.word w) C))
  let source := { s with
    memory := m3
    stack := s.stack.take s.stackSpace ++ roots
    store := fullSourceStore conf genSizes w curr other moved pa3 pb3 s.store }
  change V = { source with regs := V.regs } ∧ emptyEnv C = emptyEnv source ∧
    V.regs.lookup 0 = some ret
  have hL : L = { s with
      memory := m3
      stack := s.stack.take s.stackSpace ++ roots
      store := L.store
      regs := L.regs } :=
    full_collector_components conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
      i3 pa3 ib3 pb3 ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1
      v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 m0 m m3 roots s
  have hstore : C.store = fullSourceStore conf genSizes w curr other moved pa3 pb3 s.store :=
    full_final_store conf genSizes w len curr other moved
      i0 pa0 ib0 pb0 i pa ib pb i3 pa3 ib3 pb3
      ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1
      v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 m0 m m3 roots s
  have htail : V = { L with regs := V.regs, store := C.store } ∧
      emptyEnv C = emptyEnv { L with store := C.store } :=
    full_final_tail_components curr other pa3 pb3 w trigger ret p1 p7 p4 L
  refine ⟨?_, ?_, ?_⟩
  · calc
      V = { L with regs := V.regs, store := C.store } := htail.1
      _ = { source with regs := V.regs } := by rw [hstore, hL]
  · calc
      emptyEnv C = emptyEnv { L with store := C.store } := htail.2
      _ = emptyEnv source := by rw [hstore, hL]; rfl
  · exact full_final_return_register curr other pa3 pb3 w trigger ret p1 p7 p4 L

/-- Complete four-conclusion allocation result for the literal full program.
The source stage equations are infrastructure inputs; the final HOL case
obtains them from the original non-error source allocation premise. -/
theorem evaluate_full_program_source_result {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w len other moved curr i0 pa0 ib0 pb0 i pa ib pb i3 pa3 ib3 pb3 : BitVec width}
    {ret glob : WordLocW width}
    {m0 m m3 : BitVec width → WordLocW width} {roots : List (WordLocW width)}
    (genSizes : List Nat) (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMove conf (glob, 0, other, len >>> wordShiftAmount width,
      other + len, curr, s.memory, s.mdomain) = (.word moved, i0, pa0, ib0, pb0, m0, true))
    (hrts : wordGenGcMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i0, pa0, ib0, pb0, curr, m0, s.mdomain) =
      (roots, i, pa, ib, pb, m, true))
    (hloop : wordGenGcMoveLoop conf (len >>> wordShiftAmount width).toNat
      (other, i, pa, ib, pb, other + len, curr, m, s.mdomain) =
      (i3, pa3, ib3, pb3, m3, true))
    (hu : s.useStore = true) (hus : s.useStack = true)
    (hr : s.regs.lookup 0 = some ret) (hw : s.regs.lookup 1 = some (.word w))
    (hl : s.store.lookup .heapLength = some (.word len))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hglob : s.store.lookup .globals = some glob)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hls : conf.lenSize + 2 < width) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let source := { s with
      memory := m3
      stack := s.stack.take s.stackSpace ++ roots
      store := fullSourceStore conf genSizes w curr other moved pa3 pb3 s.store
      regs := HolFiniteMapExact.empty }
    let short := ((pa3 + newTrig (pb3 - pa3) w genSizes) - pa3).toNat < w.toNat
    let result := if short then some (.halt (.word 1)) else none
    let target := if short then emptyEnv source else source
    ∃ ck l2,
      evaluate (listSeqHOL (fullProgramCode conf genSizes),
        { s with clock := s.clock + ck }) = (result, { target with regs := l2 }) ∧
      (result ≠ none → result = some (.halt (.word 1))) ∧
      target.regs.submap l2 ∧ (result = none → l2.lookup 0 = some ret) := by
  obtain ⟨ck, q0, q1, q2, q6, t0, t1, r0, r1, r2, r5, r6, r7, r8, u0, u1,
    v0, v1, v2, v5, v6, v7, v8, z0, z1, z4, z5, z6, p7, p1, p4, heval⟩ :=
    evaluate_full_program genSizes s hm hrts hloop hu hus hr hw hl ho hglob hc hb hs
      hsl hws hw2 hlen hls hg hshift
  let R := fullRootsOutputState conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
    ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 m0 m roots s
  let L := fullLoopOutputState i3 pa3 ib3 pb3
    v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 m3
    (fullLoopSetupState pa pb other (other + len) R)
  let S := fullCleanupState curr other pa3 pb3 ret L
  let trigger := pa3 + newTrig (pb3 - pa3) w genSizes
  let T := { S with
    regs := ((S.regs.updateEq (1, p1)).updateEq (7, p7)).updateEq (4, p4)
    store := S.store.updateEq (.triggerGC, .word trigger) }
  let C := fullClearState T
  let V := setVar 2 (.word (trigger - pa3)) (setVar 2 (.word trigger)
    (setVar 1 (.word w) C))
  let source := { s with
    memory := m3
    stack := s.stack.take s.stackSpace ++ roots
    store := fullSourceStore conf genSizes w curr other moved pa3 pb3 s.store
    regs := HolFiniteMapExact.empty }
  have hstate := full_final_state conf genSizes w len curr other moved
    i0 pa0 ib0 pb0 i pa ib pb i3 pa3 ib3 pb3
    ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1
    v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 p1 p7 p4 m0 m m3 roots s
  have hn : V = { source with regs := V.regs } := hstate.1
  have hh : emptyEnv C = emptyEnv source := hstate.2.1
  have hret : V.regs.lookup 0 = some ret := hstate.2.2
  have heval' : evaluate (listSeqHOL (fullProgramCode conf genSizes),
      { s with clock := s.clock + ck }) =
      if (trigger - pa3).toNat < w.toNat then
        (some (.halt (.word 1)), emptyEnv C) else (none, V) := heval
  dsimp only
  by_cases hshort : (trigger - pa3).toNat < w.toNat
  · simp only [trigger] at hshort heval'
    simp only [hshort, if_true] at heval' ⊢
    refine ⟨ck, HolFiniteMapExact.empty, ?_, by simp, ?_, by simp⟩
    · exact heval'.trans (congrArg (fun state => (some (StackSemResult.halt (WordLocW.word (1 : BitVec width))), state)) hh)
    · exact AllocGenerationalPartial.partial_empty_regs_submap _
  · simp only [trigger] at hshort heval'
    simp only [hshort, if_false] at heval' ⊢
    refine ⟨ck, V.regs, ?_, by simp, ?_, ?_⟩
    · exact heval'.trans (congrArg (fun state => ((none : Option (StackSemResult width)), state)) hn)
    · exact AllocGenerationalPartial.partial_empty_regs_submap _
    · exact fun _ => hret

/-- Derive full collector source equations, source-shaped post-state and exact
normal/Halt allocation outcome from the original non-error alloc premise.
No successful source collector or target execution premise is added. -/
theorem alloc_full_source_result {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {genSizes : List Nat} {w : BitVec width}
    {s t : StackSemStateFiniteExact width C F} {r : Option (StackSemResult width)}
    (ha : StackSemAllocation.alloc w s = (r, t)) (hn : r ≠ some .error)
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes)
    (hp : ¬wordGenGcCanDoPartial genSizes (setStore .allocSize (.word w) s).store) :
    let A := setStore .allocSize (.word w) s
    let curr := wordSemTheWord (holFapply A.store .currHeap)
    let other := wordSemTheWord (holFapply A.store .otherHeap)
    let len := wordSemTheWord (holFapply A.store .heapLength)
    ∃ moved i0 pa0 ib0 pb0 m0 roots i pa ib pb m i3 pa3 ib3 pb3 m3,
      wordGenGcMove conf (holFapply A.store .globals, 0, other,
        len >>> wordShiftAmount width, other + len, curr, s.memory, s.mdomain) =
        (.word moved, i0, pa0, ib0, pb0, m0, true) ∧
      wordGenGcMoveRootsBitmaps conf (s.stack.drop s.stackSpace, s.bitmaps,
        i0, pa0, ib0, pb0, curr, m0, s.mdomain) = (roots, i, pa, ib, pb, m, true) ∧
      wordGenGcMoveLoop conf (len >>> wordShiftAmount width).toNat
        (other, i, pa, ib, pb, other + len, curr, m, s.mdomain) =
        (i3, pa3, ib3, pb3, m3, true) ∧ wordGcFunAssum conf A.store ∧
      let collected := { s with
        stack := s.stack.take s.stackSpace ++ roots
        memory := m3
        store := fullSourceStore conf genSizes w curr other moved pa3 pb3 s.store
        regs := HolFiniteMapExact.empty }
      (r, t) = if ((pa3 + newTrig (pb3 - pa3) w genSizes) - pa3).toNat < w.toNat then
        (some (.halt (.word 1)), emptyEnv collected) else (none, collected) := by
  obtain ⟨collected, hcol, _⟩ := alloc_collector_result ha hn
  let A := setStore .allocSize (.word w) s
  obtain ⟨root, i0, pa0, ib0, pb0, m0, roots, i, pa, ib, pb, m,
    i3, pa3, ib3, pb3, m3, hm, hrts, hloop, hass, hfinal⟩ :=
    full_source_pipeline (s := A) hgc hk hp hcol
  obtain ⟨loads, _, _, _, _⟩ := AllocGenerationalPartial.partial_source_loads conf A.store hass
  have hglob := loads .globals (by simp)
  have hglob' : holFapply A.store .globals =
      .word (wordSemTheWord (holFapply A.store .globals)) := by
    conv_lhs => unfold holFapply; rw [hglob]
  rw [hglob'] at hm
  obtain ⟨moved, hword⟩ := full_move_output_word hm
  subst root
  let curr := wordSemTheWord (holFapply A.store .currHeap)
  let other := wordSemTheWord (holFapply A.store .otherHeap)
  have hfinal' : collected = { s with
      stack := s.stack.take s.stackSpace ++ roots
      memory := m3
      store := fullSourceStore conf genSizes w curr other moved pa3 pb3 s.store
      regs := HolFiniteMapExact.empty } := by
    simpa only [fullSourceStore, A, curr, other, setStore,
      holFapply, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
      if_true, Option.getD_some, wordSemTheWord] using hfinal
  have hresult := alloc_after_full_collection (pa := pa3)
    (trigger := pa3 + newTrig (pb3 - pa3) w genSizes) hcol
    (by rw [hfinal']; simp [fullSourceStore, HolFiniteMapExact.lookup_updateListEq,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by rw [hfinal']; simp [fullSourceStore, HolFiniteMapExact.lookup_updateListEq,
      FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by rw [hfinal']; simp [fullSourceStore, HolFiniteMapExact.lookup_updateListEq,
      FUPDATE_LIST_HOL, FUPDATE_HOL])
  refine ⟨moved, i0, pa0, ib0, pb0, m0, roots, i, pa, ib, pb, m,
    i3, pa3, ib3, pb3, m3, ?_, hrts, hloop, hass, ?_⟩
  · rw [← hglob'] at hm
    exact hm
  · rw [← ha, hresult, hfinal']

/-- Canonical codec for the actual imported owning StackSem carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Original full-selector case of alloc_correct_lemma_Generational.
Retains all original hypotheses and four conclusions; only the negated
original partial-selector condition selects this source proof case. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml"
  "alloc_correct_lemma_Generational"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem alloc_correct_lemma_Generational_full {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {genSizes : List Nat} {c : DataToWord.Config}
    {w : BitVec width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} {l : HolFiniteMapExact Nat (WordLocW width)}
    {ret : WordLocW width} {anything : WordSemGcFun width}
    (ha : StackSemAllocation.alloc w s = (r, t)) (hr : r ≠ some .error)
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes)
    (hbl : s.bitmaps.length < 2 ^ width - 1)
    (hstack : s.stack.length * (width / 8) < 2 ^ width)
    (hl0 : l.lookup 0 = some ret) (hl1 : l.lookup 1 = some (.word w))
    (hp : ¬wordGenGcCanDoPartial genSizes (setStore .allocSize (.word w) s).store) :
    ∃ ck l2,
      evaluate (wordGcCode conf, { s with
        useStore := true
        useStack := true
        useAlloc := false
        clock := s.clock + ck
        regs := l
        gcFun := anything
        code := sptFromAList (compile c (sptToAList s.code)) }) =
        (r, { t with
          useStore := true
          useStack := true
          useAlloc := false
          code := sptFromAList (compile c (sptToAList s.code))
          regs := l2
          gcFun := anything }) ∧
      (r ≠ none → r = some (.halt (.word 1))) ∧
      t.regs.submap l2 ∧ (r = none → l2.lookup 0 = some ret) := by
  let A := setStore .allocSize (.word w) s
  let curr := wordSemTheWord (holFapply A.store .currHeap)
  let other := wordSemTheWord (holFapply A.store .otherHeap)
  let len := wordSemTheWord (holFapply A.store .heapLength)
  let trig := wordSemTheWord (holFapply A.store .triggerGC)
  let endh := wordSemTheWord (holFapply A.store .endOfHeap)
  let globalWord := wordSemTheWord (holFapply A.store .globals)
  obtain ⟨moved, i0, pa0, ib0, pb0, m0, roots, i, pa, ib, pb, m,
    i3, pa3, ib3, pb3, m3, hm, hrts, hloop, hass, hsource⟩ :=
    alloc_full_source_result ha hr hgc hk hp
  obtain ⟨loads, hgood, hlen, hls, hsl⟩ := AllocGenerationalPartial.partial_source_loads conf A.store hass
  have load : ∀ key ∈ ([.globals, .currHeap, .otherHeap, .heapLength, .triggerGC,
      .genStart, .endOfHeap] : List WordStoreHOL),
      s.store.lookup key = some (.word (wordSemTheWord (holFapply A.store key))) := by
    intro key hkey
    have h := loads key hkey
    have hne : key ≠ .allocSize := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hkey
      rcases hkey with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [A, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hne] using h
  have hc := load .currHeap (by simp)
  have ho := load .otherHeap (by simp)
  have hl := load .heapLength (by simp)
  have ht := load .triggerGC (by simp)
  have he := load .endOfHeap (by simp)
  have hglob := load .globals (by simp)
  rw [holFapply_of_lookup (loads .globals (by simp))] at hm
  have hws : wordShiftAmount width < width := by
    unfold wordShiftAmount
    rcases hgood with h | h <;> simp [h]
  have hw2 : 2 < width := by rcases hgood with h | h <;> omega
  have hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord := by
    intro x
    rw [← bytesInWord_mul_eq_shift x hgood, BitVec.mul_comm]
  let R : StackSemStateFiniteExact width C F := { s with
    useStore := true
    useStack := true
    useAlloc := false
    regs := l
    gcFun := anything
    code := sptFromAList (compile c (sptToAList s.code)) }
  let P := setVar 7 (.word (endh - trig)) (setVar 7 (.word endh) (setVar 8 (.word trig) R))
  obtain ⟨ck, l2, hrun, hhalt, hsub, hret⟩ := evaluate_full_program_source_result genSizes P
    hm hrts hloop rfl rfl
    (by simpa [P, R, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hl0)
    (by simpa [P, R, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hl1)
    hl ho hglob hc hbl hstack hsl hws hw2 hlen hls hgood hshift
  dsimp only at hrun hhalt hsub hret hsource
  let short := ((pa3 + newTrig (pb3 - pa3) w genSizes) - pa3).toNat < w.toNat
  have hrResult : r = (if short then some (.halt (.word 1)) else none) := by
    by_cases h : short <;> simp only [short] at h ⊢ <;>
      simp only [h, if_true, if_false, Prod.mk.injEq] at hsource ⊢ <;> exact hsource.1
  have hstate : { (if short then emptyEnv { P with
        memory := m3
        stack := P.stack.take P.stackSpace ++ roots
        store := fullSourceStore conf genSizes w curr other moved pa3 pb3 P.store
        regs := HolFiniteMapExact.empty } else { P with
        memory := m3
        stack := P.stack.take P.stackSpace ++ roots
        store := fullSourceStore conf genSizes w curr other moved pa3 pb3 P.store
        regs := HolFiniteMapExact.empty }) with regs := l2 } =
      { t with
        useStore := true
        useStack := true
        useAlloc := false
        code := sptFromAList (compile c (sptToAList s.code))
        regs := l2
        gcFun := anything } := by
    by_cases h : short
    · simp only [short] at h
      simp only [h, if_true, Prod.mk.injEq] at hsource
      rw [hsource.2]
      simp only [short, h, if_true]
      rfl
    · simp only [short] at h
      simp only [h, if_false, Prod.mk.injEq] at hsource
      rw [hsource.2]
      simp only [short, h, if_false]
      rfl
  have htregs : t.regs = HolFiniteMapExact.empty := by
    by_cases h : short <;> simp only [short] at h <;>
      simp only [h, if_true, if_false, Prod.mk.injEq] at hsource <;>
      rw [hsource.2]
    all_goals rfl
  refine ⟨ck, l2, ?_, ?_, ?_, ?_⟩
  · simp only [wordGcCode, hk]
    rw [evaluate_full_select_from_source conf genSizes w _ _
      { R with clock := s.clock + ck } hass hp rfl hl1]
    rw [holFapply_of_lookup ht, holFapply_of_lookup he]
    simp only [wordSemTheWord]
    have hrunFinal := hrun.trans (congrArg
      (fun U => ((if short then some (StackSemResult.halt (WordLocW.word (1 : BitVec width))) else none), U)) hstate)
    rw [← hrResult] at hrunFinal
    simpa only [fullProgramCode, fullSetupCode, fullRootsPrepareCode,
      fullLoopPrepareCode, fullTailCode, List.cons_append, List.nil_append,
      P, R, setVar, trig, endh, wordSemTheWord] using hrunFinal
  · rw [hrResult]
    exact hhalt
  · rw [htregs]
    exact AllocGenerationalPartial.partial_empty_regs_submap _
  · rw [hrResult]
    exact hret

end Flapjack.Compiler.Backend.StackAlloc.AllocGenerationalFull

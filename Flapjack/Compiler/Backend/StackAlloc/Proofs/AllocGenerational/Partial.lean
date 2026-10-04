import Flapjack.Compiler.Backend.StackAlloc.Proofs.GcGenerational
import Flapjack.Compiler.Backend.StackAlloc.Proofs.AllocSimple
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenPartialMoveRootsBitmaps
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenPartialMoveRefList
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenPartialMoveData
import Flapjack.Compiler.Backend.StackAlloc.Proofs.SetNewTrigger
import Flapjack.FiniteMap.MapKeys

/-!
# Generational allocation: partial collector case

The partial-selector case of `alloc_correct_lemma_Generational` at
original4592-4832 retains its complete allocator conclusion. The full-selector
case and assembly remain separate open work. The support facts below expose facts derived by HOL
from the non-error allocation premise; they add no successful target-run
hypothesis. They are Flapjack proof infrastructure, not separately named HOL
declarations, and therefore carry no `@[hol]` attribute.
-/

namespace Flapjack.Compiler.Backend.StackAlloc.AllocGenerationalPartial

open Flapjack Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions

/-- A non-error allocation necessarily obtained a collector state. This derives
collector success from the original source premise, rather than assuming it. -/
theorem alloc_collected {width : Nat} [NeZero width] {C F : Type}
    {w : BitVec width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)}
    (ha : StackSemAllocation.alloc w s = (r, t)) (hr : r ≠ some .error) :
    ∃ collected, StackSemAllocation.gc (setStore .allocSize (.word w) s) =
      some collected := by
  cases hg : StackSemAllocation.gc (setStore .allocSize (.word w) s) with
  | none =>
      simp only [StackSemAllocation.alloc, hg, Prod.mk.injEq] at ha
      exact absurd ha.1.symm hr
  | some collected => exact ⟨collected, rfl⟩

open Classical in
/-- The generational collector success premise forces the original stack-space
and store well-formedness guards. Neither condition is added to the case theorem. -/
theorem collected_guards {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {genSizes : List Nat}
    {s collected : StackSemStateFiniteExact width C F}
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes)
    (hs : StackSemAllocation.gc s = some collected) :
    s.stackSpace ≤ s.stack.length ∧ wordGcFunAssum conf s.store := by
  rw [Generational.gc_thm_generational ⟨hgc, hk⟩] at hs
  by_cases hlen : s.stack.length < s.stackSpace
  · simp only [hlen, if_true] at hs
    contradiction
  have hle : s.stackSpace ≤ s.stack.length := Nat.le_of_not_gt hlen
  simp only [hlen, if_false] at hs
  by_cases ha : wordGcFunAssum conf s.store
  · exact ⟨hle, ha⟩
  · simp only [ha, not_false_eq_true, if_true] at hs
    contradiction

/-- Guard inversion at the exact source state used by allocation. This is the
opening reduction of original4592-4646, with the AllocSize update retained. -/
theorem alloc_guards {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {genSizes : List Nat} {w : BitVec width}
    {s t : StackSemStateFiniteExact width C F} {r : Option (StackSemResult width)}
    (ha : StackSemAllocation.alloc w s = (r, t)) (hr : r ≠ some .error)
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes) :
    s.stackSpace ≤ s.stack.length ∧
      wordGcFunAssum conf (setStore .allocSize (.word w) s).store := by
  obtain ⟨collected, hs⟩ := alloc_collected ha hr
  exact collected_guards (s := setStore .allocSize (.word w) s) hgc hk hs

open Classical in
/-- The actual partial collector result implies every final success flag and
both allocation inequalities. Tuple components are the original collector
operations in their original order; no success flag is assumed separately. -/
theorem partial_collected_flags {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {genSizes : List Nat}
    {s collected : StackSemStateFiniteExact width C F}
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes)
    (hp : wordGenGcCanDoPartial genSizes s.store)
    (hs : StackSemAllocation.gc s = some collected) :
        let curr := wordSemTheWord (holFapply s.store .currHeap)
        let other := wordSemTheWord (holFapply s.store .otherHeap)
        let gs := wordSemTheWord (holFapply s.store .genStart)
        let endh := wordSemTheWord (holFapply s.store .endOfHeap)
        let (_w1, i0, pa0, m0, c0) := wordGenGcPartialMove conf
          (holFapply s.store .globals, gs >>> wordShiftAmount width,
            other, curr, s.memory, s.mdomain, gs, endh - curr)
        let (_ws2, i1, pa1, m1, c1) := wordGenGcPartialMoveRootsBitmaps conf
          (s.stack.drop s.stackSpace, s.bitmaps, i0, pa0, curr, m0,
            s.mdomain, gs, endh - curr)
        let (i2, pa2, m2, c2) := wordGenGcPartialMoveRefList (2 ^ width) conf
          (endh, i1, pa1, curr, m1, s.mdomain, c0 && c1, gs, endh - curr,
            curr + wordSemTheWord (holFapply s.store .heapLength))
        let (_i3, pa3, m3, c3) := wordGenGcPartialMoveData conf (2 ^ width)
          (other, i2, pa2, curr, m2, s.mdomain, gs, endh - curr)
        let (b1, _m4, c4) := memcpy ((pa3 - other) >>> wordShiftAmount width)
          other (curr + gs) m3 s.mdomain
        let a := wordSemTheWord (holFapply s.store .allocSize)
        wordGcFunAssum conf s.store ∧ c2 = true ∧ c3 = true ∧ c4 = true ∧
            a ≤ endh - b1 ∧ a ≤ newTrig (endh - b1) a genSizes := by
  obtain ⟨hlen, ha⟩ := collected_guards hgc hk hs
  rw [Generational.gc_partial hgc hk (Nat.not_lt_of_ge hlen) ha hp] at hs
  simp only [Generational.gcExpanded, Nat.not_lt_of_ge hlen, if_false, ha,
    not_true_eq_false, hp, if_true] at hs
  dsimp only at hs ⊢
  split at hs
  · simpa only [ha, true_and] using ‹True ∧ _›
  · contradiction

open Classical in
/-- The successful partial collector returns the complete original state update,
including the untouched stack prefix, empty registers and ordered store updates.
This follows from the source collector equation, not a target-run assumption. -/
theorem partial_collected_state {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {genSizes : List Nat}
    {s collected : StackSemStateFiniteExact width C F}
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes)
    (hp : wordGenGcCanDoPartial genSizes s.store)
    (hs : StackSemAllocation.gc s = some collected) :
        let curr := wordSemTheWord (holFapply s.store .currHeap)
        let other := wordSemTheWord (holFapply s.store .otherHeap)
        let gs := wordSemTheWord (holFapply s.store .genStart)
        let endh := wordSemTheWord (holFapply s.store .endOfHeap)
        let (w1, i0, pa0, m0, c0) := wordGenGcPartialMove conf
          (holFapply s.store .globals, gs >>> wordShiftAmount width,
            other, curr, s.memory, s.mdomain, gs, endh - curr)
        let (ws2, i1, pa1, m1, c1) := wordGenGcPartialMoveRootsBitmaps conf
          (s.stack.drop s.stackSpace, s.bitmaps, i0, pa0, curr, m0,
            s.mdomain, gs, endh - curr)
        let (i2, pa2, m2, _c2) := wordGenGcPartialMoveRefList (2 ^ width) conf
          (endh, i1, pa1, curr, m1, s.mdomain, c0 && c1, gs, endh - curr,
            curr + wordSemTheWord (holFapply s.store .heapLength))
        let (_i3, pa3, m3, _c3) := wordGenGcPartialMoveData conf (2 ^ width)
          (other, i2, pa2, curr, m2, s.mdomain, gs, endh - curr)
        let (b1, m4, _c4) := memcpy ((pa3 - other) >>> wordShiftAmount width)
          other (curr + gs) m3 s.mdomain
        let a := wordSemTheWord (holFapply s.store .allocSize)
        let s1 := s.store.updateListEq
            [(.currHeap, .word curr), (.otherHeap, .word other),
             (.nextFree, .word b1), (.genStart, .word (b1 - curr)),
             (.triggerGC, .word (b1 + newTrig (endh - b1) a genSizes)),
             (.globals, w1), (.globReal, globReal conf curr (w1)),
             (.temp 0, .word 0), (.temp 1, .word 0)]
        collected = { s with
          stack := s.stack.take s.stackSpace ++ ws2
          memory := m4
          store := s1
          regs := HolFiniteMapExact.empty } := by
  obtain ⟨hlen, ha⟩ := collected_guards hgc hk hs
  rw [Generational.gc_partial hgc hk (Nat.not_lt_of_ge hlen) ha hp] at hs
  simp only [Generational.gcExpanded, Nat.not_lt_of_ge hlen, if_false, ha,
    not_true_eq_false, hp, if_true] at hs
  dsimp only at hs ⊢
  split at hs
  · exact (Option.some.inj hs).symm
  · contradiction

open Flapjack.StackSemEvaluate Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- Concrete selector evaluation used at original4660-4678. The original
unsigned space test selects the partial code after loading trigger and end.
This infrastructure preserves arbitrary code and clock; no run is assumed. -/
theorem evaluate_partial_select {width : Nat} [NeZero width] {C F : Type}
    {genSizes : List Nat} {w trig endh : BitVec width}
    (xs ys : List (HolProg width)) (s : StackSemStateFiniteExact width C F)
    (hne : genSizes ≠ []) (hu : s.useStore = true)
    (ht : s.store.lookup .triggerGC = some (.word trig))
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (hw : s.regs.lookup 1 = some (.word w))
    (hspace : w.toNat ≤ (endh - trig).toNat) :
    evaluate (wordGcPartialOrFull genSizes xs ys, s) =
      evaluate (listSeqHOL xs,
        setVar 7 (.word (endh - trig)) (setVar 7 (.word endh)
          (setVar 8 (.word trig) s))) := by
  cases genSizes with
  | nil => contradiction
  | cons g gs =>
    have hn : ¬(endh - trig).toNat < w.toNat := Nat.not_lt_of_ge hspace
    simp only [BitVec.toNat_sub] at hn
    simp [wordGcPartialOrFull, listSeqHOL, evaluate_seq, evaluate_get,
      evaluate_inst, evaluate_ite, subInst, StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
      StackSemExpressions.wordExp, getVar, StackSemStateOps.getVarImm,
      HolRegImm.toWordRegImm, wordSemWordCmp, wordCmpHOL, wordOpHOL, wordOp, BitVec.lt_def, hu, ht, he, hw, hn,
      setVar, fixClock, StackSemRegisterTransfers.storeOfSyntax,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

open Flapjack.Compiler.Backend.StackRemove (rightShiftInst)

/-- State after the original thirteen-instruction partial collector setup.
This is infrastructure for composing the first collector code theorem. -/
def setupState {width : Nat} [NeZero width] {C F : Type}
    (w gs endh curr len other : BitVec width) (ret glob : WordLocW width)
    (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  setVar 6 (.word other) (setVar 4 (.word (gs >>> wordShiftAmount width)) (setVar 3 (.word other) (setVar 5 glob (setVar 7 (.word len) (setStore (.temp 1) (.word (endh - curr)) (setVar 5 (.word (endh - curr)) (setStore (.temp 0) (.word gs) (setVar 2 (.word curr) (setVar 5 (.word endh) (setVar 4 (.word gs) (setStore .nextFree ret (setStore .allocSize (.word w) (s)))))))))))))

/-- Exact execution of the original partial setup, retaining arbitrary clock
and the return register value saved in NextFree. -/
theorem evaluate_partial_setup {width : Nat} [NeZero width] {C F : Type}
    {w gs endh curr len other : BitVec width} {ret glob : WordLocW width}
    (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true) (hr : s.regs.lookup 0 = some ret)
    (hw : s.regs.lookup 1 = some (.word w))
    (hgs : s.store.lookup .genStart = some (.word gs))
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hl : s.store.lookup .heapLength = some (.word len))
    (hg : s.store.lookup .globals = some glob)
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hshift : wordShiftAmount width < width) :
    evaluate (listSeqHOL [.set .allocSize 1, .set .nextFree 0,
      .get 4 .genStart, .get 5 .endOfHeap, .get 2 .currHeap,
      .set (.temp 0) 4, subInst 5 2, .set (.temp 1) 5,
      .get 7 .heapLength, .get 5 .globals, .get 3 .otherHeap,
      rightShiftInst 4 (wordShiftAmount width), moveHOL 6 3], s) =
      (none, setupState w gs endh curr len other ret glob s) := by
  have hm : wordShiftAmount width % 2 ^ width = wordShiftAmount width :=
    Nat.mod_eq_of_lt (Nat.lt_trans hshift (Nat.lt_two_pow_self))
  have hn : ¬width ≤ wordShiftAmount width := Nat.not_le_of_gt hshift
  simp [listSeqHOL, evaluate_seq, evaluate_set, evaluate_get, evaluate_inst,
    subInst, rightShiftInst, moveHOL, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, wordOpHOL, wordOp, wordShiftHOL,
    getVar, setVar, setStore, fixClock, setupState,
    StackSemRegisterTransfers.storeOfSyntax, HolFiniteMapExact.lookup_updateEq,
    FUPDATE_HOL, hu, hr, hw, hgs, he, hc, hl, hg, ho, hm, hn]

/-- The first collector stage on its concrete setup state. Its source move
success will be discharged using `partial_collected_flags` and ref-list flag
propagation when the full allocator case is assembled. -/
theorem evaluate_partial_first_move {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w gs endh curr len other : BitVec width}
    {ret glob moved : WordLocW width} {i pa : BitVec width}
    {m : BitVec width → WordLocW width} (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true)
    (hr : s.regs.lookup 0 = some ret) (hw : s.regs.lookup 1 = some (.word w))
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hm : wordGenGcPartialMove conf (glob, gs >>> wordShiftAmount width,
      other, curr, s.memory, s.mdomain, gs, endh - curr) = (moved, i, pa, m, true))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hgood : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := setupState w gs endh curr len other ret glob s
    ∃ ck r0 r1 r2 r6,
      evaluate (wordGenGcPartialMoveCode conf, { S with clock := S.clock + ck }) =
        (none, { S with
          memory := m
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2),
            (3, .word pa), (4, .word i), (5, moved), (6, r6)] }) := by
  dsimp only
  apply word_gen_gc_partial_move_code_thm
  refine ⟨hm, hsl, hws, hw2, hlen, hshift, ?_, ?_, rfl, rfl, hgood,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [setupState, getVar, setVar, setStore, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL, hu, hc, hr, hw]

open Flapjack.Compiler.Backend.StackRemove (leftShiftInst constInst)

/-- Original straight-line block after the partial globals move. -/
def rootsSetupState {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (moved curr : BitVec width)
    (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  setVar 8 (.word 0) (setStore .globReal (.word ((moved >>> shiftLength conf <<< wordShiftAmount width) + curr)) (setVar 8 (.word ((moved >>> shiftLength conf <<< wordShiftAmount width) + curr)) (setVar 9 (.word curr) (setVar 8 (.word (moved >>> shiftLength conf <<< wordShiftAmount width)) (setVar 8 (.word (moved >>> shiftLength conf)) (setVar 8 (.word moved) (setStore .globals (.word moved) (s))))))))

/-- The original globals/GlobReal update and stack-index initialization execute
without consuming clock, before the dynamic frame load and roots collector. -/
theorem evaluate_partial_roots_setup {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {moved curr : BitVec width}
    (s : StackSemStateFiniteExact width C F) (hu : s.useStore = true)
    (hm : s.regs.lookup 5 = some (.word moved))
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) :
    evaluate (listSeqHOL [.set .globals 5, moveHOL 8 5,
      rightShiftInst 8 (shiftLength conf), leftShiftInst 8 (wordShiftAmount width),
      .get 9 .currHeap, addInst 8 9, .set .globReal 8, constInst 8 0], s) =
      (none, rootsSetupState conf moved curr s) := by
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
    wordShiftHOL, getVar, setVar, setStore, fixClock, rootsSetupState,
    StackSemRegisterTransfers.storeOfSyntax, HolFiniteMapExact.lookup_updateEq,
    FUPDATE_HOL, hu, hm, hc, hslm, hwsm, hsn, hwn]

/-- The original zero-offset dynamic load reads the first word of the active
frame. Stack nonemptiness is required explicitly here and derived from the
successful roots collector when the allocator case is assembled. -/
theorem evaluate_partial_frame_load {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (hu : s.useStack = true)
    (hr : s.regs.lookup 8 = some (.word 0)) (hs : s.stackSpace < s.stack.length) :
    evaluate (.stackLoadAny 9 8, s) =
      (none, setVar 9 (holHd (s.stack.drop s.stackSpace)) s) := by
  have hv := holHd_drop s.stack s.stackSpace hs
  simp [evaluate_stackLoadAny, hu, getVar, hr, hs, hv]

/-- A successful partial roots pass supplies the strict frame bound needed by
its generated dynamic load. This discharges that bound from the source result. -/
theorem partial_roots_frame_bound {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {curr gs rs i pa i1 pa1 : BitVec width}
    {m m1 : BitVec width → WordLocW width} {stack1 : List (WordLocW width)}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i, pa, curr, m, s.mdomain, gs, rs) =
      (stack1, i1, pa1, m1, true)) :
    s.stackSpace < s.stack.length := by
  by_contra h
  have hd : s.stack.drop s.stackSpace = [] :=
    List.drop_eq_nil_of_le (Nat.le_of_not_gt h)
  rw [hd] at hm
  have hx := wordGenGcPartialMoveRootsBitmaps_unroll [] i pa m stack1 i1 pa1 m1 hm
  rw [hx] at hm
  simp at hm

/-- The four original instructions prepare the partial ref-list pass: register9
is current heap plus heap length and register8 is the end of heap. -/
theorem evaluate_partial_refs_setup {width : Nat} [NeZero width] {C F : Type}
    {curr len endh : BitVec width} (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hl : s.store.lookup .heapLength = some (.word len))
    (he : s.store.lookup .endOfHeap = some (.word endh)) :
    evaluate (listSeqHOL [.get 8 .currHeap, .get 9 .heapLength,
      addInst 9 8, .get 8 .endOfHeap], s) =
      (none, setVar 8 (.word endh) (setVar 9 (.word (len + curr))
        (setVar 9 (.word len) (setVar 8 (.word curr) s)))) := by
  simp [listSeqHOL, evaluate_seq, evaluate_get, evaluate_inst, addInst,
    StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp, wordOpHOL, wordOp,
    setVar, fixClock, StackSemRegisterTransfers.storeOfSyntax,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hu, hc, hl, he]

/-- Concrete original memcpy preparation: length is the shifted source span,
source is OtherHeap and destination is CurrHeap plus GenStart. -/
def memcpySetupState {width : Nat} [NeZero width] {C F : Type}
    (pa other gs curr : BitVec width) (s : StackSemStateFiniteExact width C F) :
    StackSemStateFiniteExact width C F :=
  setVar 3 (.word (gs + curr)) (setVar 1 (.word curr) (setVar 3 (.word gs)
    (setVar 0 (.word ((pa - other) >>> wordShiftAmount width))
      (setVar 0 (.word (pa - other)) (setVar 0 (.word pa)
        (setVar 2 (.word other) s))))))

/-- Exact seven-instruction memcpy setup preserves the current clock. -/
theorem evaluate_partial_memcpy_setup {width : Nat} [NeZero width] {C F : Type}
    {pa other gs curr : BitVec width} (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true) (hp : s.regs.lookup 3 = some (.word pa))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hg : s.store.lookup .genStart = some (.word gs))
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hws : wordShiftAmount width < width) :
    evaluate (listSeqHOL [.get 2 .otherHeap, moveHOL 0 3, subInst 0 2,
      rightShiftInst 0 (wordShiftAmount width), .get 3 .genStart,
      .get 1 .currHeap, addInst 3 1], s) =
      (none, memcpySetupState pa other gs curr s) := by
  have hm : wordShiftAmount width % 2 ^ width = wordShiftAmount width :=
    Nat.mod_eq_of_lt (Nat.lt_trans hws (Nat.lt_two_pow_self))
  have hn : ¬width ≤ wordShiftAmount width := Nat.not_le_of_gt hws
  simp [listSeqHOL, evaluate_seq, evaluate_get, evaluate_inst,
    moveHOL, subInst, rightShiftInst, addInst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, wordOpHOL, wordOp, wordShiftHOL, setVar,
    fixClock, memcpySetupState, StackSemRegisterTransfers.storeOfSyntax,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hu, hp, ho, hg, hc, hm, hn]

/-- Original partial collector cleanup after SetNewTrigger. -/
def cleanupState {width : Nat} [NeZero width] {C F : Type}
    (w endh pa curr : BitVec width) (s : StackSemStateFiniteExact width C F) :
    StackSemStateFiniteExact width C F :=
  setStore .genStart (.word (pa - curr)) (setVar 3 (.word (pa - curr)) (setVar 7 (.word curr) (setVar 8 (.word (endh - pa)) (setVar 1 (.word w) (setStore (.temp 1) (.word 0) (setStore (.temp 0) (.word 0) (setVar 1 (.word 0) (s))))))))

/-- The original cleanup clears precisely Temp0/Temp1, reloads the allocation
request, and writes the new generation start with modular subtraction. -/
theorem evaluate_partial_cleanup {width : Nat} [NeZero width] {C F : Type}
    {w endh pa curr : BitVec width} (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true) (he : s.regs.lookup 8 = some (.word endh))
    (hp : s.regs.lookup 3 = some (.word pa))
    (hw : s.store.lookup .allocSize = some (.word w))
    (hc : s.store.lookup .currHeap = some (.word curr)) :
    evaluate (listSeqHOL [constInst 1 0, .set (.temp 0) 1, .set (.temp 1) 1,
      .get 1 .allocSize, subInst 8 3, .get 7 .currHeap, subInst 3 7,
      .set .genStart 3], s) = (none, cleanupState w endh pa curr s) := by
  simp [listSeqHOL, evaluate_seq, evaluate_set, evaluate_get, evaluate_inst,
    constInst, subInst, StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp, wordOpHOL, wordOp,
    getVar, setVar, setStore, fixClock, cleanupState,
    StackSemRegisterTransfers.storeOfSyntax, HolFiniteMapExact.lookup_updateEq,
    FUPDATE_HOL, hu, he, hp, hw, hc]

/-- Source allocation succeeds after a collector installs NextFree and the
new trigger. The guard uses modular TriggerGC-NextFree exactly as HOL does;
its inequality is provided by the partial collector success inversion. -/
theorem alloc_after_partial_collection {width : Nat} [NeZero width] {C F : Type}
    {w pa space : BitVec width} {s collected : StackSemStateFiniteExact width C F}
    (hg : StackSemAllocation.gc (setStore .allocSize (.word w) s) = some collected)
    (ha : collected.store.lookup .allocSize = some (.word w))
    (hp : collected.store.lookup .nextFree = some (.word pa))
    (ht : collected.store.lookup .triggerGC = some (.word (pa + space)))
    (hw : w.toNat ≤ space.toNat) :
    StackSemAllocation.alloc w s = (none, collected) := by
  have hcancel : pa + space - pa = space := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  simp [StackSemAllocation.alloc, hg, ha, StackSemAllocation.hasSpace, hp, ht,
    hcancel, hw]

/-- The original partial collector success guards force normal source allocation
completion. This supplies the source result used by the final code simulation. -/
theorem alloc_partial_result {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {genSizes : List Nat} {w : BitVec width}
    {s t : StackSemStateFiniteExact width C F} {r : Option (StackSemResult width)}
    (ha : StackSemAllocation.alloc w s = (r, t)) (hr : r ≠ some .error)
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes)
    (hp : wordGenGcCanDoPartial genSizes (setStore .allocSize (.word w) s).store) :
    r = none := by
  obtain ⟨collected, hg⟩ := alloc_collected ha hr
  have hf := partial_collected_flags (s := setStore .allocSize (.word w) s) hgc hk hp hg
  have ht := partial_collected_state (s := setStore .allocSize (.word w) s) hgc hk hp hg
  dsimp only at hf ht
  let S := setStore .allocSize (.word w) s
  let curr := wordSemTheWord (holFapply S.store .currHeap)
  let other := wordSemTheWord (holFapply S.store .otherHeap)
  let gs := wordSemTheWord (holFapply S.store .genStart)
  let endh := wordSemTheWord (holFapply S.store .endOfHeap)
  generalize hmove : wordGenGcPartialMove (width := width) conf (holFapply S.store .globals, gs >>> wordShiftAmount width, other, curr, S.memory, S.mdomain, gs, endh - curr) = q0 at hf ht
  obtain ⟨root, i0, pa0, m0, c0⟩ := q0
  dsimp only [S, curr, other, gs, endh] at hmove
  try rw [hmove] at hf
  try rw [hmove] at ht
  dsimp only at hf ht
  generalize hroots : wordGenGcPartialMoveRootsBitmaps (width := width) (bitmapWidth := width) conf (S.stack.drop S.stackSpace, S.bitmaps, i0, pa0, curr, m0, S.mdomain, gs, endh - curr) = q1 at hf ht
  obtain ⟨roots, i1, pa1, m1, c1⟩ := q1
  dsimp only [S, curr, other, gs, endh] at hroots
  try rw [hroots] at hf
  try rw [hroots] at ht
  dsimp only at hf ht
  generalize hrefs : wordGenGcPartialMoveRefList (width := width) (2 ^ width) conf (endh, i1, pa1, curr, m1, S.mdomain, c0 && c1, gs, endh - curr, curr + wordSemTheWord (holFapply S.store .heapLength)) = q2 at hf ht
  obtain ⟨i2, pa2, m2, c2⟩ := q2
  dsimp only [S, curr, other, gs, endh] at hrefs
  try rw [hrefs] at hf
  try rw [hrefs] at ht
  dsimp only at hf ht
  generalize hdata : wordGenGcPartialMoveData (width := width) conf (2 ^ width) (other, i2, pa2, curr, m2, S.mdomain, gs, endh - curr) = q3 at hf ht
  obtain ⟨i3, pa3, m3, c3⟩ := q3
  dsimp only [S, curr, other, gs, endh] at hdata
  try rw [hdata] at hf
  try rw [hdata] at ht
  dsimp only at hf ht
  generalize hcopy : memcpy (width := width) ((pa3 - other) >>> wordShiftAmount width) other (curr + gs) m3 S.mdomain = q4 at hf ht
  obtain ⟨b1, m4, c4⟩ := q4
  dsimp only [S, curr, other, gs, endh] at hcopy
  try rw [hcopy] at hf
  try rw [hcopy] at ht
  dsimp only at hf ht
  simp only [StackSemAllocation.alloc, hg] at ha
  rw [ht] at ha
  have hle := hf.2.2.2.2.2
  simp only [setStore, holFapply, HolFiniteMapExact.lookup_updateEq,
    FUPDATE_HOL, wordSemTheWord] at hle
  have hcancel : ∀ (a b : BitVec width), a + b - a = b := by
    intro a b
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  simp [-BitVec.toNat_sub, -BitVec.toNat_add, BitVec.le_def] at hle
  simp [-BitVec.toNat_sub, -BitVec.toNat_add, StackSemAllocation.hasSpace, HolFiniteMapExact.lookup_updateListEq,
    FUPDATE_LIST_HOL, FUPDATE_HOL, setStore, HolFiniteMapExact.lookup_updateEq,
    holFapply, wordSemTheWord, hcancel, hle] at ha
  exact ha.1.symm

/-- The original prefix ending immediately before the partial globals move. -/
def partialSetupCode {width : Nat} [NeZero width] : List (HolProg width) :=
  [.set .allocSize 1, .set .nextFree 0,
    .get 4 .genStart, .get 5 .endOfHeap, .get 2 .currHeap,
    .set (.temp 0) 4, subInst 5 2, .set (.temp 1) 5,
    .get 7 .heapLength, .get 5 .globals, .get 3 .otherHeap,
    rightShiftInst 4 (wordShiftAmount width), moveHOL 6 3]

/-- Compose the checked original setup with the remaining collector program.
The continuation is arbitrary; its successful evaluation is not a premise. -/
theorem evaluate_partial_setup_append {width : Nat} [NeZero width] {C F : Type}
    {w gs endh curr len other : BitVec width} {ret glob : WordLocW width}
    (rest : List (HolProg width)) (hrest : rest ≠ [])
    (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true) (hr : s.regs.lookup 0 = some ret)
    (hw : s.regs.lookup 1 = some (.word w))
    (hgs : s.store.lookup .genStart = some (.word gs))
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hl : s.store.lookup .heapLength = some (.word len))
    (hg : s.store.lookup .globals = some glob)
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hshift : wordShiftAmount width < width) :
    evaluate (listSeqHOL (partialSetupCode ++ rest), s) =
      evaluate (listSeqHOL rest, setupState w gs endh curr len other ret glob s) := by
  apply evaluate_listSeq_append_none _ _ _ _ (by simp [partialSetupCode]) hrest
  · intro x hx S
    simp only [partialSetupCode, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact evaluate_clock_of_leaf _ (Or.inl rfl) S
        | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) S
  · exact evaluate_partial_setup s hu hr hw hgs he hc hl hg ho hshift

/-- Concrete roots input after the globals move, GlobReal setup and frame load. -/
noncomputable def rootsInputState {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (w gs endh curr len other moved i pa : BitVec width)
    (ret glob r0 r1 r2 r6 : WordLocW width)
    (m : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F) :
    StackSemStateFiniteExact width C F :=
  let S := setupState w gs endh curr len other ret glob s
  let M := { S with
    memory := m
    regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2),
      (3, .word pa), (4, .word i), (5, .word moved), (6, r6)] }
  setVar 9 (holHd (s.stack.drop s.stackSpace)) (rootsSetupState conf moved curr M)

/-- Apply the original roots code theorem on the actual state prepared by the
partial collector. All frame/bitmap bounds and register facts are discharged
from the source result and concrete setup rather than target evaluation. -/
theorem evaluate_partial_roots {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w gs endh curr len other moved i pa i1 pa1 : BitVec width}
    {ret glob q0 q1 q2 q6 : WordLocW width}
    {m m1 : BitVec width → WordLocW width} {stack1 : List (WordLocW width)}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i, pa, curr, m, s.mdomain, gs, endh - curr) =
      (stack1, i1, pa1, m1, true))
    (hu : s.useStore = true) (hus : s.useStack = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := rootsInputState conf w gs endh curr len other moved i pa ret glob q0 q1 q2 q6 m s
    ∃ ck r0 r1 r2 r5 r6 r7 r8,
      evaluate (wordGenGcPartialMoveRootsBitmapsCode conf, { S with clock := S.clock + ck }) =
        (none, { S with
          memory := m1
          stack := s.stack.take s.stackSpace ++ stack1
          clock := S.clock
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
            (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8), (9, .word 0)] }) := by
  have hframe := partial_roots_frame_bound s hm
  dsimp only
  have H := word_gen_gc_partial_move_roots_bitmaps_code_thm (conf := conf) (gs := gs) (rs := endh - curr)
    (init := s.stack.take s.stackSpace) (stack := s.stack.drop s.stackSpace)
    s.bitmaps (rootsInputState conf w gs endh curr len other moved i pa ret glob q0 q1 q2 q6 m s)
    i pa curr m s.mdomain [] stack1 0 i1 pa1 m1 []
  have HH := H (by
    refine ⟨hm, hb, hg, hsl, hws, hw2, hlen, hg, hshift, ?_⟩
    simp [rootsInputState, rootsSetupState, setupState, getVar, setVar, setStore,
      HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hu, hus, hc,
      List.take_append_drop, List.length_take, Nat.min_eq_left (Nat.le_of_lt hframe),
      Nat.mul_comm, hs])
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, r9, heval⟩ := HH
  exact ⟨ck, r0, r1, r2, r5, r6, r7, r8, by simpa using heval⟩

/-- Concrete ref-list input: the roots result installs all ten registers, then
four original instructions set the end pointer and reference-region bound. -/
def refsInputState {width : Nat} [NeZero width] {C F : Type}
    (curr len endh i pa : BitVec width) (q0 q1 q2 q5 q6 q7 q8 : WordLocW width)
    (m : BitVec width → WordLocW width) (stack : List (WordLocW width))
    (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  let R := { s with
    memory := m
    stack := stack
    regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa),
      (4, .word i), (5, q5), (6, q6), (7, q7), (8, q8), (9, .word 0)] }
  setVar 8 (.word endh) (setVar 9 (.word (len + curr))
    (setVar 9 (.word len) (setVar 8 (.word curr) R)))

/-- Original ref-list code on its concrete post-roots state. Dummy parameters
of the original theorem remain immaterial; every live register is installed
by the actual roots output and the four preparation instructions. -/
theorem evaluate_partial_refs {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {curr len endh gs rs i pa i2 pa2 : BitVec width}
    {q0 q1 q2 q5 q6 q7 q8 : WordLocW width}
    {m m2 : BitVec width → WordLocW width} {stack : List (WordLocW width)}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveRefList (2 ^ width) conf
      (endh, i, pa, curr, m, s.mdomain, true, gs, rs, curr + len) = (i2, pa2, m2, true))
    (hu : s.useStore = true) (hc : s.store.lookup .currHeap = some (.word curr))
    (hgs : s.store.lookup (.temp 0) = some (.word gs))
    (hrs : s.store.lookup (.temp 1) = some (.word rs))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hls : conf.lenSize + 2 < width) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := refsInputState curr len endh i pa q0 q1 q2 q5 q6 q7 q8 m stack s
    ∃ ck r0 r1 r2 r5 r6 r7 r8 r9,
      evaluate (wordGenGcPartialMoveRefListCode conf, { S with clock := S.clock + ck }) =
        (none, { S with
          memory := m2
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
            (4, .word i2), (5, r5), (6, r6), (7, r7), (8, r8), (9, r9)] }) := by
  dsimp only
  apply word_gen_gc_partial_move_ref_list_code_thm (conf := conf) (gs := gs) (rs := rs)
    (2 ^ width) (curr + len) endh 0 i pa 0 0 curr m s.mdomain true i2 pa2 0 0 m2
  refine ⟨hm, hsl, hws, hw2, hlen, hls, hg, hshift, ?_⟩
  simp [refsInputState, getVar, setVar, HolFiniteMapExact.lookup_updateListEq,
    FUPDATE_LIST_HOL, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    hu, hc, BitVec.add_comm]
  exact ⟨hgs, hrs⟩

/-- Data-pass input after the complete ref-list register update and Get8 OtherHeap. -/
def dataInputState {width : Nat} [NeZero width] {C F : Type}
    (other i pa : BitVec width) (q0 q1 q2 q5 q6 q7 q8 q9 : WordLocW width)
    (m : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F) :
    StackSemStateFiniteExact width C F :=
  setVar 8 (.word other) { s with
    memory := m
    regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa),
      (4, .word i), (5, q5), (6, q6), (7, q7), (8, q8), (9, q9)] }

/-- The original data code theorem on the concrete ref-list output state.
The original unused existential carriers are instantiated by Unit and discarded;
the complete actual evaluator output is retained. -/
theorem evaluate_partial_data {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {other curr gs rs i pa i2 pa2 : BitVec width}
    {q0 q1 q2 q5 q6 q7 q8 q9 : WordLocW width}
    {m m2 : BitVec width → WordLocW width}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveData conf (2 ^ width)
      (other, i, pa, curr, m, s.mdomain, gs, rs) = (i2, pa2, m2, true))
    (hu : s.useStore = true) (hc : s.store.lookup .currHeap = some (.word curr))
    (hgs : s.store.lookup (.temp 0) = some (.word gs))
    (hrs : s.store.lookup (.temp 1) = some (.word rs))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hls : conf.lenSize + 2 < width) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := dataInputState other i pa q0 q1 q2 q5 q6 q7 q8 q9 m s
    ∃ ck r0 r1 r2 r5 r6 r7,
      evaluate (wordGenGcPartialMoveDataCode conf, { S with clock := S.clock + ck }) =
        (none, { S with
          memory := m2
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
            (4, .word i2), (5, r5), (6, r6), (7, r7), (8, .word pa2)] }) := by
  dsimp only
  have H := word_gen_gc_partial_move_data_code_thm (conf := conf) (gs := gs) (rs := rs)
    (D := Unit) (E := Unit) (2 ^ width) other i pa curr m s.mdomain true i2 pa2 m2
    (dataInputState other i pa q0 q1 q2 q5 q6 q7 q8 q9 m s)
  have HH := H (by
    refine ⟨hm, hsl, hws, hw2, hlen, hls, hshift, ?_⟩
    simp [dataInputState, getVar, setVar, HolFiniteMapExact.lookup_updateListEq,
      FUPDATE_LIST_HOL, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hu, hc, hg]
    exact ⟨hgs, hrs⟩)
    (by simp [dataInputState, setVar, HolFiniteMapExact.lookup_updateListEq,
      FUPDATE_LIST_HOL, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
    (by simp [dataInputState, setVar, HolFiniteMapExact.lookup_updateListEq,
      FUPDATE_LIST_HOL, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
    (by simp [dataInputState, getVar, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, t0, t1, heval⟩ := HH
  exact ⟨ck, r0, r1, r2, r5, r6, r7, heval⟩

/-- Concrete memcpy input after the data-pass output and seven preparation instructions. -/
def memcpyInputState {width : Nat} [NeZero width] {C F : Type}
    (pa i other gs curr : BitVec width) (q0 q1 q2 q5 q6 q7 : WordLocW width)
    (m : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F) :
    StackSemStateFiniteExact width C F :=
  let D := { s with
    memory := m
    regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa),
      (4, .word i), (5, q5), (6, q6), (7, q7), (8, .word pa)] }
  memcpySetupState pa other gs curr D

/-- Original memcpy code on the actual post-data state. Its exact extra clock
is the unsigned shifted source-span length, as in the original HOL theorem. -/
theorem evaluate_partial_memcpy {width : Nat} [NeZero width] {C F : Type}
    {pa i other gs curr b1 : BitVec width} {q0 q1 q2 q5 q6 q7 : WordLocW width}
    {m m1 : BitVec width → WordLocW width} (s : StackSemStateFiniteExact width C F)
    (hm : memcpy ((pa - other) >>> wordShiftAmount width) other (curr + gs)
      m s.mdomain = (b1, m1, true)) :
    let S := memcpyInputState pa i other gs curr q0 q1 q2 q5 q6 q7 m s
    ∃ r1,
      evaluate (memcpyCode,
        { S with clock := S.clock + ((pa - other) >>> wordShiftAmount width).toNat }) =
        (none, { S with
          memory := m1
          regs := S.regs.updateListEq [(0, .word 0), (1, r1),
            (2, .word (other + ((pa - other) >>> wordShiftAmount width) * wordSemBytesInWord)),
            (3, .word b1)] }) := by
  dsimp only
  apply memcpy_code_thm ((pa - other) >>> wordShiftAmount width) other (curr + gs)
    m s.mdomain b1 m1
  refine ⟨hm, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;>
    simp [memcpyInputState, memcpySetupState, getVar, setVar,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, BitVec.add_comm]

/-- The four original instructions between memcpy and SetNewTrigger save the
return value back in register0 and install the new NextFree pointer. -/
def triggerSetupState {width : Nat} [NeZero width] {C F : Type}
    (b1 endh trig : BitVec width) (ret : WordLocW width)
    (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  setVar 2 (.word trig) (setVar 8 (.word endh)
    (setStore .nextFree (.word b1) (setVar 0 ret s)))

/-- Exact trigger preparation, preserving the memcpy result and clock. -/
theorem evaluate_partial_trigger_setup {width : Nat} [NeZero width] {C F : Type}
    {b1 endh trig : BitVec width} {ret : WordLocW width}
    (s : StackSemStateFiniteExact width C F) (hu : s.useStore = true)
    (hb : s.regs.lookup 3 = some (.word b1))
    (hr : s.store.lookup .nextFree = some ret)
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (ht : s.store.lookup .triggerGC = some (.word trig)) :
    evaluate (listSeqHOL [.get 0 .nextFree, .set .nextFree 3,
      .get 8 .endOfHeap, .get 2 .triggerGC], s) =
      (none, triggerSetupState b1 endh trig ret s) := by
  simp [listSeqHOL, evaluate_seq, evaluate_get, evaluate_set, getVar, setVar,
    setStore, fixClock, triggerSetupState, StackSemRegisterTransfers.storeOfSyntax,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hu, hb, hr, he, ht]

/-- Constructive original trigger evaluation on the concrete prepared state.
No target evaluation is assumed; the registers8/3 instance discharges the
original distinct-register side condition. -/
theorem evaluate_partial_trigger {width : Nat} [NeZero width] {C F : Type}
    {w b1 endh trig : BitVec width} {ret : WordLocW width} (genSizes : List Nat)
    (s : StackSemStateFiniteExact width C F) (hg : goodDimindex width)
    (hu : s.useStore = true) (hb : s.regs.lookup 3 = some (.word b1))
    (hw : s.store.lookup .allocSize = some (.word w)) :
    let S := triggerSetupState b1 endh trig ret s
    ∃ r7 r1 r4,
      evaluate (setNewTrigger 8 3 genSizes, S) =
        (none, { S with
          regs := ((S.regs.updateEq (1, r1)).updateEq (7, r7)).updateEq (4, r4)
          store := S.store.updateEq (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)) }) := by
  dsimp only
  apply setNewTrigger_run _ 8 3 endh b1 w genSizes hg
  · simpa [triggerSetupState, setVar, setStore] using hu
  · decide
  · simp [triggerSetupState, setVar, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  · simp [triggerSetupState, setVar, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hb]
  · simp [triggerSetupState, setVar, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hw]

/-- Compose two already-proved collector stages with the sum of their clocks.
This is Flapjack proof infrastructure: its evaluation premises are intermediate
results produced by the original code theorems, not hypotheses of the final
HOL allocator case. The first stage restores the source clock as those code
theorems do; no timeout branch is suppressed. -/
theorem evaluate_seq_collector_clocks {width : Nat} [NeZero width] {C F : Type}
    (p q : HolProg width) (S T U : StackSemStateFiniteExact width C F)
    (a b : Nat) (hclock : T.clock = S.clock)
    (hp : evaluate (p, { S with clock := S.clock + a }) = (none, T))
    (hq : evaluate (q, { T with clock := T.clock + b }) = (none, U)) :
    evaluate (.seq p q, { S with clock := S.clock + (a + b) }) = (none, U) := by
  have he := StackProps.evaluateAddClock b p _ none T ⟨hp, by simp⟩
  have hpExtended : evaluate (p, { S with clock := S.clock + (a + b) }) =
      (none, { T with clock := T.clock + b }) := by
    simpa only [Nat.add_assoc] using he
  rw [evaluate_seq_none p q _ _ hpExtended (by simp only; omega)]
  exact hq

/-- Cleanup after the original trigger result preserves the return value
installed by Get0 NextFree. Every subsequent register update is at 1/2/3/4/7/8. -/
theorem partial_final_return_register {width : Nat} [NeZero width] {C F : Type}
    (w b1 endh trig curr : BitVec width) (genSizes : List Nat)
    (ret r7 r1 r4 : WordLocW width) (s : StackSemStateFiniteExact width C F) :
    let S := triggerSetupState b1 endh trig ret s
    let T := { S with
      regs := ((S.regs.updateEq (1, r1)).updateEq (7, r7)).updateEq (4, r4)
      store := S.store.updateEq (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)) }
    (cleanupState w endh b1 curr T).regs.lookup 0 = some ret := by
  simp [triggerSetupState, cleanupState, setVar, setStore,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- The source collector empties the register map, so the final submap
obligation holds for every complete target register map. This is a canonical
finite-map fact, not a target-state hypothesis. -/
theorem partial_empty_regs_submap {width : Nat} [NeZero width]
    (regs : HolFiniteMapExact Nat (WordLocW width)) :
    (HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW width)).submap regs := by
  intro key value h
  simp [HolFiniteMapExact.empty] at h

/-- Ordered generated store updates agree with the source partial collector.
The unchanged heap-base fields follow from their original lookups. This is
untagged finite-map infrastructure for the final allocator state equality. -/
theorem partial_store_updates {width : Nat} [NeZero width]
    (f : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (w curr other gs endh b1 space root : BitVec width) (ret gr : WordLocW width)
    (hc : f.lookup .currHeap = some (.word curr))
    (ho : f.lookup .otherHeap = some (.word other)) :
    f.updateListEq [
      (.allocSize, .word w), (.nextFree, ret),
      (.temp 0, .word gs), (.temp 1, .word (endh - curr)),
      (.globals, .word root), (.globReal, gr),
      (.nextFree, .word b1), (.triggerGC, .word (b1 + space)),
      (.temp 0, .word 0), (.temp 1, .word 0), (.genStart, .word (b1 - curr))] =
    (f.updateEq (.allocSize, .word w)).updateListEq [
      (.currHeap, .word curr), (.otherHeap, .word other),
      (.nextFree, .word b1), (.genStart, .word (b1 - curr)),
      (.triggerGC, .word (b1 + space)), (.globals, .word root),
      (.globReal, gr), (.temp 0, .word 0), (.temp 1, .word 0)] := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  cases key <;>
    simp [HolFiniteMapExact.lookup_updateListEq, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_LIST_HOL, FUPDATE_HOL, hc, ho]
  split <;> simp_all

/-- Recover a concrete word lookup from the source collector's presence and
word-shape guards, without assuming a successful target load. -/
theorem partial_word_lookup {width : Nat} [NeZero width]
    (f : HolFiniteMapExact WordStoreHOL (WordLocW width)) (key : WordStoreHOL)
    (hp : (f.lookup key).isSome = true)
    (hw : wordSemIsWordLoc (holFapply f key) = true) :
    f.lookup key = some (.word (wordSemTheWord (holFapply f key))) := by
  cases h : f.lookup key with
  | none => simp [h] at hp
  | some value =>
    cases value with
    | word w => simp [holFapply, h, wordSemTheWord]
    | loc n m => simp [holFapply, h, wordSemIsWordLoc] at hw

/-- All seven source store guards become the concrete loads used by the partial
program. Width and configuration restrictions are retained from HOL's guard. -/
theorem partial_source_loads {width : Nat} [NeZero width]
    (conf : Config) (f : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (ha : wordGcFunAssum conf f) :
    (∀ key ∈ ([.globals, .currHeap, .otherHeap, .heapLength, .triggerGC,
      .genStart, .endOfHeap] : List WordStoreHOL),
      f.lookup key = some (.word (wordSemTheWord (holFapply f key)))) ∧
    goodDimindex width ∧ conf.lenSize ≠ 0 ∧ conf.lenSize + 2 < width ∧
    shiftLength conf < width := by
  rcases ha with ⟨hp, ho, hc, ht, hl, hgs, he, hg, hd, hn, hlen, hshift⟩
  refine ⟨?_, hd, hn, hlen, hshift⟩
  intro key hkey
  apply partial_word_lookup f key (hp key hkey)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hkey
  rcases hkey with h | h | h | h | h | h | h
  · subst key; exact hg
  · subst key; exact hc
  · subst key; exact ho
  · subst key; exact hl
  · subst key; exact ht
  · subst key; exact hgs
  · subst key; exact he

/-- Select the actual partial program using the source collector's assumptions
and original partial selector. Its store loads and unsigned comparison are
derived rather than supplied as additional allocator hypotheses. -/
theorem evaluate_partial_select_from_source {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (genSizes : List Nat) (w : BitVec width)
    (xs ys : List (HolProg width)) (s : StackSemStateFiniteExact width C F)
    (ha : wordGcFunAssum conf (setStore .allocSize (.word w) s).store)
    (hp : wordGenGcCanDoPartial genSizes (setStore .allocSize (.word w) s).store)
    (hu : s.useStore = true) (hw : s.regs.lookup 1 = some (.word w)) :
    let trig := wordSemTheWord (holFapply s.store .triggerGC)
    let endh := wordSemTheWord (holFapply s.store .endOfHeap)
    evaluate (wordGcPartialOrFull genSizes xs ys, s) =
      evaluate (listSeqHOL xs,
        setVar 7 (.word (endh - trig)) (setVar 7 (.word endh)
          (setVar 8 (.word trig) s))) := by
  dsimp only
  obtain ⟨loads, _⟩ := partial_source_loads conf _ ha
  have ht := loads .triggerGC (by simp)
  have he := loads .endOfHeap (by simp)
  simp [setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    holFapply] at ht he
  rcases hp with ⟨hne, hspace⟩
  simp [setStore, holFapply, HolFiniteMapExact.lookup_updateEq,
    FUPDATE_HOL, wordSemTheWord] at hspace
  apply evaluate_partial_select xs ys s hne hu
  · simpa only [holFapply] using ht
  · simpa only [holFapply] using he
  · exact hw
  · simpa only [BitVec.le_def, holFapply, wordSemTheWord] using hspace

/-- The source ref-list success propagates backwards to both preceding move
stages, exactly as HOL's `word_gen_gc_partial_move_ref_list_ok` does. These are
source operation equations, not assumed executions of the target program. -/
theorem partial_initial_flags {width : Nat} [NeZero width]
    (conf : Config) (endh curr gs len i pa : BitVec width)
    (m m2 : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (c0 c1 : Bool) (i2 pa2 : BitVec width)
    (hr : wordGenGcPartialMoveRefList (2 ^ width) conf
      (endh, i, pa, curr, m, dm, c0 && c1, gs, endh - curr, curr + len) =
      (i2, pa2, m2, true)) : c0 = true ∧ c1 = true := by
  have h := wordGenGcPartialMoveRefList_ok (2 ^ width) (endh - curr)
    (curr + len) endh pa curr m i gs dm conf (c0 && c1) i2 pa2 m2 hr
  simpa only [Bool.and_eq_true] using h

/-- The generated global-real store agrees with the original word-case
projection; the instruction sequence adds the heap base in the opposite order,
which is equivalent in the original modular word arithmetic. -/
theorem partial_global_real {width : Nat} [NeZero width]
    (conf : Config) (curr root : BitVec width) :
    globReal conf curr (.word root) =
      .word (((root >>> shiftLength conf) <<< wordShiftAmount width) + curr) := by
  simp only [globReal, BitVec.add_comm]

/-- A word global remains a word after the exact partial move, including all
forwarding and copy branches. This justifies the following shift instructions. -/
theorem partial_move_preserves_word {width : Nat} [NeZero width]
    (conf : Config) (root i pa curr gs rs : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) :
    wordSemIsWordLoc (wordGenGcPartialMove conf
      (.word root, i, pa, curr, m, dm, gs, rs)).1 = true := by
  simp only [wordGenGcPartialMove]
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- Execute the original thirteen-instruction prefix and first collector as
one program at the collector's existential clock. The only move equation is
the source collector equation; no target execution is assumed. -/
theorem evaluate_partial_setup_move {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w gs endh curr len other : BitVec width}
    {ret glob moved : WordLocW width} {i pa : BitVec width}
    {m : BitVec width → WordLocW width} (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true)
    (hr : s.regs.lookup 0 = some ret) (hw : s.regs.lookup 1 = some (.word w))
    (hgs : s.store.lookup .genStart = some (.word gs))
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hl : s.store.lookup .heapLength = some (.word len))
    (hg : s.store.lookup .globals = some glob)
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hm : wordGenGcPartialMove conf (glob, gs >>> wordShiftAmount width,
      other, curr, s.memory, s.mdomain, gs, endh - curr) = (moved, i, pa, m, true))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hgood : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := setupState w gs endh curr len other ret glob s
    ∃ ck r0 r1 r2 r6,
      evaluate (listSeqHOL (partialSetupCode ++ [wordGenGcPartialMoveCode conf]),
        { s with clock := s.clock + ck }) =
        (none, { S with
          memory := m
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2),
            (3, .word pa), (4, .word i), (5, moved), (6, r6)] }) := by
  dsimp only
  obtain ⟨ck, r0, r1, r2, r6, hrun⟩ :=
    evaluate_partial_first_move s hu hr hw hc hm hsl hws hw2 hlen hgood hshift
  refine ⟨ck, r0, r1, r2, r6, ?_⟩
  rw [evaluate_partial_setup_append [wordGenGcPartialMoveCode conf] (by simp)
    { s with clock := s.clock + ck } hu hr hw hgs he hc hl hg ho hws]
  simpa only [listSeqHOL, setupState, setVar, setStore] using hrun

/-- Original globals update, GlobReal calculation and frame-load prefix. -/
def partialRootsSetupCode {width : Nat} [NeZero width] (conf : Config) :
    List (HolProg width) :=
  [.set .globals 5, moveHOL 8 5, rightShiftInst 8 (shiftLength conf),
    leftShiftInst 8 (wordShiftAmount width), .get 9 .currHeap, addInst 8 9,
    .set .globReal 8, constInst 8 0, .stackLoadAny 9 8]

/-- The complete straight-line roots preparation forwards its concrete state
to any continuation. Successful source roots collection supplies the frame
bound; there is no assumption about the continuation's target execution. -/
theorem evaluate_partial_roots_prepare_append {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {moved curr gs rs i pa i1 pa1 : BitVec width}
    {m m1 : BitVec width → WordLocW width} {stack1 : List (WordLocW width)}
    (rest : List (HolProg width)) (hrest : rest ≠ [])
    (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true) (hst : s.useStack = true)
    (hglob : s.regs.lookup 5 = some (.word moved))
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hm : wordGenGcPartialMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i, pa, curr, m, s.mdomain, gs, rs) =
      (stack1, i1, pa1, m1, true)) :
    evaluate (listSeqHOL (partialRootsSetupCode conf ++ rest), s) =
      evaluate (listSeqHOL rest,
        setVar 9 (holHd (s.stack.drop s.stackSpace)) (rootsSetupState conf moved curr s)) := by
  have hframe := partial_roots_frame_bound s hm
  apply evaluate_listSeq_append_none _ _ _ _ (by simp [partialRootsSetupCode]) hrest
  · intro x hx S
    simp only [partialRootsSetupCode, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact evaluate_clock_of_leaf _ (Or.inl rfl) S
        | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) S
  · have hp := evaluate_partial_roots_setup s hu hglob hc hsl hws
    have hq := evaluate_partial_frame_load (rootsSetupState conf moved curr s)
      (by simpa [rootsSetupState, setVar, setStore] using hst)
      (by simp [rootsSetupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
      (by simpa [rootsSetupState, setVar, setStore] using hframe)
    rw [show listSeqHOL (partialRootsSetupCode conf) =
      listSeqHOL ([.set .globals 5, moveHOL 8 5,
        rightShiftInst 8 (shiftLength conf), leftShiftInst 8 (wordShiftAmount width),
        .get 9 .currHeap, addInst 8 9, .set .globReal 8, constInst 8 0] ++
        [.stackLoadAny 9 8]) from rfl]
    rw [evaluate_listSeq_append_none _ _ s _ (by simp) (by simp) _ hp]
    · simpa only [listSeqHOL, rootsSetupState, setVar, setStore] using hq
    · intro x hx S
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact evaluate_clock_of_leaf _ (Or.inl rfl) S
          | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) S

/-- Compose the globals/frame preparation with the original roots collector,
starting at the concrete first-move output and restoring its original clock. -/
theorem evaluate_partial_roots_with_prefix {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w gs endh curr len other moved i pa i1 pa1 : BitVec width}
    {ret glob q0 q1 q2 q6 : WordLocW width}
    {m m1 : BitVec width → WordLocW width} {stack1 : List (WordLocW width)}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i, pa, curr, m, s.mdomain, gs, endh - curr) =
      (stack1, i1, pa1, m1, true))
    (hu : s.useStore = true) (hus : s.useStack = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let B := setupState w gs endh curr len other ret glob s
    let M := { B with
      memory := m
      regs := B.regs.updateListEq [(0, q0), (1, q1), (2, q2),
        (3, .word pa), (4, .word i), (5, .word moved), (6, q6)] }
    let S := rootsInputState conf w gs endh curr len other moved i pa ret glob q0 q1 q2 q6 m s
    ∃ ck r0 r1 r2 r5 r6 r7 r8,
      evaluate (listSeqHOL (partialRootsSetupCode conf ++
        [wordGenGcPartialMoveRootsBitmapsCode conf]), { M with clock := M.clock + ck }) =
        (none, { S with
          memory := m1
          stack := s.stack.take s.stackSpace ++ stack1
          clock := S.clock
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
            (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8), (9, .word 0)] }) := by
  dsimp only
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, hrun⟩ :=
    evaluate_partial_roots (w := w) (len := len) (other := other) (moved := moved)
      (ret := ret) (glob := glob) (q0 := q0) (q1 := q1) (q2 := q2) (q6 := q6)
      s hm hu hus hc hb hs hsl hws hw2 hlen hg hshift
  refine ⟨ck, r0, r1, r2, r5, r6, r7, r8, ?_⟩
  rw [evaluate_partial_roots_prepare_append (moved := moved) (curr := curr)
    (gs := gs) (rs := endh - curr) (i := i) (pa := pa) (i1 := i1) (pa1 := pa1)
    (m := m) (m1 := m1) (stack1 := stack1) _ (by simp) _
    (by simpa [setupState, setVar, setStore] using hu)
    (by simpa [setupState, setVar, setStore] using hus)
    (by simp [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simpa [setupState, setVar, setStore, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL] using hc) hsl hws
    (by simpa [setupState, setVar, setStore] using hm)]
  simpa only [listSeqHOL, rootsInputState, rootsSetupState, setupState, setVar, setStore]
    using hrun

/-- Exact ref-list preparation forwards the state to an arbitrary continuation,
including at the extra clock supplied by the ref-list collector theorem. -/
theorem evaluate_partial_refs_setup_append {width : Nat} [NeZero width] {C F : Type}
    {curr len endh : BitVec width} (rest : List (HolProg width)) (hrest : rest ≠ [])
    (s : StackSemStateFiniteExact width C F) (hu : s.useStore = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hl : s.store.lookup .heapLength = some (.word len))
    (he : s.store.lookup .endOfHeap = some (.word endh)) :
    evaluate (listSeqHOL ([.get 8 .currHeap, .get 9 .heapLength,
      addInst 9 8, .get 8 .endOfHeap] ++ rest), s) =
      evaluate (listSeqHOL rest, setVar 8 (.word endh) (setVar 9 (.word (len + curr))
        (setVar 9 (.word len) (setVar 8 (.word curr) s)))) := by
  apply evaluate_listSeq_append_none _ _ _ _ (by simp) hrest
  · intro x hx S
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      first
        | exact evaluate_clock_of_leaf _ (Or.inl rfl) S
        | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) S
  · exact evaluate_partial_refs_setup s hu hc hl he

/-- Run ref-list preparation and collection together from the actual roots
output. All target execution equations are produced by the original theorem. -/
theorem evaluate_partial_refs_with_prefix {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {curr len endh gs rs i pa i2 pa2 : BitVec width}
    {q0 q1 q2 q5 q6 q7 q8 : WordLocW width}
    {m m2 : BitVec width → WordLocW width} {stack : List (WordLocW width)}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveRefList (2 ^ width) conf
      (endh, i, pa, curr, m, s.mdomain, true, gs, rs, curr + len) = (i2, pa2, m2, true))
    (hu : s.useStore = true) (hc : s.store.lookup .currHeap = some (.word curr))
    (hl : s.store.lookup .heapLength = some (.word len))
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (hgs : s.store.lookup (.temp 0) = some (.word gs))
    (hrs : s.store.lookup (.temp 1) = some (.word rs))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hls : conf.lenSize + 2 < width) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let R := { s with
      memory := m
      stack := stack
      regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa),
        (4, .word i), (5, q5), (6, q6), (7, q7), (8, q8), (9, .word 0)] }
    let S := refsInputState curr len endh i pa q0 q1 q2 q5 q6 q7 q8 m stack s
    ∃ ck r0 r1 r2 r5 r6 r7 r8 r9,
      evaluate (listSeqHOL [.get 8 .currHeap, .get 9 .heapLength,
        addInst 9 8, .get 8 .endOfHeap, wordGenGcPartialMoveRefListCode conf],
        { R with clock := R.clock + ck }) =
        (none, { S with
          memory := m2
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
            (4, .word i2), (5, r5), (6, r6), (7, r7), (8, r8), (9, r9)] }) := by
  dsimp only
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, r9, hrun⟩ :=
    evaluate_partial_refs (q0 := q0) (q1 := q1) (q2 := q2) (q5 := q5)
      (q6 := q6) (q7 := q7) (q8 := q8) (stack := stack)
      s hm hu hc hgs hrs hsl hws hw2 hlen hls hg hshift
  refine ⟨ck, r0, r1, r2, r5, r6, r7, r8, r9, ?_⟩
  rw [show ([.get 8 .currHeap, .get 9 .heapLength, addInst 9 8,
    .get 8 .endOfHeap, wordGenGcPartialMoveRefListCode conf] : List (HolProg width)) =
    [.get 8 .currHeap, .get 9 .heapLength, addInst 9 8, .get 8 .endOfHeap] ++
      [wordGenGcPartialMoveRefListCode conf] from rfl]
  rw [evaluate_partial_refs_setup_append (curr := curr) (len := len) (endh := endh)
    _ (by simp) { s with
      memory := m
      stack := stack
      clock := s.clock + ck
      regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa),
        (4, .word i), (5, q5), (6, q6), (7, q7), (8, q8), (9, .word 0)] }
    hu hc hl he]
  simpa only [listSeqHOL, refsInputState, setVar] using hrun

/-- The actual OtherHeap load followed by the data collector, starting from
the concrete ref-list result. The load succeeds from the original store fact. -/
theorem evaluate_partial_data_with_prefix {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {other curr gs rs i pa i2 pa2 : BitVec width}
    {q0 q1 q2 q5 q6 q7 q8 q9 : WordLocW width}
    {m m2 : BitVec width → WordLocW width}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveData conf (2 ^ width)
      (other, i, pa, curr, m, s.mdomain, gs, rs) = (i2, pa2, m2, true))
    (hu : s.useStore = true) (hc : s.store.lookup .currHeap = some (.word curr))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hgs : s.store.lookup (.temp 0) = some (.word gs))
    (hrs : s.store.lookup (.temp 1) = some (.word rs))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hls : conf.lenSize + 2 < width) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let R := { s with
      memory := m
      regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa),
        (4, .word i), (5, q5), (6, q6), (7, q7), (8, q8), (9, q9)] }
    let S := dataInputState other i pa q0 q1 q2 q5 q6 q7 q8 q9 m s
    ∃ ck r0 r1 r2 r5 r6 r7,
      evaluate (listSeqHOL [.get 8 .otherHeap, wordGenGcPartialMoveDataCode conf],
        { R with clock := R.clock + ck }) =
        (none, { S with
          memory := m2
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
            (4, .word i2), (5, r5), (6, r6), (7, r7), (8, .word pa2)] }) := by
  dsimp only
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, hrun⟩ :=
    evaluate_partial_data (q0 := q0) (q1 := q1) (q2 := q2) (q5 := q5)
      (q6 := q6) (q7 := q7) (q8 := q8) (q9 := q9)
      s hm hu hc hgs hrs hsl hws hw2 hlen hls hg hshift
  refine ⟨ck, r0, r1, r2, r5, r6, r7, ?_⟩
  have hget : evaluate (.get 8 .otherHeap, { s with
      memory := m
      clock := s.clock + ck
      regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa),
        (4, .word i), (5, q5), (6, q6), (7, q7), (8, q8), (9, q9)] }) =
      (none, { dataInputState other i pa q0 q1 q2 q5 q6 q7 q8 q9 m s with
        clock := s.clock + ck }) := by
    simp [evaluate_get, dataInputState, setVar,
      StackSemRegisterTransfers.storeOfSyntax, hu, ho]
  rw [listSeqHOL, evaluate_seq_none _ _ _ _ hget
    (by change s.clock + ck ≤ s.clock + ck; exact Nat.le_refl _)]
  simpa only [listSeqHOL, dataInputState, setVar] using hrun

/-- The original memcpy preparation forwards its state to any continuation;
the source-span shift retains the original width side condition. -/
theorem evaluate_partial_memcpy_setup_append {width : Nat} [NeZero width] {C F : Type}
    {pa other gs curr : BitVec width} (rest : List (HolProg width)) (hrest : rest ≠ [])
    (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true) (hp : s.regs.lookup 3 = some (.word pa))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hg : s.store.lookup .genStart = some (.word gs))
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hws : wordShiftAmount width < width) :
    evaluate (listSeqHOL ([.get 2 .otherHeap, moveHOL 0 3, subInst 0 2,
      rightShiftInst 0 (wordShiftAmount width), .get 3 .genStart,
      .get 1 .currHeap, addInst 3 1] ++ rest), s) =
      evaluate (listSeqHOL rest, memcpySetupState pa other gs curr s) := by
  apply evaluate_listSeq_append_none _ _ _ _ (by simp) hrest
  · intro x hx S
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact evaluate_clock_of_leaf _ (Or.inl rfl) S
        | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) S
  · exact evaluate_partial_memcpy_setup s hu hp ho hg hc hws

/-- Execute memcpy preparation and copy from the concrete data result, with
exactly the original unsigned shifted-span clock and complete output state. -/
theorem evaluate_partial_memcpy_with_prefix {width : Nat} [NeZero width] {C F : Type}
    {pa i other gs curr b1 : BitVec width} {q0 q1 q2 q5 q6 q7 : WordLocW width}
    {m m1 : BitVec width → WordLocW width} (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true)
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hg : s.store.lookup .genStart = some (.word gs))
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hws : wordShiftAmount width < width)
    (hm : memcpy ((pa - other) >>> wordShiftAmount width) other (curr + gs)
      m s.mdomain = (b1, m1, true)) :
    let D := { s with
      memory := m
      regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa),
        (4, .word i), (5, q5), (6, q6), (7, q7), (8, .word pa)] }
    let S := memcpyInputState pa i other gs curr q0 q1 q2 q5 q6 q7 m s
    ∃ r1,
      evaluate (listSeqHOL ([.get 2 .otherHeap, moveHOL 0 3, subInst 0 2,
        rightShiftInst 0 (wordShiftAmount width), .get 3 .genStart,
        .get 1 .currHeap, addInst 3 1] ++ [memcpyCode]),
        { D with clock := D.clock + ((pa - other) >>> wordShiftAmount width).toNat }) =
        (none, { S with
          memory := m1
          regs := S.regs.updateListEq [(0, .word 0), (1, r1),
            (2, .word (other + ((pa - other) >>> wordShiftAmount width) * wordSemBytesInWord)),
            (3, .word b1)] }) := by
  dsimp only
  obtain ⟨r1, hrun⟩ := evaluate_partial_memcpy (i := i) (q0 := q0) (q1 := q1)
    (q2 := q2) (q5 := q5) (q6 := q6) (q7 := q7) s hm
  refine ⟨r1, ?_⟩
  rw [evaluate_partial_memcpy_setup_append (pa := pa) (other := other)
    (gs := gs) (curr := curr) [memcpyCode] (by simp) { s with
      memory := m
      clock := s.clock + ((pa - other) >>> wordShiftAmount width).toNat
      regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa),
        (4, .word i), (5, q5), (6, q6), (7, q7), (8, .word pa)] }
    hu (by simp [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    ho hg hc hws]
  simpa only [listSeqHOL, memcpyInputState, memcpySetupState, setVar] using hrun

/-- Final trigger preparation, constructive SetNewTrigger and cleanup execute
as the original thirteen-instruction suffix, retaining the complete final
store/register state and source clock. -/
theorem evaluate_partial_trigger_cleanup {width : Nat} [NeZero width] {C F : Type}
    {w b1 endh trig curr : BitVec width} {ret : WordLocW width} (genSizes : List Nat)
    (s : StackSemStateFiniteExact width C F) (hg : goodDimindex width)
    (hu : s.useStore = true) (hb : s.regs.lookup 3 = some (.word b1))
    (hr : s.store.lookup .nextFree = some ret)
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (ht : s.store.lookup .triggerGC = some (.word trig))
    (hw : s.store.lookup .allocSize = some (.word w))
    (hc : s.store.lookup .currHeap = some (.word curr)) :
    let S := triggerSetupState b1 endh trig ret s
    ∃ r7 r1 r4,
      let T := { S with
        regs := ((S.regs.updateEq (1, r1)).updateEq (7, r7)).updateEq (4, r4)
        store := S.store.updateEq (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)) }
      evaluate (listSeqHOL ([.get 0 .nextFree, .set .nextFree 3,
        .get 8 .endOfHeap, .get 2 .triggerGC] ++
        [setNewTrigger 8 3 genSizes, constInst 1 0, .set (.temp 0) 1, .set (.temp 1) 1,
          .get 1 .allocSize, subInst 8 3, .get 7 .currHeap, subInst 3 7, .set .genStart 3]), s) =
        (none, cleanupState w endh b1 curr T) := by
  dsimp only
  obtain ⟨r7, r1, r4, hrun⟩ := evaluate_partial_trigger (endh := endh) (trig := trig)
    (ret := ret) genSizes s hg hu hb hw
  refine ⟨r7, r1, r4, ?_⟩
  rw [evaluate_listSeq_append_none _ _ s _ (by simp) (by simp) _
    (evaluate_partial_trigger_setup s hu hb hr he ht)]
  · rw [listSeqHOL, evaluate_seq_none _ _ _ _ hrun
      (by simp only [triggerSetupState, setVar, setStore]; exact Nat.le_refl _)]
    apply evaluate_partial_cleanup
    · simpa [triggerSetupState, setVar, setStore] using hu
    · simp [triggerSetupState, setVar, setStore, HolFiniteMapExact.lookup_updateEq,
        FUPDATE_HOL]
    · simp [triggerSetupState, setVar, setStore, HolFiniteMapExact.lookup_updateEq,
        FUPDATE_HOL, hb]
    · simp [triggerSetupState, setVar, setStore, HolFiniteMapExact.lookup_updateEq,
        FUPDATE_HOL, hw]
    · simp [triggerSetupState, setVar, setStore, HolFiniteMapExact.lookup_updateEq,
        FUPDATE_HOL, hc]
  · intro x hx R
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      exact evaluate_clock_of_leaf _ (Or.inl rfl) R

/-- A normally completing source allocation returns its collector state
unchanged. In particular the partial case's final-state equality may use `t`
directly, without a separate target-state or successful-space premise. -/
theorem alloc_normal_collector {width : Nat} [NeZero width] {C F : Type}
    {w : BitVec width} {s t : StackSemStateFiniteExact width C F}
    (ha : StackSemAllocation.alloc w s = (none, t)) :
    StackSemAllocation.gc (setStore .allocSize (.word w) s) = some t := by
  obtain ⟨collected, hg⟩ := alloc_collected ha (by simp)
  cases hl : collected.store.lookup .allocSize with
  | none => simp [StackSemAllocation.alloc, hg, hl] at ha
  | some amount =>
    cases hs : StackSemAllocation.hasSpace amount collected.store with
    | none => simp [StackSemAllocation.alloc, hg, hl, hs] at ha
    | some b =>
      cases b with
      | false => simp [StackSemAllocation.alloc, hg, hl, hs] at ha
      | true =>
        have ht : collected = t := by
          simpa [StackSemAllocation.alloc, hg, hl, hs] using ha
        simpa only [ht] using hg

/-- The original partial allocation result is precisely the successful source
collector state, discharging both the normal-result and state-match obligations. -/
theorem alloc_partial_collector {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {genSizes : List Nat} {w : BitVec width}
    {s t : StackSemStateFiniteExact width C F} {r : Option (StackSemResult width)}
    (ha : StackSemAllocation.alloc w s = (r, t)) (hr : r ≠ some .error)
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes)
    (hp : wordGenGcCanDoPartial genSizes (setStore .allocSize (.word w) s).store) :
    r = none ∧ StackSemAllocation.gc (setStore .allocSize (.word w) s) = some t := by
  have hn := alloc_partial_result ha hr hgc hk hp
  refine ⟨hn, ?_⟩
  apply alloc_normal_collector
  simpa only [hn] using ha

/-- Extract every successful original source collector stage and its complete
result from source collection. Early flags follow backwards from ref-list
success, so no independent successful-stage hypothesis is introduced. -/
theorem partial_source_pipeline {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {genSizes : List Nat}
    {s collected : StackSemStateFiniteExact width C F}
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes)
    (hp : wordGenGcCanDoPartial genSizes s.store)
    (hs : StackSemAllocation.gc s = some collected) :
    let curr := wordSemTheWord (holFapply s.store .currHeap)
    let other := wordSemTheWord (holFapply s.store .otherHeap)
    let gs := wordSemTheWord (holFapply s.store .genStart)
    let endh := wordSemTheWord (holFapply s.store .endOfHeap)
    let len := wordSemTheWord (holFapply s.store .heapLength)
    let a := wordSemTheWord (holFapply s.store .allocSize)
    ∃ root i0 pa0 m0 roots i1 pa1 m1 i2 pa2 m2 i3 pa3 m3 b1 m4,
      wordGenGcPartialMove conf
        (holFapply s.store .globals, gs >>> wordShiftAmount width,
          other, curr, s.memory, s.mdomain, gs, endh - curr) = (root, i0, pa0, m0, true) ∧
      wordGenGcPartialMoveRootsBitmaps conf
        (s.stack.drop s.stackSpace, s.bitmaps, i0, pa0, curr, m0,
          s.mdomain, gs, endh - curr) = (roots, i1, pa1, m1, true) ∧
      wordGenGcPartialMoveRefList (2 ^ width) conf
        (endh, i1, pa1, curr, m1, s.mdomain, true, gs, endh - curr, curr + len) =
          (i2, pa2, m2, true) ∧
      wordGenGcPartialMoveData conf (2 ^ width)
        (other, i2, pa2, curr, m2, s.mdomain, gs, endh - curr) = (i3, pa3, m3, true) ∧
      memcpy ((pa3 - other) >>> wordShiftAmount width) other (curr + gs) m3 s.mdomain =
        (b1, m4, true) ∧
      wordGcFunAssum conf s.store ∧ a ≤ endh - b1 ∧
      a ≤ newTrig (endh - b1) a genSizes ∧
      collected = { s with
        stack := s.stack.take s.stackSpace ++ roots
        memory := m4
        store := s.store.updateListEq
          [(.currHeap, .word curr), (.otherHeap, .word other),
           (.nextFree, .word b1), (.genStart, .word (b1 - curr)),
           (.triggerGC, .word (b1 + newTrig (endh - b1) a genSizes)),
           (.globals, root), (.globReal, globReal conf curr root),
           (.temp 0, .word 0), (.temp 1, .word 0)]
        regs := HolFiniteMapExact.empty } := by
  dsimp only
  have hf := partial_collected_flags (s := s) hgc hk hp hs
  have ht := partial_collected_state (s := s) hgc hk hp hs
  dsimp only at hf ht
  let S := s
  let curr := wordSemTheWord (holFapply S.store .currHeap)
  let other := wordSemTheWord (holFapply S.store .otherHeap)
  let gs := wordSemTheWord (holFapply S.store .genStart)
  let endh := wordSemTheWord (holFapply S.store .endOfHeap)
  generalize hmove : wordGenGcPartialMove (width := width) conf (holFapply S.store .globals, gs >>> wordShiftAmount width, other, curr, S.memory, S.mdomain, gs, endh - curr) = q0 at hf ht
  obtain ⟨root, i0, pa0, m0, c0⟩ := q0
  dsimp only [S, curr, other, gs, endh] at hmove
  try rw [hmove] at hf
  try rw [hmove] at ht
  dsimp only at hf ht
  generalize hroots : wordGenGcPartialMoveRootsBitmaps (width := width) (bitmapWidth := width) conf (S.stack.drop S.stackSpace, S.bitmaps, i0, pa0, curr, m0, S.mdomain, gs, endh - curr) = q1 at hf ht
  obtain ⟨roots, i1, pa1, m1, c1⟩ := q1
  dsimp only [S, curr, other, gs, endh] at hroots
  try rw [hroots] at hf
  try rw [hroots] at ht
  dsimp only at hf ht
  generalize hrefs : wordGenGcPartialMoveRefList (width := width) (2 ^ width) conf (endh, i1, pa1, curr, m1, S.mdomain, c0 && c1, gs, endh - curr, curr + wordSemTheWord (holFapply S.store .heapLength)) = q2 at hf ht
  obtain ⟨i2, pa2, m2, c2⟩ := q2
  dsimp only [S, curr, other, gs, endh] at hrefs
  try rw [hrefs] at hf
  try rw [hrefs] at ht
  dsimp only at hf ht
  generalize hdata : wordGenGcPartialMoveData (width := width) conf (2 ^ width) (other, i2, pa2, curr, m2, S.mdomain, gs, endh - curr) = q3 at hf ht
  obtain ⟨i3, pa3, m3, c3⟩ := q3
  dsimp only [S, curr, other, gs, endh] at hdata
  try rw [hdata] at hf
  try rw [hdata] at ht
  dsimp only at hf ht
  generalize hcopy : memcpy (width := width) ((pa3 - other) >>> wordShiftAmount width) other (curr + gs) m3 S.mdomain = q4 at hf ht
  obtain ⟨b1, m4, c4⟩ := q4
  dsimp only [S, curr, other, gs, endh] at hcopy
  try rw [hcopy] at hf
  try rw [hcopy] at ht
  dsimp only at hf ht
  rcases hf with ⟨hass, hc2, hc3, hc4, hend, htrig⟩
  subst c2
  subst c3
  subst c4
  have hinput := wordGenGcPartialMoveRefList_ok (2 ^ width) (endh - curr)
    (curr + wordSemTheWord (holFapply S.store .heapLength)) endh pa1 curr m1
    i1 gs S.mdomain conf (c0 && c1) i2 pa2 m2 hrefs
  simp only [Bool.and_eq_true] at hinput
  rcases hinput with ⟨hc0, hc1⟩
  subst c0
  subst c1
  refine ⟨root, i0, pa0, m0, roots, i1, pa1, m1, i2, pa2, m2,
    i3, pa3, m3, b1, m4, ?_, ?_, ?_, ?_, ?_, hass, hend, htrig, ht⟩
  · rfl
  · exact hroots
  · simpa only [Bool.true_and] using hrefs
  · exact hdata
  · exact hcopy

/-- Join the first two concrete collector segments at the sum of their clocks.
No target run is assumed: both equations come from the source stage results. -/
theorem evaluate_partial_move_roots {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w gs endh curr len other : BitVec width}
    {ret glob : WordLocW width} {moved i pa i1 pa1 : BitVec width}
    {m m1 : BitVec width → WordLocW width} {stack1 : List (WordLocW width)} (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true)
    (hr : s.regs.lookup 0 = some ret) (hw : s.regs.lookup 1 = some (.word w))
    (hgs : s.store.lookup .genStart = some (.word gs))
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hl : s.store.lookup .heapLength = some (.word len))
    (hg : s.store.lookup .globals = some glob)
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hm : wordGenGcPartialMove conf (glob, gs >>> wordShiftAmount width,
      other, curr, s.memory, s.mdomain, gs, endh - curr) = (.word moved, i, pa, m, true))
    (hmroots : wordGenGcPartialMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i, pa, curr, m, s.mdomain, gs, endh - curr) =
      (stack1, i1, pa1, m1, true))
    (hus : s.useStack = true) (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hgood : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    ∃ ck q0 q1 q2 q6 r0 r1 r2 r5 r6 r7 r8,
      let S := rootsInputState conf w gs endh curr len other moved i pa
        ret glob q0 q1 q2 q6 m s
      evaluate (.seq
        (listSeqHOL (partialSetupCode ++ [wordGenGcPartialMoveCode conf]))
        (listSeqHOL (partialRootsSetupCode conf ++ [wordGenGcPartialMoveRootsBitmapsCode conf])),
        { s with clock := s.clock + ck }) =
        (none, { S with
          memory := m1
          stack := s.stack.take s.stackSpace ++ stack1
          clock := S.clock
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
            (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8), (9, .word 0)] }) := by
  obtain ⟨k0, q0, q1, q2, q6, hfirst⟩ :=
    evaluate_partial_setup_move s hu hr hw hgs he hc hl hg ho hm hsl hws hw2 hlen hgood hshift
  obtain ⟨k1, r0, r1, r2, r5, r6, r7, r8, hroots⟩ :=
    evaluate_partial_roots_with_prefix (w := w) (len := len) (other := other)
      (moved := moved) (ret := ret) (glob := glob)
      (q0 := q0) (q1 := q1) (q2 := q2) (q6 := q6)
      s hmroots hu hus hc hb hs hsl hws hw2 hlen hgood hshift
  refine ⟨k0 + k1, q0, q1, q2, q6, r0, r1, r2, r5, r6, r7, r8, ?_⟩
  dsimp only
  apply evaluate_seq_collector_clocks _ _ s _ _ k0 k1
    (by simp [setupState, setVar, setStore]) hfirst hroots

/-- Append a continuation after a collector-ending prefix. Only the preceding
straight-line instructions must preserve clock; the final collector's clock
bound comes from its checked concrete run. This is untagged composition
infrastructure, whose evaluation premise is an intermediate stage result. -/
theorem evaluate_listSeq_append_collector {width : Nat} [NeZero width] {C F : Type} :
    ∀ (xs ys : List (HolProg width)) (S T : StackSemStateFiniteExact width C F),
      xs ≠ [] → ys ≠ [] →
      (∀ x ∈ xs.dropLast, ∀ U : StackSemStateFiniteExact width C F,
        (evaluate (x, U)).2.clock = U.clock) →
      T.clock ≤ S.clock → evaluate (listSeqHOL xs, S) = (none, T) →
      evaluate (listSeqHOL (xs ++ ys), S) = evaluate (listSeqHOL ys, T)
  | [], _, _, _, h, _, _, _, _ => absurd rfl h
  | [x], y :: ys, S, T, _, _, _, hclock, h => by
      change evaluate (x, S) = (none, T) at h
      exact evaluate_seq_none x (listSeqHOL (y :: ys)) S T h hclock
  | x :: x1 :: xs, y :: ys, S, T, _, _, hcl, hclock, h => by
      show evaluate (.seq x (listSeqHOL ((x1 :: xs) ++ y :: ys)), S) = _
      rw [show listSeqHOL (x :: x1 :: xs) = .seq x (listSeqHOL (x1 :: xs)) from rfl,
        evaluate_seq] at h
      rw [evaluate_seq]
      have hx := hcl x (by simp) S
      rcases he : evaluate (x, S) with ⟨r, U⟩
      rw [he] at h hx
      simp only at hx
      have hfix : fixClock S (r, U) = (r, U) := by
        show (r, { U with clock := min S.clock U.clock }) = (r, U)
        rw [← hx, Nat.min_self]
      rw [hfix] at h ⊢
      cases r with
      | some e => simp at h
      | none =>
        apply evaluate_listSeq_append_collector (x1 :: xs) (y :: ys) U T
          (by simp) (by simp) _ (by simpa only [hx] using hclock) h
        intro z hz V
        apply hcl z _ V
        simpa using List.mem_cons_of_mem x hz
  | _ :: _, [], _, _, _, h, _, _, _ => absurd rfl h

/-- Join two collector segments as the original concatenated instruction list,
with the sum of the checked segment clocks rather than a changed grouping. -/
theorem evaluate_listSeq_collector_clocks {width : Nat} [NeZero width] {C F : Type}
    (xs ys : List (HolProg width)) (hx : xs ≠ []) (hy : ys ≠ [])
    (S T U : StackSemStateFiniteExact width C F) (a b : Nat)
    (hcl : ∀ x ∈ xs.dropLast, ∀ V : StackSemStateFiniteExact width C F,
      (evaluate (x, V)).2.clock = V.clock)
    (hclock : T.clock = S.clock)
    (hp : evaluate (listSeqHOL xs, { S with clock := S.clock + a }) = (none, T))
    (hq : evaluate (listSeqHOL ys, { T with clock := T.clock + b }) = (none, U)) :
    evaluate (listSeqHOL (xs ++ ys), { S with clock := S.clock + (a + b) }) =
      (none, U) := by
  have he := StackProps.evaluateAddClock b (listSeqHOL xs) _ none T ⟨hp, by simp⟩
  have hpExtended : evaluate (listSeqHOL xs, { S with clock := S.clock + (a + b) }) =
      (none, { T with clock := T.clock + b }) := by
    simpa only [Nat.add_assoc] using he
  rw [evaluate_listSeq_append_collector xs ys _ _ hx hy hcl
    (by simp only; omega) hpExtended]
  exact hq

/-- The first two collector segments as the exact original instruction list. -/
theorem evaluate_partial_move_roots_list {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w gs endh curr len other : BitVec width}
    {ret glob : WordLocW width} {moved i pa i1 pa1 : BitVec width}
    {m m1 : BitVec width → WordLocW width} {stack1 : List (WordLocW width)} (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true)
    (hr : s.regs.lookup 0 = some ret) (hw : s.regs.lookup 1 = some (.word w))
    (hgs : s.store.lookup .genStart = some (.word gs))
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hl : s.store.lookup .heapLength = some (.word len))
    (hg : s.store.lookup .globals = some glob)
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hm : wordGenGcPartialMove conf (glob, gs >>> wordShiftAmount width,
      other, curr, s.memory, s.mdomain, gs, endh - curr) = (.word moved, i, pa, m, true))
    (hmroots : wordGenGcPartialMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i, pa, curr, m, s.mdomain, gs, endh - curr) =
      (stack1, i1, pa1, m1, true))
    (hus : s.useStack = true) (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hgood : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    ∃ ck q0 q1 q2 q6 r0 r1 r2 r5 r6 r7 r8,
      let S := rootsInputState conf w gs endh curr len other moved i pa
        ret glob q0 q1 q2 q6 m s
      evaluate (listSeqHOL ((partialSetupCode ++ [wordGenGcPartialMoveCode conf]) ++
        (partialRootsSetupCode conf ++ [wordGenGcPartialMoveRootsBitmapsCode conf])),
        { s with clock := s.clock + ck }) =
        (none, { S with
          memory := m1
          stack := s.stack.take s.stackSpace ++ stack1
          clock := S.clock
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
            (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8), (9, .word 0)] }) := by
  obtain ⟨k0, q0, q1, q2, q6, hfirst⟩ :=
    evaluate_partial_setup_move s hu hr hw hgs he hc hl hg ho hm hsl hws hw2 hlen hgood hshift
  obtain ⟨k1, r0, r1, r2, r5, r6, r7, r8, hroots⟩ :=
    evaluate_partial_roots_with_prefix (w := w) (len := len) (other := other)
      (moved := moved) (ret := ret) (glob := glob)
      (q0 := q0) (q1 := q1) (q2 := q2) (q6 := q6)
      s hmroots hu hus hc hb hs hsl hws hw2 hlen hgood hshift
  refine ⟨k0 + k1, q0, q1, q2, q6, r0, r1, r2, r5, r6, r7, r8, ?_⟩
  dsimp only
  apply evaluate_listSeq_collector_clocks _ _ (by simp [partialSetupCode])
    (by simp [partialRootsSetupCode]) s _ _ k0 k1 _
    (by simp [setupState, setVar, setStore]) hfirst hroots
  intro x hx V
  simp only [partialSetupCode, List.cons_append, List.nil_append,
    List.dropLast_cons_cons, List.dropLast_singleton,
    List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact evaluate_clock_of_leaf _ (Or.inl rfl) V
      | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) V

/-- Join memcpy with the complete original trigger/cleanup suffix. Register
premises describe its concrete prepared input and are discharged by preparation
in the allocator assembly; no target execution is assumed here. -/
theorem evaluate_partial_copy_trigger_tail {width : Nat} [NeZero width] {C F : Type}
    (genSizes : List Nat) (count src dst b1 w endh trig curr : BitVec width)
    (ret : WordLocW width) (m1 : BitVec width → WordLocW width)
    (s : StackSemStateFiniteExact width C F) (hg : goodDimindex width)
    (hu : s.useStore = true)
    (h0 : getVar 0 s = some (.word count)) (h1 : (s.regs.lookup 1).isSome = true)
    (h2 : getVar 2 s = some (.word src)) (h3 : getVar 3 s = some (.word dst))
    (hr : s.store.lookup .nextFree = some ret)
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (ht : s.store.lookup .triggerGC = some (.word trig))
    (hw : s.store.lookup .allocSize = some (.word w))
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hm : memcpy count src dst s.memory s.mdomain = (b1, m1, true)) :
    ∃ copyReg r7 r1 r4,
      let M := { s with
        memory := m1
        regs := s.regs.updateListEq [(0, .word 0), (1, copyReg),
          (2, .word (src + count * wordSemBytesInWord)), (3, .word b1)] }
      let S := triggerSetupState b1 endh trig ret M
      let T := { S with
        regs := ((S.regs.updateEq (1, r1)).updateEq (7, r7)).updateEq (4, r4)
        store := S.store.updateEq (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)) }
      evaluate (.seq memcpyCode (listSeqHOL ([.get 0 .nextFree, .set .nextFree 3,
        .get 8 .endOfHeap, .get 2 .triggerGC] ++
        [setNewTrigger 8 3 genSizes, constInst 1 0, .set (.temp 0) 1, .set (.temp 1) 1,
          .get 1 .allocSize, subInst 8 3, .get 7 .currHeap, subInst 3 7, .set .genStart 3])),
        { s with clock := s.clock + count.toNat }) =
        (none, cleanupState w endh b1 curr T) := by
  obtain ⟨copyReg, hcopy⟩ := memcpy_code_thm count src dst s.memory s.mdomain b1 m1 s
    ⟨hm, rfl, rfl, h0, h1, h2, h3⟩
  let M := { s with
    memory := m1
    regs := s.regs.updateListEq [(0, .word 0), (1, copyReg),
      (2, .word (src + count * wordSemBytesInWord)), (3, .word b1)] }
  obtain ⟨r7, r1, r4, htail⟩ := evaluate_partial_trigger_cleanup (w := w)
    (b1 := b1) (endh := endh) (trig := trig) (curr := curr) (ret := ret)
    genSizes M hg hu
    (by simp [M, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    hr he ht hw hc
  refine ⟨copyReg, r7, r1, r4, ?_⟩
  dsimp only
  rw [evaluate_seq_none _ _ _ _ hcopy
    (by change s.clock ≤ s.clock + count.toNat; omega)]
  exact htail

/-- Complete original suffix from the data result through memcpy preparation,
copy, trigger and cleanup. Its only collector premise is the source memcpy
equation; prepared register facts are proved by the seven instructions. -/
theorem evaluate_partial_memcpy_tail {width : Nat} [NeZero width] {C F : Type}
    (genSizes : List Nat) (pa other gs b1 w endh trig curr : BitVec width)
    (ret : WordLocW width) (m1 : BitVec width → WordLocW width)
    (s : StackSemStateFiniteExact width C F) (hg : goodDimindex width)
    (hu : s.useStore = true) (hpa : s.regs.lookup 3 = some (.word pa))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hgs : s.store.lookup .genStart = some (.word gs))
    (hr : s.store.lookup .nextFree = some ret)
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (ht : s.store.lookup .triggerGC = some (.word trig))
    (hw : s.store.lookup .allocSize = some (.word w))
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hws : wordShiftAmount width < width)
    (hm : memcpy ((pa - other) >>> wordShiftAmount width) other (curr + gs)
      s.memory s.mdomain = (b1, m1, true)) :
    let P := memcpySetupState pa other gs curr s
    ∃ copyReg r7 r1 r4,
      let M := { P with
        memory := m1
        regs := P.regs.updateListEq [(0, .word 0), (1, copyReg),
          (2, .word (other + ((pa - other) >>> wordShiftAmount width) * wordSemBytesInWord)),
          (3, .word b1)] }
      let S := triggerSetupState b1 endh trig ret M
      let T := { S with
        regs := ((S.regs.updateEq (1, r1)).updateEq (7, r7)).updateEq (4, r4)
        store := S.store.updateEq (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)) }
      evaluate (listSeqHOL ([.get 2 .otherHeap, moveHOL 0 3, subInst 0 2,
        rightShiftInst 0 (wordShiftAmount width), .get 3 .genStart,
        .get 1 .currHeap, addInst 3 1] ++
        [memcpyCode, .get 0 .nextFree, .set .nextFree 3, .get 8 .endOfHeap,
          .get 2 .triggerGC, setNewTrigger 8 3 genSizes, constInst 1 0,
          .set (.temp 0) 1, .set (.temp 1) 1, .get 1 .allocSize, subInst 8 3,
          .get 7 .currHeap, subInst 3 7, .set .genStart 3]),
        { s with clock := s.clock + ((pa - other) >>> wordShiftAmount width).toNat }) =
        (none, cleanupState w endh b1 curr T) := by
  dsimp only
  obtain ⟨copyReg, r7, r1, r4, htail⟩ := evaluate_partial_copy_trigger_tail genSizes
    ((pa - other) >>> wordShiftAmount width) other (curr + gs) b1 w endh trig curr
    ret m1 (memcpySetupState pa other gs curr s) hg hu
    (by simp [memcpySetupState, getVar, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
    (by simp [memcpySetupState, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
    (by simp [memcpySetupState, getVar, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
    (by simp [memcpySetupState, getVar, setVar, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL, BitVec.add_comm]) hr he ht hw hc hm
  refine ⟨copyReg, r7, r1, r4, ?_⟩
  rw [evaluate_partial_memcpy_setup_append (pa := pa) (other := other)
    (gs := gs) (curr := curr) _ (by simp)
    { s with clock := s.clock + ((pa - other) >>> wordShiftAmount width).toNat }
    hu hpa ho hgs hc hws]
  simpa only [listSeqHOL, List.cons_append, List.nil_append, memcpySetupState, setVar]
    using htail

/-- Data collection and the complete original copy/trigger suffix, with a full
source-shaped state update and return-register preservation. -/
theorem evaluate_partial_data_tail {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {other curr gs rs i pa i2 pa2 b1 w endh trig : BitVec width}
    {q0 q1 q2 q5 q6 q7 q8 q9 : WordLocW width}
    {m m2 m3 : BitVec width → WordLocW width}
    (genSizes : List Nat) (ret : WordLocW width)
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveData conf (2 ^ width)
      (other, i, pa, curr, m, s.mdomain, gs, rs) = (i2, pa2, m2, true))
    (hu : s.useStore = true) (hc : s.store.lookup .currHeap = some (.word curr))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hgsStore : s.store.lookup .genStart = some (.word gs))
    (hr : s.store.lookup .nextFree = some ret)
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (ht : s.store.lookup .triggerGC = some (.word trig))
    (hw : s.store.lookup .allocSize = some (.word w))
    (hcopy : memcpy ((pa2 - other) >>> wordShiftAmount width) other (curr + gs)
      m2 s.mdomain = (b1, m3, true))
    (hgs : s.store.lookup (.temp 0) = some (.word gs))
    (hrs : s.store.lookup (.temp 1) = some (.word rs))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hls : conf.lenSize + 2 < width) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let R := { s with
      memory := m
      regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa),
        (4, .word i), (5, q5), (6, q6), (7, q7), (8, q8), (9, q9)] }
    ∃ ck regs,
      evaluate (listSeqHOL ([.get 8 .otherHeap, wordGenGcPartialMoveDataCode conf] ++
        [.get 2 .otherHeap, moveHOL 0 3, subInst 0 2,
          rightShiftInst 0 (wordShiftAmount width), .get 3 .genStart,
          .get 1 .currHeap, addInst 3 1, memcpyCode, .get 0 .nextFree,
          .set .nextFree 3, .get 8 .endOfHeap, .get 2 .triggerGC,
          setNewTrigger 8 3 genSizes, constInst 1 0, .set (.temp 0) 1,
          .set (.temp 1) 1, .get 1 .allocSize, subInst 8 3,
          .get 7 .currHeap, subInst 3 7, .set .genStart 3]),
        { R with clock := R.clock + ck }) =
        (none, { s with
          memory := m3
          regs := regs
          store := s.store.updateListEq [(.nextFree, .word b1),
            (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)),
            (.temp 0, .word 0), (.temp 1, .word 0), (.genStart, .word (b1 - curr))] }) ∧
      regs.lookup 0 = some ret := by
  dsimp only
  obtain ⟨kd, d0, d1, d2, d5, d6, d7, hd⟩ :=
    evaluate_partial_data_with_prefix (q0 := q0) (q1 := q1) (q2 := q2)
      (q5 := q5) (q6 := q6) (q7 := q7) (q8 := q8) (q9 := q9)
      s hm hu hc ho hgs hrs hsl hws hw2 hlen hls hg hshift
  let S := dataInputState other i pa q0 q1 q2 q5 q6 q7 q8 q9 m s
  let D := { S with
    memory := m2
    regs := S.regs.updateListEq [(0, d0), (1, d1), (2, d2), (3, .word pa2),
      (4, .word i2), (5, d5), (6, d6), (7, d7), (8, .word pa2)] }
  obtain ⟨copyReg, r7, r1, r4, htail⟩ := evaluate_partial_memcpy_tail genSizes
    pa2 other gs b1 w endh trig curr ret m3 D hg hu
    (by simp [D, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    ho hgsStore hr he ht hw hc hws hcopy
  let P := memcpySetupState pa2 other gs curr D
  let M := { P with
    memory := m3
    regs := P.regs.updateListEq [(0, .word 0), (1, copyReg),
      (2, .word (other + ((pa2 - other) >>> wordShiftAmount width) * wordSemBytesInWord)),
      (3, .word b1)] }
  let T0 := triggerSetupState b1 endh trig ret M
  let T := { T0 with
    regs := ((T0.regs.updateEq (1, r1)).updateEq (7, r7)).updateEq (4, r4)
    store := T0.store.updateEq (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)) }
  let final := cleanupState w endh b1 curr T
  have hstate : final = { s with
      memory := m3
      regs := final.regs
      store := s.store.updateListEq [(.nextFree, .word b1),
        (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)),
        (.temp 0, .word 0), (.temp 1, .word 0), (.genStart, .word (b1 - curr))] } := by
    rfl
  refine ⟨kd + ((pa2 - other) >>> wordShiftAmount width).toNat, final.regs, ?_, ?_⟩
  · rw [← hstate]
    apply evaluate_listSeq_collector_clocks _ _ (by simp) (by simp) _ D final
      kd ((pa2 - other) >>> wordShiftAmount width).toNat _
      (by simp [D, S, dataInputState, setVar]) hd htail
    intro x hx V
    simp only [List.dropLast_cons_cons, List.dropLast_singleton,
      List.mem_cons, List.mem_nil_iff, or_false] at hx
    subst x
    exact evaluate_clock_of_leaf _ (Or.inl rfl) V
  · exact partial_final_return_register w b1 endh trig curr genSizes ret r7 r1 r4 M

/-- Original ref-list collector followed by the full data/copy/trigger tail. -/
theorem evaluate_partial_refs_tail {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {curr len endh gs rs i pa i2 pa2 other i3 pa3 b1 w trig : BitVec width}
    {q0 q1 q2 q5 q6 q7 q8 : WordLocW width}
    {m m2 m3 m4 : BitVec width → WordLocW width} {stack : List (WordLocW width)}
    (genSizes : List Nat) (ret : WordLocW width)
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveRefList (2 ^ width) conf
      (endh, i, pa, curr, m, s.mdomain, true, gs, rs, curr + len) = (i2, pa2, m2, true))
    (hu : s.useStore = true) (hc : s.store.lookup .currHeap = some (.word curr))
    (hl : s.store.lookup .heapLength = some (.word len))
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hgsStore : s.store.lookup .genStart = some (.word gs))
    (hr : s.store.lookup .nextFree = some ret)
    (ht : s.store.lookup .triggerGC = some (.word trig))
    (hw : s.store.lookup .allocSize = some (.word w))
    (hmdata : wordGenGcPartialMoveData conf (2 ^ width)
      (other, i2, pa2, curr, m2, s.mdomain, gs, rs) = (i3, pa3, m3, true))
    (hmcopy : memcpy ((pa3 - other) >>> wordShiftAmount width) other (curr + gs)
      m3 s.mdomain = (b1, m4, true))
    (hgs : s.store.lookup (.temp 0) = some (.word gs))
    (hrs : s.store.lookup (.temp 1) = some (.word rs))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hls : conf.lenSize + 2 < width) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let R := { s with
      memory := m
      stack := stack
      regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa),
        (4, .word i), (5, q5), (6, q6), (7, q7), (8, q8), (9, .word 0)] }
    ∃ ck regs,
      evaluate (listSeqHOL ([.get 8 .currHeap, .get 9 .heapLength, addInst 9 8,
        .get 8 .endOfHeap, wordGenGcPartialMoveRefListCode conf] ++
        ([.get 8 .otherHeap, wordGenGcPartialMoveDataCode conf] ++
        [.get 2 .otherHeap, moveHOL 0 3, subInst 0 2,
          rightShiftInst 0 (wordShiftAmount width), .get 3 .genStart,
          .get 1 .currHeap, addInst 3 1, memcpyCode, .get 0 .nextFree,
          .set .nextFree 3, .get 8 .endOfHeap, .get 2 .triggerGC,
          setNewTrigger 8 3 genSizes, constInst 1 0, .set (.temp 0) 1,
          .set (.temp 1) 1, .get 1 .allocSize, subInst 8 3,
          .get 7 .currHeap, subInst 3 7, .set .genStart 3])),
        { R with clock := R.clock + ck }) =
        (none, { s with
          memory := m4
          stack := stack
          regs := regs
          store := s.store.updateListEq [(.nextFree, .word b1),
            (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)),
            (.temp 0, .word 0), (.temp 1, .word 0), (.genStart, .word (b1 - curr))] }) ∧
      regs.lookup 0 = some ret := by
  dsimp only
  obtain ⟨kr, r0, r1, r2, r5, r6, r7, r8, r9, href⟩ :=
    evaluate_partial_refs_with_prefix (q0 := q0) (q1 := q1) (q2 := q2)
      (q5 := q5) (q6 := q6) (q7 := q7) (q8 := q8) (stack := stack)
      s hm hu hc hl he hgs hrs hsl hws hw2 hlen hls hg hshift
  let S := refsInputState curr len endh i pa q0 q1 q2 q5 q6 q7 q8 m stack s
  let U := { S with
    memory := m2
    regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
      (4, .word i2), (5, r5), (6, r6), (7, r7), (8, r8), (9, r9)] }
  obtain ⟨kt, regs, htail, hret⟩ :=
    evaluate_partial_data_tail (q0 := r0) (q1 := r1) (q2 := r2)
      (q5 := r5) (q6 := r6) (q7 := r7) (q8 := r8) (q9 := r9)
      genSizes ret S hmdata hu hc ho hgsStore hr he ht hw hmcopy hgs hrs
      hsl hws hw2 hlen hls hg hshift
  refine ⟨kr + kt, regs, ?_, hret⟩
  apply evaluate_listSeq_collector_clocks _ _ (by simp) (by simp) _ U _ kr kt _
    (by simp [U, S, refsInputState, setVar]) href htail
  intro x hx V
  simp only [List.dropLast_cons_cons, List.dropLast_singleton,
    List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    first
      | exact evaluate_clock_of_leaf _ (Or.inl rfl) V
      | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) V

/-- Roots collection followed by the complete original ref-list/data/copy tail. -/
theorem evaluate_partial_roots_tail {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w gs endh curr len other moved i pa i1 pa1 i2 pa2 i3 pa3 b1 trig : BitVec width}
    {ret glob q0 q1 q2 q6 : WordLocW width}
    {m m1 m2 m3 m4 : BitVec width → WordLocW width} {stack1 : List (WordLocW width)}
    (genSizes : List Nat)
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i, pa, curr, m, s.mdomain, gs, endh - curr) =
      (stack1, i1, pa1, m1, true))
    (hu : s.useStore = true) (hus : s.useStack = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hl : s.store.lookup .heapLength = some (.word len))
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hgsStore : s.store.lookup .genStart = some (.word gs))
    (ht : s.store.lookup .triggerGC = some (.word trig))
    (hmrefs : wordGenGcPartialMoveRefList (2 ^ width) conf
      (endh, i1, pa1, curr, m1, s.mdomain, true, gs, endh - curr, curr + len) =
      (i2, pa2, m2, true))
    (hmdata : wordGenGcPartialMoveData conf (2 ^ width)
      (other, i2, pa2, curr, m2, s.mdomain, gs, endh - curr) = (i3, pa3, m3, true))
    (hmcopy : memcpy ((pa3 - other) >>> wordShiftAmount width) other (curr + gs)
      m3 s.mdomain = (b1, m4, true))
    (hls : conf.lenSize + 2 < width)
    (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let B := setupState w gs endh curr len other ret glob s
    let M := { B with
      memory := m
      regs := B.regs.updateListEq [(0, q0), (1, q1), (2, q2),
        (3, .word pa), (4, .word i), (5, .word moved), (6, q6)] }
    let S := rootsInputState conf w gs endh curr len other moved i pa ret glob q0 q1 q2 q6 m s
    ∃ ck regs,
      evaluate (listSeqHOL ((partialRootsSetupCode conf ++
        [wordGenGcPartialMoveRootsBitmapsCode conf]) ++
        ([.get 8 .currHeap, .get 9 .heapLength, addInst 9 8,
        .get 8 .endOfHeap, wordGenGcPartialMoveRefListCode conf] ++
        ([.get 8 .otherHeap, wordGenGcPartialMoveDataCode conf] ++
        [.get 2 .otherHeap, moveHOL 0 3, subInst 0 2,
          rightShiftInst 0 (wordShiftAmount width), .get 3 .genStart,
          .get 1 .currHeap, addInst 3 1, memcpyCode, .get 0 .nextFree,
          .set .nextFree 3, .get 8 .endOfHeap, .get 2 .triggerGC,
          setNewTrigger 8 3 genSizes, constInst 1 0, .set (.temp 0) 1,
          .set (.temp 1) 1, .get 1 .allocSize, subInst 8 3,
          .get 7 .currHeap, subInst 3 7, .set .genStart 3]))),
        { M with clock := M.clock + ck }) =
        (none, { s with
          memory := m4
          stack := s.stack.take s.stackSpace ++ stack1
          regs := regs
          store := S.store.updateListEq [(.nextFree, .word b1),
            (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)),
            (.temp 0, .word 0), (.temp 1, .word 0), (.genStart, .word (b1 - curr))] }) ∧
      regs.lookup 0 = some ret := by
  dsimp only
  obtain ⟨kr, r0, r1, r2, r5, r6, r7, r8, hroot⟩ :=
    evaluate_partial_roots_with_prefix (w := w) (len := len) (other := other)
      (moved := moved) (ret := ret) (glob := glob)
      (q0 := q0) (q1 := q1) (q2 := q2) (q6 := q6)
      s hm hu hus hc hb hs hsl hws hw2 hlen hg hshift
  let S := rootsInputState conf w gs endh curr len other moved i pa ret glob q0 q1 q2 q6 m s
  let U := { S with
    memory := m1
    stack := s.stack.take s.stackSpace ++ stack1
    regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
      (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8), (9, .word 0)] }
  obtain ⟨kt, regs, htail, hret⟩ :=
    evaluate_partial_refs_tail (w := w) (q0 := r0) (q1 := r1) (q2 := r2)
      (q5 := r5) (q6 := r6) (q7 := r7) (q8 := r8)
      (stack := s.stack.take s.stackSpace ++ stack1)
      genSizes ret S hmrefs hu
      (by simpa [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hc)
      (by simpa [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hl)
      (by simpa [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using he)
      (by simpa [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using ho)
      (by simpa [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hgsStore)
      (by simp [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
      (by simpa [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using ht)
      (by simp [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]) hmdata hmcopy
      (by simp [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
      (by simp [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
      hsl hws hw2 hlen hls hg hshift
  refine ⟨kr + kt, regs, ?_, hret⟩
  apply evaluate_listSeq_collector_clocks _ _ (by simp [partialRootsSetupCode])
    (by simp) _ U _ kr kt _
    (by simp [U, S, rootsInputState, rootsSetupState, setupState, setVar, setStore]) hroot htail
  intro x hx V
  simp only [partialRootsSetupCode, List.cons_append, List.nil_append,
    List.dropLast_cons_cons, List.dropLast_singleton,
    List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact evaluate_clock_of_leaf _ (Or.inl rfl) V
      | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) V

/-- Execute the whole original partial branch from the successful source
collector stage equations, retaining the full target state and saved return. -/
theorem evaluate_partial_program {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w gs endh curr len other moved i pa i1 pa1 i2 pa2 i3 pa3 b1 trig : BitVec width}
    {ret glob : WordLocW width}
    {m m1 m2 m3 m4 : BitVec width → WordLocW width} {stack1 : List (WordLocW width)} (genSizes : List Nat) (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true)
    (hr : s.regs.lookup 0 = some ret) (hw : s.regs.lookup 1 = some (.word w))
    (hgs : s.store.lookup .genStart = some (.word gs))
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hl : s.store.lookup .heapLength = some (.word len))
    (hg : s.store.lookup .globals = some glob)
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hm : wordGenGcPartialMove conf (glob, gs >>> wordShiftAmount width,
      other, curr, s.memory, s.mdomain, gs, endh - curr) = (.word moved, i, pa, m, true))
    (hmroots : wordGenGcPartialMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i, pa, curr, m, s.mdomain, gs, endh - curr) =
      (stack1, i1, pa1, m1, true))
    (hmrefs : wordGenGcPartialMoveRefList (2 ^ width) conf
      (endh, i1, pa1, curr, m1, s.mdomain, true, gs, endh - curr, curr + len) =
      (i2, pa2, m2, true))
    (hmdata : wordGenGcPartialMoveData conf (2 ^ width)
      (other, i2, pa2, curr, m2, s.mdomain, gs, endh - curr) = (i3, pa3, m3, true))
    (hmcopy : memcpy ((pa3 - other) >>> wordShiftAmount width) other (curr + gs)
      m3 s.mdomain = (b1, m4, true))
    (hus : s.useStack = true) (ht : s.store.lookup .triggerGC = some (.word trig))
    (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hls : conf.lenSize + 2 < width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hgood : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    ∃ ck regs,
      evaluate (listSeqHOL ((partialSetupCode ++ [wordGenGcPartialMoveCode conf]) ++
        ((partialRootsSetupCode conf ++
        [wordGenGcPartialMoveRootsBitmapsCode conf]) ++
        ([.get 8 .currHeap, .get 9 .heapLength, addInst 9 8,
        .get 8 .endOfHeap, wordGenGcPartialMoveRefListCode conf] ++
        ([.get 8 .otherHeap, wordGenGcPartialMoveDataCode conf] ++
        [.get 2 .otherHeap, moveHOL 0 3, subInst 0 2,
          rightShiftInst 0 (wordShiftAmount width), .get 3 .genStart,
          .get 1 .currHeap, addInst 3 1, memcpyCode, .get 0 .nextFree,
          .set .nextFree 3, .get 8 .endOfHeap, .get 2 .triggerGC,
          setNewTrigger 8 3 genSizes, constInst 1 0, .set (.temp 0) 1,
          .set (.temp 1) 1, .get 1 .allocSize, subInst 8 3,
          .get 7 .currHeap, subInst 3 7, .set .genStart 3])))),
        { s with clock := s.clock + ck }) =
        (none, { s with
          memory := m4
          stack := s.stack.take s.stackSpace ++ stack1
          regs := regs
          store := (rootsSetupState conf moved curr
            (setupState w gs endh curr len other ret glob s)).store.updateListEq
            [(.nextFree, .word b1),
             (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)),
             (.temp 0, .word 0), (.temp 1, .word 0), (.genStart, .word (b1 - curr))] }) ∧
      regs.lookup 0 = some ret := by
  obtain ⟨km, q0, q1, q2, q6, hmove⟩ :=
    evaluate_partial_setup_move s hu hr hw hgs he hc hl hg ho hm hsl hws hw2 hlen hgood hshift
  let B := setupState w gs endh curr len other ret glob s
  let M := { B with
    memory := m
    regs := B.regs.updateListEq [(0, q0), (1, q1), (2, q2),
      (3, .word pa), (4, .word i), (5, .word moved), (6, q6)] }
  obtain ⟨kt, regs, htail, hret⟩ :=
    evaluate_partial_roots_tail (w := w) (q0 := q0) (q1 := q1) (q2 := q2) (q6 := q6)
      genSizes s hmroots hu hus hc hl he ho hgs ht hmrefs hmdata hmcopy hls hb hs
      hsl hws hw2 hlen hgood hshift
  refine ⟨km + kt, regs, ?_, hret⟩
  apply evaluate_listSeq_collector_clocks _ _ (by simp [partialSetupCode])
    (by simp [partialRootsSetupCode]) s M _ km kt _
    (by simp [M, B, setupState, setVar, setStore]) hmove htail
  intro x hx V
  simp only [partialSetupCode, List.cons_append, List.nil_append,
    List.dropLast_cons_cons, List.dropLast_singleton,
    List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact evaluate_clock_of_leaf _ (Or.inl rfl) V
      | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) V

/-- Normalize the complete generated store to the original partial collector's
ordered result. Both heap-base rewrites are justified by source lookups; the
GlobReal equation is the original modular-word projection. -/
theorem partial_final_store {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (genSizes : List Nat)
    (w gs endh curr len other moved b1 : BitVec width) (ret glob : WordLocW width)
    (s : StackSemStateFiniteExact width C F)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (ho : s.store.lookup .otherHeap = some (.word other)) :
    (rootsSetupState conf moved curr
      (setupState w gs endh curr len other ret glob s)).store.updateListEq
      [(.nextFree, .word b1),
       (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)),
       (.temp 0, .word 0), (.temp 1, .word 0), (.genStart, .word (b1 - curr))] =
    (s.store.updateEq (.allocSize, .word w)).updateListEq
      [(.currHeap, .word curr), (.otherHeap, .word other),
       (.nextFree, .word b1), (.genStart, .word (b1 - curr)),
       (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)),
       (.globals, .word moved), (.globReal, globReal conf curr (.word moved)),
       (.temp 0, .word 0), (.temp 1, .word 0)] := by
  rw [partial_global_real]
  have h := partial_store_updates s.store w curr other gs endh b1
    (newTrig (endh - b1) w genSizes) moved ret
    (.word ((moved >>> shiftLength conf <<< wordShiftAmount width) + curr)) hc ho
  simpa only [rootsSetupState, setupState, setVar, setStore,
    HolFiniteMapExact.updateListEq, HolFiniteMapExact.updateEq, FUPDATE_LIST_HOL,
    List.foldl_cons, List.foldl_nil] using h

/-- Instruction list of the partial collector branch, used only to abbreviate
its literal concatenation in the assembly proof. -/
def partialProgramCode {width : Nat} [NeZero width] (conf : Config) (genSizes : List Nat) :
    List (HolProg width) :=
  (partialSetupCode ++ [wordGenGcPartialMoveCode conf]) ++
        ((partialRootsSetupCode conf ++
        [wordGenGcPartialMoveRootsBitmapsCode conf]) ++
        ([.get 8 .currHeap, .get 9 .heapLength, addInst 9 8,
        .get 8 .endOfHeap, wordGenGcPartialMoveRefListCode conf] ++
        ([.get 8 .otherHeap, wordGenGcPartialMoveDataCode conf] ++
        [.get 2 .otherHeap, moveHOL 0 3, subInst 0 2,
          rightShiftInst 0 (wordShiftAmount width), .get 3 .genStart,
          .get 1 .currHeap, addInst 3 1, memcpyCode, .get 0 .nextFree,
          .set .nextFree 3, .get 8 .endOfHeap, .get 2 .triggerGC,
          setNewTrigger 8 3 genSizes, constInst 1 0, .set (.temp 0) 1,
          .set (.temp 1) 1, .get 1 .allocSize, subInst 8 3,
          .get 7 .currHeap, subInst 3 7, .set .genStart 3])))

/-- Canonical codec for the imported owning StackSem state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Partial-selector case of the original generational allocation theorem.
All successful source stages are derived from allocation; the complete original
existential evaluator/state/submap/return conclusion is retained. The sole added
case selector is HOL's `word_gen_gc_can_do_partial` on the AllocSize-updated
source store. This is the original4592-4832 partial branch; it does not prove
the remaining full-collector case. Canonical finite-support regs/fpRegs/store
and positive-width words are the only carrier translations. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem alloc_correct_lemma_Generational_partial {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {genSizes : List Nat} {c : DataToWord.Config}
    {w : BitVec width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} {l : HolFiniteMapExact Nat (WordLocW width)}
    {ret : WordLocW width} {anything : WordSemGcFun width}
    (ha : StackSemAllocation.alloc w s = (r, t)) (hr : r ≠ some .error)
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes)
    (hbl : s.bitmaps.length < 2 ^ width - 1)
    (hstack : s.stack.length * (width / 8) < 2 ^ width)
    (hl0 : l.lookup 0 = some ret) (hl1 : l.lookup 1 = some (.word w))
    (hp : wordGenGcCanDoPartial genSizes (setStore .allocSize (.word w) s).store) :
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
  obtain ⟨hn, hcol⟩ := alloc_partial_collector ha hr hgc hk hp
  subst r
  let A := setStore .allocSize (.word w) s
  let curr := wordSemTheWord (holFapply A.store .currHeap)
  let other := wordSemTheWord (holFapply A.store .otherHeap)
  let gs := wordSemTheWord (holFapply A.store .genStart)
  let endh := wordSemTheWord (holFapply A.store .endOfHeap)
  let len := wordSemTheWord (holFapply A.store .heapLength)
  let trig := wordSemTheWord (holFapply A.store .triggerGC)
  let globalWord := wordSemTheWord (holFapply A.store .globals)
  obtain ⟨root, i0, pa0, m0, roots, i1, pa1, m1, i2, pa2, m2,
    i3, pa3, m3, b1, m4, hm, hmroots, hmrefs, hmdata, hmcopy,
    hass, hend, htrig, hfinal⟩ := partial_source_pipeline (s := A) hgc hk hp hcol
  obtain ⟨loads, hgood, hlen, hls, hsl⟩ := partial_source_loads conf A.store hass
  have hcurrA : A.store.lookup .currHeap = some (.word curr) := loads _ (by simp)
  have hotherA : A.store.lookup .otherHeap = some (.word other) := loads _ (by simp)
  have hgsA : A.store.lookup .genStart = some (.word gs) := loads _ (by simp)
  have hendA : A.store.lookup .endOfHeap = some (.word endh) := loads _ (by simp)
  have hlenA : A.store.lookup .heapLength = some (.word len) := loads _ (by simp)
  have htrigA : A.store.lookup .triggerGC = some (.word trig) := loads _ (by simp)
  have hglobA : A.store.lookup .globals = some (.word globalWord) := loads _ (by simp)
  have hc : s.store.lookup .currHeap = some (.word curr) := by
    simpa [A, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hcurrA
  have ho : s.store.lookup .otherHeap = some (.word other) := by
    simpa [A, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hotherA
  have hgs : s.store.lookup .genStart = some (.word gs) := by
    simpa [A, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hgsA
  have he : s.store.lookup .endOfHeap = some (.word endh) := by
    simpa [A, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hendA
  have hl : s.store.lookup .heapLength = some (.word len) := by
    simpa [A, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hlenA
  have ht : s.store.lookup .triggerGC = some (.word trig) := by
    simpa [A, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using htrigA
  have hglob : s.store.lookup .globals = some (.word globalWord) := by
    simpa [A, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hglobA
  rw [holFapply_of_lookup hglobA] at hm
  have hrootword := partial_move_preserves_word conf globalWord
    (gs >>> wordShiftAmount width) other curr gs (endh - curr) s.memory s.mdomain
  change wordGenGcPartialMove conf (.word globalWord, gs >>> wordShiftAmount width,
    other, curr, s.memory, s.mdomain, gs, endh - curr) = (root, i0, pa0, m0, true) at hm
  rw [hm] at hrootword
  have hex : ∃ moved, root = .word moved := by
    cases root with
    | word moved => exact ⟨moved, rfl⟩
    | loc block offset => simp [wordSemIsWordLoc] at hrootword
  obtain ⟨moved, rfl⟩ := hex
  have hws : wordShiftAmount width < width := by
    unfold wordShiftAmount
    rcases hgood with h | h <;> simp [h]
  have hw2 : 2 < width := by
    rcases hgood with h | h <;> omega
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
  obtain ⟨ck, regs, hrun, hret⟩ := evaluate_partial_program genSizes P rfl
    (by simpa [P, R, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hl0)
    (by simpa [P, R, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hl1)
    hgs he hc hl hglob ho hm hmroots hmrefs hmdata hmcopy rfl ht hbl hstack
    hls hsl hws hw2 hlen hgood hshift
  rw [partial_final_store conf genSizes w gs endh curr len other moved b1
    ret (.word globalWord) P hc ho] at hrun
  have hamount : wordSemTheWord (holFapply A.store .allocSize) = w := by
    simp [A, setStore, holFapply, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, wordSemTheWord]
  rw [hamount] at hfinal
  have hstate : { P with
      memory := m4
      stack := s.stack.take s.stackSpace ++ roots
      regs := regs
      store := (P.store.updateEq (.allocSize, .word w)).updateListEq
        [(.currHeap, .word curr), (.otherHeap, .word other),
         (.nextFree, .word b1), (.genStart, .word (b1 - curr)),
         (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)),
         (.globals, .word moved), (.globReal, globReal conf curr (.word moved)),
         (.temp 0, .word 0), (.temp 1, .word 0)] } =
      { t with
        useStore := true
        useStack := true
        useAlloc := false
        code := sptFromAList (compile c (sptToAList s.code))
        regs := regs
        gcFun := anything } := by
    rw [hfinal]
    rfl
  have hrunFinal := hrun.trans
    (congrArg (fun U => ((none : Option (StackSemResult width)), U)) hstate)
  refine ⟨ck, regs, ?_, by simp, ?_, fun _ => hret⟩
  · simp only [wordGcCode, hk]
    rw [evaluate_partial_select_from_source conf genSizes w _ _
      { R with clock := s.clock + ck } hass hp rfl hl1]
    rw [holFapply_of_lookup ht, holFapply_of_lookup he]
    simp only [wordSemTheWord]
    simpa only [partialProgramCode, partialSetupCode, partialRootsSetupCode,
      List.cons_append, List.nil_append, P, R, setVar] using hrunFinal
  · rw [hfinal]
    exact partial_empty_regs_submap regs

end Flapjack.Compiler.Backend.StackAlloc.AllocGenerationalPartial

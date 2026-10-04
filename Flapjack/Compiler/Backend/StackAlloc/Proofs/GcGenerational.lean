import Flapjack.Compiler.Backend.StackAlloc.Proofs.GcSimple

namespace Flapjack.Compiler.Backend.StackAlloc.Generational

open Flapjack Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions

open Classical in
/-- Full generational store-level unfolding of original `word_gc_fun_thm_generational`
(line1731). HOL lambdas become sequential tuple lets; negative-one word products
become modular subtraction. Both collector branches retain every store update. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem word_gc_fun_thm_generational {width : Nat} [NeZero width] {conf : Config}
    {genSizes : List Nat} {roots : List (WordLocW width)}
    {m : BitVec width → WordLocW width} {dm : BitVec width → Bool}
    {s : HolFiniteMapExact WordStoreHOL (WordLocW width)} :
    conf.gcKind = .generational genSizes →
    wordGcFun conf (roots, m, dm, s) =
      if ¬wordGcFunAssum conf s then none else
      if wordGenGcCanDoPartial genSizes s then
        let curr := wordSemTheWord (holFapply s .currHeap)
        let other := wordSemTheWord (holFapply s .otherHeap)
        let gs := wordSemTheWord (holFapply s .genStart)
        let endh := wordSemTheWord (holFapply s .endOfHeap)
        let (roots1, i1, pa1, m1, c1) := wordGenGcPartialMoveRoots conf
          (holFapply s .globals :: roots, gs >>> wordShiftAmount width,
            other, curr, m, dm, gs, endh - curr)
        let (i2, pa2, m2, c2) := wordGenGcPartialMoveRefList (2 ^ width) conf
          (endh, i1, pa1, curr, m1, dm, c1, gs, endh - curr,
            curr + wordSemTheWord (holFapply s .heapLength))
        let (_i3, pa3, m3, c3) := wordGenGcPartialMoveData conf (2 ^ width)
          (other, i2, pa2, curr, m2, dm, gs, endh - curr)
        let (b1, m4, c4) := memcpy ((pa3 - other) >>> wordShiftAmount width)
          other (curr + gs) m3 dm
        let a := wordSemTheWord (holFapply s .allocSize)
        if (c2 && c3 && c4) = true ∧ a ≤ endh - b1 ∧
            a ≤ newTrig (endh - b1) a genSizes then
          some (roots1.tail, m4, s.updateListEq
            [(.currHeap, .word curr), (.otherHeap, .word other),
             (.nextFree, .word b1), (.genStart, .word (b1 - curr)),
             (.triggerGC, .word (b1 + newTrig (endh - b1) a genSizes)),
             (.globals, holHd roots1), (.globReal, globReal conf curr (holHd roots1)),
             (.temp 0, .word 0), (.temp 1, .word 0)])
        else none
      else
        let curr := wordSemTheWord (holFapply s .currHeap)
        let other := wordSemTheWord (holFapply s .otherHeap)
        let newEnd := other + wordSemTheWord (holFapply s .heapLength)
        let len := wordSemTheWord (holFapply s .heapLength) >>> wordShiftAmount width
        let (w1, i1, pa1, ib1, pb1, m1, c1) :=
          wordGenGcMove conf (holFapply s .globals, 0, other, len, newEnd, curr, m, dm)
        let (ws2, i2, pa2, ib2, pb2, m2, c2) :=
          wordGenGcMoveRoots conf (roots, i1, pa1, ib1, pb1, curr, m1, dm)
        let (_i3, pa3, _ib3, pb3, m3, c3) :=
          wordGenGcMoveLoop conf len.toNat (other, i2, pa2, ib2, pb2, newEnd, curr, m2, dm)
        let a := wordSemTheWord (holFapply s .allocSize)
        let s1 := s.updateListEq
          [(.currHeap, .word other), (.otherHeap, .word curr),
           (.nextFree, .word pa3), (.genStart, .word (pa3 - other)),
           (.triggerGC, .word (pa3 + newTrig (pb3 - pa3) a genSizes)),
           (.endOfHeap, .word pb3), (.globals, w1), (.globReal, globReal conf other w1),
           (.temp 0, .word 0), (.temp 1, .word 0), (.temp 2, .word 0),
           (.temp 3, .word 0), (.temp 4, .word 0), (.temp 5, .word 0), (.temp 6, .word 0)]
        if wordGcFunAssum conf s ∧ c1 = true ∧ c2 = true ∧ c3 = true
        then some (ws2, m3, s1) else none := by
  intro hk
  simp only [wordGcFun, hk]
  by_cases ha : wordGcFunAssum conf s
  · simp only [ha, not_true_eq_false, if_false]
    by_cases hp : wordGenGcCanDoPartial genSizes s
    · simp only [hp, if_true, wordGenGcPartialFull, wordGenGcPartial]
      have hc : wordSemTheWord (holFapply s .currHeap) +
          (wordSemTheWord (holFapply s .endOfHeap) -
            wordSemTheWord (holFapply s .currHeap)) =
          wordSemTheWord (holFapply s .endOfHeap) := by
        rw [BitVec.add_comm, BitVec.sub_add_cancel]
      simp [hc, Bool.and_assoc]
    · simp only [hp, if_false, wordGenGc, wordGenGcMoveRoots_cons]
      rcases wordGenGcMove conf (holFapply s .globals, 0,
        wordSemTheWord (holFapply s .otherHeap),
        wordSemTheWord (holFapply s .heapLength) >>> wordShiftAmount width,
        wordSemTheWord (holFapply s .otherHeap) + wordSemTheWord (holFapply s .heapLength),
        wordSemTheWord (holFapply s .currHeap), m, dm)
        with ⟨w1, i1, pa1, ib1, pb1, m1, c1⟩
      rcases wordGenGcMoveRoots conf (roots, i1, pa1, ib1, pb1,
        wordSemTheWord (holFapply s .currHeap), m1, dm)
        with ⟨ws2, i2, pa2, ib2, pb2, m2, c2⟩
      rcases wordGenGcMoveLoop conf
        (wordSemTheWord (holFapply s .heapLength) >>> wordShiftAmount width).toNat
        (wordSemTheWord (holFapply s .otherHeap), i2, pa2, ib2, pb2,
        wordSemTheWord (holFapply s .otherHeap) + wordSemTheWord (holFapply s .heapLength),
        wordSemTheWord (holFapply s .currHeap), m2, dm)
        with ⟨i3, pa3, ib3, pb3, m3, c3⟩
      simp [holHd, Bool.and_eq_true, and_assoc]
  · simp [ha]

open Classical in
/-- Working expression for the complete original generational `gc_thm` RHS
(line 1884). This is untagged proof infrastructure pending the equality theorem;
it does not assert transition equivalence. -/
noncomputable def gcExpanded {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (genSizes : List Nat) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemStateFiniteExact width C F) :=
  if s.stack.length < s.stackSpace then none else
      if ¬wordGcFunAssum conf s.store then none else
      if wordGenGcCanDoPartial genSizes s.store then
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
        let (i2, pa2, m2, c2) := wordGenGcPartialMoveRefList (2 ^ width) conf
          (endh, i1, pa1, curr, m1, s.mdomain, c0 && c1, gs, endh - curr,
            curr + wordSemTheWord (holFapply s.store .heapLength))
        let (_i3, pa3, m3, c3) := wordGenGcPartialMoveData conf (2 ^ width)
          (other, i2, pa2, curr, m2, s.mdomain, gs, endh - curr)
        let (b1, m4, c4) := memcpy ((pa3 - other) >>> wordShiftAmount width)
          other (curr + gs) m3 s.mdomain
        let a := wordSemTheWord (holFapply s.store .allocSize)
        let s1 := s.store.updateListEq
            [(.currHeap, .word curr), (.otherHeap, .word other),
             (.nextFree, .word b1), (.genStart, .word (b1 - curr)),
             (.triggerGC, .word (b1 + newTrig (endh - b1) a genSizes)),
             (.globals, w1), (.globReal, globReal conf curr (w1)),
             (.temp 0, .word 0), (.temp 1, .word 0)]
        if wordGcFunAssum conf s.store ∧ c2 = true ∧ c3 = true ∧ c4 = true ∧
            a ≤ endh - b1 ∧ a ≤ newTrig (endh - b1) a genSizes then
          some { s with
            stack := s.stack.take s.stackSpace ++ ws2
            memory := m4
            store := s1
            regs := HolFiniteMapExact.empty }
        else none
      else
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
        if wordGcFunAssum conf s.store ∧ c1 = true ∧ c2 = true ∧ c3 = true
        then some { s with
          stack := s.stack.take s.stackSpace ++ ws2
          memory := m3
          store := s1
          regs := HolFiniteMapExact.empty } else none

/-- Flapjack proof infrastructure: a failed bitmap input cannot become a
successful partial collector through the reference-list pass. The existing
HOL `ref_list_ok` theorem supplies the implication; no success premise is added. -/
theorem partialRefList_false {width : Nat} [NeZero width] (k : Nat) (conf : Config)
    (pb i pa old gs rs re : BitVec width) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) :
    (wordGenGcPartialMoveRefList k conf
      (pb, i, pa, old, m, dm, false, gs, rs, re)).2.2.2 = false := by
  rcases h : wordGenGcPartialMoveRefList k conf
    (pb, i, pa, old, m, dm, false, gs, rs, re) with ⟨i1, pa1, m1, c1⟩
  cases c1 with
  | false => rfl
  | true =>
    have hf := wordGenGcPartialMoveRefList_ok k rs re pb pa old m i gs dm conf
      false i1 pa1 m1 h
    cases hf

open Classical in
/-- Assumption-failure case of the pending original generational `gc_thm`:
regardless of bitmap encoding, the collector cannot run without its assumption. -/
theorem gc_noAssum {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    {genSizes : List Nat} {s : StackSemStateFiniteExact width C F}
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes)
    (ha : ¬wordGcFunAssum conf s.store) : StackSemAllocation.gc s = none := by
  simp only [StackSemAllocation.gc]
  split
  · rfl
  · simp only [hgc, word_gc_fun_thm_generational hk, ha, not_false_eq_true, if_true]
    split <;> rfl

open Classical in
/-- Full-collector case of original1884; the case hypotheses select the original
branch and will be discharged by the assembling theorem. -/
theorem gc_full {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    {genSizes : List Nat} {s : StackSemStateFiniteExact width C F}
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes)
    (hlt : ¬s.stack.length < s.stackSpace)
    (ha : wordGcFunAssum conf s.store)
    (hp : ¬wordGenGcCanDoPartial genSizes s.store) :
    StackSemAllocation.gc s = gcExpanded conf genSizes s := by
  simp only [StackSemAllocation.gc, gcExpanded, hlt, if_false, hgc,
    word_gc_fun_thm_generational hk, ha, not_true_eq_false, hp, wordGenGcMoveRootsBitmaps]
  rcases wordGenGcMove conf (holFapply s.store .globals, 0,
    wordSemTheWord (holFapply s.store .otherHeap),
    wordSemTheWord (holFapply s.store .heapLength) >>> wordShiftAmount width,
    wordSemTheWord (holFapply s.store .otherHeap) + wordSemTheWord (holFapply s.store .heapLength),
    wordSemTheWord (holFapply s.store .currHeap), s.memory, s.mdomain)
    with ⟨w1, i1, pa1, ib1, pb1, m1, c1⟩
  rcases he : StackSem.encStack s.bitmaps (s.stack.drop s.stackSpace) with _ | wl
  · simp
  · simp only []
    rcases wordGenGcMoveRoots conf (wl, i1, pa1, ib1, pb1,
      wordSemTheWord (holFapply s.store .currHeap), m1, s.mdomain)
      with ⟨ws2, i2, pa2, ib2, pb2, m2, c2⟩
    dsimp only
    rcases hloop : wordGenGcMoveLoop conf
      (wordSemTheWord (holFapply s.store .heapLength) >>> wordShiftAmount width).toNat
      (wordSemTheWord (holFapply s.store .otherHeap), i2, pa2, ib2, pb2,
      wordSemTheWord (holFapply s.store .otherHeap) + wordSemTheWord (holFapply s.store .heapLength),
      wordSemTheWord (holFapply s.store .currHeap), m2, s.mdomain)
      with ⟨i3, pa3, ib3, pb3, m3, c3⟩
    simp only [BitVec.toNat_ushiftRight] at hloop
    rcases hd : StackSem.decStack s.bitmaps ws2 (s.stack.drop s.stackSpace) with _ | stack
    · cases c1 <;> cases c2 <;> cases c3 <;> simp_all
    · cases c1 <;> cases c2 <;> cases c3 <;> simp_all

open Classical in
/-- Partial-collector case of original1884. Branch conditions are discharged
by the final assembly; bitmap failure propagates through the reference pass. -/
theorem gc_partial {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    {genSizes : List Nat} {s : StackSemStateFiniteExact width C F}
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes)
    (hlt : ¬s.stack.length < s.stackSpace)
    (ha : wordGcFunAssum conf s.store)
    (hp : wordGenGcCanDoPartial genSizes s.store) :
    StackSemAllocation.gc s = gcExpanded conf genSizes s := by
  simp only [StackSemAllocation.gc, gcExpanded, hlt, if_false, hgc,
    word_gc_fun_thm_generational hk, ha, not_true_eq_false, hp, if_true,
    wordGenGcPartialMoveRoots_cons, wordGenGcPartialMoveRootsBitmaps]
  rcases wordGenGcPartialMove conf
    (holFapply s.store .globals,
      wordSemTheWord (holFapply s.store .genStart) >>> wordShiftAmount width,
      wordSemTheWord (holFapply s.store .otherHeap),
      wordSemTheWord (holFapply s.store .currHeap), s.memory, s.mdomain,
      wordSemTheWord (holFapply s.store .genStart),
      wordSemTheWord (holFapply s.store .endOfHeap) - wordSemTheWord (holFapply s.store .currHeap))
    with ⟨w1, i0, pa0, m0, c0⟩
  rcases he : StackSem.encStack s.bitmaps (s.stack.drop s.stackSpace) with _ | wl
  · simp [partialRefList_false]
  · simp only []
    rcases wordGenGcPartialMoveRoots conf
      (wl, i0, pa0, wordSemTheWord (holFapply s.store .currHeap), m0, s.mdomain,
      wordSemTheWord (holFapply s.store .genStart),
      wordSemTheWord (holFapply s.store .endOfHeap) - wordSemTheWord (holFapply s.store .currHeap))
      with ⟨ws2, i1, pa1, m1, c1⟩
    dsimp only
    rcases hr : wordGenGcPartialMoveRefList (2 ^ width) conf
      (wordSemTheWord (holFapply s.store .endOfHeap), i1, pa1,
      wordSemTheWord (holFapply s.store .currHeap), m1, s.mdomain, c0 && c1,
      wordSemTheWord (holFapply s.store .genStart),
      wordSemTheWord (holFapply s.store .endOfHeap) - wordSemTheWord (holFapply s.store .currHeap),
      wordSemTheWord (holFapply s.store .currHeap) + wordSemTheWord (holFapply s.store .heapLength))
      with ⟨i2, pa2, m2, c2⟩
    rcases hdata : wordGenGcPartialMoveData conf (2 ^ width)
      (wordSemTheWord (holFapply s.store .otherHeap), i2, pa2,
      wordSemTheWord (holFapply s.store .currHeap), m2, s.mdomain,
      wordSemTheWord (holFapply s.store .genStart),
      wordSemTheWord (holFapply s.store .endOfHeap) - wordSemTheWord (holFapply s.store .currHeap))
      with ⟨i3, pa3, m3, c3⟩
    rcases hcopy : memcpy ((pa3 - wordSemTheWord (holFapply s.store .otherHeap)) >>> wordShiftAmount width)
      (wordSemTheWord (holFapply s.store .otherHeap))
      (wordSemTheWord (holFapply s.store .currHeap) + wordSemTheWord (holFapply s.store .genStart))
      m3 s.mdomain with ⟨b1, m4, c4⟩
    rcases hd : StackSem.decStack s.bitmaps ws2 (s.stack.drop s.stackSpace) with _ | stack
    · simp only [Bool.and_false]
      simp [partialRefList_false]
      split <;> simp_all [holHd]
    · dsimp only
      cases c2 <;> cases c3 <;> cases c4 <;> simp_all [holHd]
      split <;> simp_all

/-- Canonical codec of the imported StackSem owner. Flapjack qualifier
infrastructure, re-exporting the checked actual carrier roundtrip. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

open Classical in
/-- Complete original generational `gc_thm` (line1884), with only the original
collector-function and kind hypotheses. The full statement is explicit rather
than hidden behind the working expression. The canonical owning StackSem
carrier uses finite-support regs/fpRegs/store; its codec witness is local. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem gc_thm_generational {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    {genSizes : List Nat} {s : StackSemStateFiniteExact width C F} :
    s.gcFun = wordGcFun conf ∧ conf.gcKind = .generational genSizes →
    StackSemAllocation.gc s =
  if s.stack.length < s.stackSpace then none else
      if ¬wordGcFunAssum conf s.store then none else
      if wordGenGcCanDoPartial genSizes s.store then
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
        let (i2, pa2, m2, c2) := wordGenGcPartialMoveRefList (2 ^ width) conf
          (endh, i1, pa1, curr, m1, s.mdomain, c0 && c1, gs, endh - curr,
            curr + wordSemTheWord (holFapply s.store .heapLength))
        let (_i3, pa3, m3, c3) := wordGenGcPartialMoveData conf (2 ^ width)
          (other, i2, pa2, curr, m2, s.mdomain, gs, endh - curr)
        let (b1, m4, c4) := memcpy ((pa3 - other) >>> wordShiftAmount width)
          other (curr + gs) m3 s.mdomain
        let a := wordSemTheWord (holFapply s.store .allocSize)
        let s1 := s.store.updateListEq
            [(.currHeap, .word curr), (.otherHeap, .word other),
             (.nextFree, .word b1), (.genStart, .word (b1 - curr)),
             (.triggerGC, .word (b1 + newTrig (endh - b1) a genSizes)),
             (.globals, w1), (.globReal, globReal conf curr (w1)),
             (.temp 0, .word 0), (.temp 1, .word 0)]
        if wordGcFunAssum conf s.store ∧ c2 = true ∧ c3 = true ∧ c4 = true ∧
            a ≤ endh - b1 ∧ a ≤ newTrig (endh - b1) a genSizes then
          some { s with
            stack := s.stack.take s.stackSpace ++ ws2
            memory := m4
            store := s1
            regs := HolFiniteMapExact.empty }
        else none
      else
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
        if wordGcFunAssum conf s.store ∧ c1 = true ∧ c2 = true ∧ c3 = true
        then some { s with
          stack := s.stack.take s.stackSpace ++ ws2
          memory := m3
          store := s1
          regs := HolFiniteMapExact.empty } else none := by
  rintro ⟨hgc, hk⟩
  change StackSemAllocation.gc s = gcExpanded conf genSizes s
  by_cases hlt : s.stack.length < s.stackSpace
  · simp only [StackSemAllocation.gc, gcExpanded, hlt, if_true]
  by_cases ha : wordGcFunAssum conf s.store
  · by_cases hp : wordGenGcCanDoPartial genSizes s.store
    · exact gc_partial hgc hk hlt ha hp
    · exact gc_full hgc hk hlt ha hp
  · rw [gc_noAssum hgc hk ha]
    simp only [gcExpanded, hlt, if_false, ha, not_false_eq_true, if_true]

end Flapjack.Compiler.Backend.StackAlloc.Generational

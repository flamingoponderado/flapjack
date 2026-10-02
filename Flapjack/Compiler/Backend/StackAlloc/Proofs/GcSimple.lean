import Flapjack.Compiler.Backend.StackAlloc.Proofs.GcBitmaps
import Flapjack.Compiler.Backend.Semantics.StackSem.Allocation

/-!
# `stack_allocProof` Simple-collector unfolding

`word_gc_fun_thm` (`stack_allocProofScript.sml:481-517`) and `gc_thm`
(`stack_allocProofScript.sml:554-~605`) for `conf.gc_kind = Simple`: the
store-level `word_gc_fun` and the StackSem `gc` step unfolded into the
`word_gc_move` / `word_gc_move_roots(_bitmaps)` / `word_gc_move_loop`
composition that the GC code simulation theorems follow. HOL's `s ' X` is
`holFapply`, its `theWord` is `wordSemTheWord`, and `dimword (:'a)` is `2 ^ width`.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions

open Classical in
/-- Exact HOL `word_gc_fun_thm` (`stack_allocProofScript.sml:481-517`), the
Simple-collector unfolding of `word_gc_fun`; HOL's free `roots m dm s` and
`conf` are implicit and the store binder `s` is the canonical finite map. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_fun_thm" 481
  (fmap_as_finite_support_relation := [s]) (words_as_type_indexed_bitvec)]
theorem word_gc_fun_thm {width : Nat} [NeZero width] {conf : Config}
    {roots : List (WordLocW width)} {m : BitVec width → WordLocW width}
    {dm : BitVec width → Bool} {s : HolFiniteMapExact WordStoreHOL (WordLocW width)} :
    conf.gcKind = .simple →
    wordGcFun conf (roots, m, dm, s) =
      let (w1, i1, pa1, m1, c1) :=
        wordGcMove conf (holFapply s .globals, 0, wordSemTheWord (holFapply s .otherHeap),
          wordSemTheWord (holFapply s .currHeap), m, dm)
      let (ws2, i2, pa2, m2, c2) :=
        wordGcMoveRoots conf (roots, i1, pa1, wordSemTheWord (holFapply s .currHeap), m1, dm)
      let (_i1, pa1, m1, c2) :=
        wordGcMoveLoop (2 ^ width) conf (wordSemTheWord (holFapply s .otherHeap), i2, pa2,
          wordSemTheWord (holFapply s .currHeap), m2, dm, c1 && c2)
      let s1 := s.updateListEq
        [(.currHeap, .word (wordSemTheWord (holFapply s .otherHeap))),
         (.otherHeap, .word (wordSemTheWord (holFapply s .currHeap))),
         (.nextFree, .word pa1),
         (.triggerGC, .word (wordSemTheWord (holFapply s .otherHeap) +
            wordSemTheWord (holFapply s .heapLength))),
         (.endOfHeap, .word (wordSemTheWord (holFapply s .otherHeap) +
            wordSemTheWord (holFapply s .heapLength))),
         (.globals, w1),
         (.globReal, globReal conf (wordSemTheWord (holFapply s .otherHeap)) w1)]
      if wordGcFunAssum conf s ∧ c2 = true then some (ws2, m1, s1) else none := by
  intro hk
  simp only [wordGcFun, hk, wordFullGc, wordGcMoveRoots_cons]
  rcases wordGcMove conf (holFapply s .globals, 0, wordSemTheWord (holFapply s .otherHeap),
    wordSemTheWord (holFapply s .currHeap), m, dm) with ⟨w1, i1, pa1, m1, c1⟩
  rcases wordGcMoveRoots conf (roots, i1, pa1, wordSemTheWord (holFapply s .currHeap), m1, dm)
    with ⟨ws2, i2, pa2, m2, c2⟩
  rcases wordGcMoveLoop (2 ^ width) conf (wordSemTheWord (holFapply s .otherHeap), i2, pa2,
    wordSemTheWord (holFapply s .currHeap), m2, dm, c1 && c2) with ⟨i3, pa3, m3, c3⟩
  simp [holHd]

namespace GcSimpleSupport

/-- Canonical finite-support codec of the owning StackSem state carrier, required
by the `fmap_as_finite_support` qualifier of `gc_thm`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

end GcSimpleSupport

/-- The Simple collector's loop with a failed input flag fails. -/
theorem wordGcMoveLoop_false_snd {width : Nat} [NeZero width] (k : Nat) (conf : Config)
    (pb i pa old : BitVec width) (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) :
    (wordGcMoveLoop k conf (pb, i, pa, old, m, dm, false)).2.2.2 = false := by
  rcases h : wordGcMoveLoop k conf (pb, i, pa, old, m, dm, false) with ⟨i1, pa1, m1, c1⟩
  simpa using wordGcMoveLoop_F k conf pb i pa old m dm i1 pa1 m1 c1 h

open Classical in
/-- Exact HOL `gc_thm` (`stack_allocProofScript.sml:554`, the Simple-collector
declaration), the StackSem `gc` step under `word_gc_fun conf` with
`conf.gc_kind = Simple`; HOL's free `s` and `conf` are implicit. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "gc_thm" 554
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem gc_thm {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    {s : StackSemStateFiniteExact width C F} :
    s.gcFun = wordGcFun conf ∧ conf.gcKind = .simple →
    StackSemAllocation.gc s =
      if s.stack.length < s.stackSpace then none else
        let unused := s.stack.take s.stackSpace
        let stack := s.stack.drop s.stackSpace
        let (w1, i1, pa1, m1, c1) :=
          wordGcMove conf (holFapply s.store .globals, 0,
            wordSemTheWord (holFapply s.store .otherHeap),
            wordSemTheWord (holFapply s.store .currHeap), s.memory, s.mdomain)
        let (stack, i2, pa2, m2, c2) :=
          wordGcMoveRootsBitmaps conf (stack, s.bitmaps, i1, pa1,
            wordSemTheWord (holFapply s.store .currHeap), m1, s.mdomain)
        let (_i1, pa1, m1, c2) :=
          wordGcMoveLoop (2 ^ width) conf (wordSemTheWord (holFapply s.store .otherHeap), i2, pa2,
            wordSemTheWord (holFapply s.store .currHeap), m2, s.mdomain, c1 && c2)
        let s1 := s.store.updateListEq
          [(.currHeap, .word (wordSemTheWord (holFapply s.store .otherHeap))),
           (.otherHeap, .word (wordSemTheWord (holFapply s.store .currHeap))),
           (.nextFree, .word pa1),
           (.triggerGC, .word (wordSemTheWord (holFapply s.store .otherHeap) +
              wordSemTheWord (holFapply s.store .heapLength))),
           (.endOfHeap, .word (wordSemTheWord (holFapply s.store .otherHeap) +
              wordSemTheWord (holFapply s.store .heapLength))),
           (.globals, w1),
           (.globReal, globReal conf (wordSemTheWord (holFapply s.store .otherHeap)) w1)]
        if wordGcFunAssum conf s.store ∧ c2 = true then
          some { s with
            stack := unused ++ stack
            store := s1
            regs := HolFiniteMapExact.empty
            memory := m1 }
        else none := by
  rintro ⟨hgc, hk⟩
  simp only [StackSemAllocation.gc]
  by_cases hlt : s.stack.length < s.stackSpace
  · simp only [hlt, if_true]
  simp only [hlt, if_false, hgc, word_gc_fun_thm hk, wordGcMoveRootsBitmaps]
  rcases wordGcMove conf (holFapply s.store .globals, 0,
    wordSemTheWord (holFapply s.store .otherHeap),
    wordSemTheWord (holFapply s.store .currHeap), s.memory, s.mdomain) with ⟨w1, i1, pa1, m1, c1⟩
  rcases he : StackSem.encStack s.bitmaps (s.stack.drop s.stackSpace) with _ | wl
  · simp [wordGcMoveLoop_false_snd]
  simp only []
  generalize wordGcMoveRoots conf (wl, i1, pa1, wordSemTheWord (holFapply s.store .currHeap), m1,
    s.mdomain) = R
  obtain ⟨ws2, i2, pa2, m2, c2⟩ := R
  dsimp only
  rcases hd : StackSem.decStack s.bitmaps ws2 (List.drop s.stackSpace s.stack) with _ | st
  · by_cases hP : wordGcFunAssum conf s.store ∧
        (wordGcMoveLoop (2 ^ width) conf (wordSemTheWord (holFapply s.store .otherHeap), i2, pa2,
          wordSemTheWord (holFapply s.store .currHeap), m2, s.mdomain, c1 && c2)).2.2.2 = true
    · simp [hP, hd, wordGcMoveLoop_false_snd]
    · simp [hP, wordGcMoveLoop_false_snd]
  · generalize wordGcMoveLoop (2 ^ width) conf (wordSemTheWord (holFapply s.store .otherHeap), i2,
      pa2, wordSemTheWord (holFapply s.store .currHeap), m2, s.mdomain, c1 && c2) = L
    obtain ⟨i3, pa3, m3, c3⟩ := L
    by_cases hP : wordGcFunAssum conf s.store ∧ c3 = true
    · simp [hP, hd]
    · simp [hP]

end Flapjack.Compiler.Backend.StackAlloc

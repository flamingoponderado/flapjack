import Flapjack.Compiler.Backend.StackAlloc.Proofs.AllocGenerational
import Flapjack.Compiler.Backend.StackAlloc.Proofs.AllocNone
import Flapjack.Compiler.Backend.StackAlloc.Proofs.AllocSimple

/-! Original allocation correctness theorem, assembled along HOL's
garbage collector kind split. All branches evaluate the actual wordGcCode. -/
namespace Flapjack.Compiler.Backend.StackAlloc.AllocCorrect
open Flapjack Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.StackSemEvaluate

/-- Canonical codec for the imported owning StackSem state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Original allocation dispatch theorem (5078-5105), retaining
all original premises and all four original conclusions. The proof exhausts
the original garbage collector kinds internally; no case-selection premise remains.
Canonical regs/fpRegs/store and positive-width words are the only carrier
translations; total instruction closure inherits the rational-cut limit. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml"
  "alloc_correct_lemma"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem alloc_correct_lemma {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {c : DataToWord.Config}
    {w : BitVec width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} {l : HolFiniteMapExact Nat (WordLocW width)}
    {ret : WordLocW width} {anything : WordSemGcFun width}
    (ha : StackSemAllocation.alloc w s = (r, t)) (hr : r ≠ some .error)
    (hgc : s.gcFun = wordGcFun conf)
    (hbl : s.bitmaps.length < 2 ^ width - 1)
    (hstack : s.stack.length * (width / 8) < 2 ^ width)
    (hl0 : l.lookup 0 = some ret) (hl1 : l.lookup 1 = some (.word w))
    :
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
  cases hk : conf.gcKind with
  | none => exact Flapjack.Compiler.Backend.StackAlloc.alloc_correct_lemma_None ⟨ha, hr, hgc, hk, hbl, hstack, hl0, hl1⟩
  | simple => exact Flapjack.Compiler.Backend.StackAlloc.alloc_correct_lemma_Simple ⟨ha, hr, hgc, hk, hbl, hstack, hl0, hl1⟩
  | generational sizes =>
      exact AllocGenerational.alloc_correct_lemma_Generational ha hr hgc hk hbl hstack hl0 hl1

end Flapjack.Compiler.Backend.StackAlloc.AllocCorrect

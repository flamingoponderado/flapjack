import Flapjack.Compiler.Backend.StackAlloc.Proofs.AllocGenerational.Full

/-! Whole original generational allocation theorem, assembled along HOL's
partial/full selector split. Both branches evaluate the actual wordGcCode. -/
namespace Flapjack.Compiler.Backend.StackAlloc.AllocGenerational
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

/-- Whole original generational allocation theorem (4592-5016), retaining
all original premises and all four original conclusions. The proof exhausts
the original partial selector internally; no case-selection premise remains.
Canonical regs/fpRegs/store and positive-width words are the only carrier
translations; total instruction closure inherits the rational-cut limit. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem alloc_correct_lemma_Generational {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {genSizes : List Nat} {c : DataToWord.Config}
    {w : BitVec width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} {l : HolFiniteMapExact Nat (WordLocW width)}
    {ret : WordLocW width} {anything : WordSemGcFun width}
    (ha : StackSemAllocation.alloc w s = (r, t)) (hr : r ≠ some .error)
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes)
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
  by_cases hp : wordGenGcCanDoPartial genSizes (setStore .allocSize (.word w) s).store
  · exact AllocGenerationalPartial.alloc_correct_lemma_Generational_partial
      ha hr hgc hk hbl hstack hl0 hl1 hp
  · exact AllocGenerationalFull.alloc_correct_lemma_Generational_full
      ha hr hgc hk hbl hstack hl0 hl1 hp

end Flapjack.Compiler.Backend.StackAlloc.AllocGenerational

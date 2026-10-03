import Flapjack.Compiler.Backend.StackAlloc.Proofs.AllocGenerational
import Flapjack.Compiler.Backend.StackAlloc.Proofs.AllocNone
import Flapjack.Compiler.Backend.StackAlloc.Proofs.AllocSimple
import Flapjack.Compiler.Backend.StackProps.AllocationConstants
import Flapjack.Compiler.Backend.StackProps.StackLengths

/-! Original allocation correctness theorem, assembled along HOL's
garbage collector kind split. All branches evaluate the actual wordGcCode. -/
namespace Flapjack.Compiler.Backend.StackAlloc.AllocCorrect
open Flapjack Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.StackSemEvaluate Flapjack.Compiler.Backend.StackLang

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

/-- HOL's `find_code` of the stub location in the compiled code: the first
association of `compile c` is the GC stub `Seq (word_gc_code c) (Return 0)`. -/
theorem findCode_gcStub_compile {width : Nat} [NeZero width] {κ : Type}
    (c : DataToWord.Config) (regs : HolFiniteMapExact κ (WordLocW width))
    (code : List (Nat × HolProg width)) :
    StackSemControl.findCode (.inl gcStubLocation) regs (sptFromAList (compile c code)) =
      some (.seq (wordGcCode c) (.ret 0)) := by
  simp [StackSemControl.findCode, sptLookup_sptFromAList, compile, stubs, sptAListLookup]

/-- Original `alloc_correct` (`stack_allocProofScript.sml:5107-5135`): the
allocation step is simulated by the returning call to the GC stub that `comp`
emits for `Alloc`. HOL's free `w s r t c l n' m anything` are implicit, and all
five original premises are kept; the repeated `use_alloc := F` update of the
source record is a single field update. The proof follows HOL: the stub is found
in the compiled code, its body runs `word_gc_code` by `alloc_correct_lemma`
started from `l |+ (0, Loc n' m)`, and `Return 0` returns to `Skip`. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml"
  "alloc_correct"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem alloc_correct {width : Nat} [NeZero width] {C F : Type}
    {c : DataToWord.Config} {w : BitVec width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} {l : HolFiniteMapExact Nat (WordLocW width)}
    {n' m : Nat} {anything : WordSemGcFun width}
    (ha : StackSemAllocation.alloc w s = (r, t)) (hr : r ≠ some .error)
    (hgc : s.gcFun = wordGcFun c)
    (hbl : s.bitmaps.length < 2 ^ width - 1)
    (hstack : s.stack.length * (width / 8) < 2 ^ width)
    (hl1 : l.lookup 1 = some (.word w)) :
    ∃ ck l2,
      evaluate (.call (some (.skip, 0, n', m)) (.inl gcStubLocation) none, { s with
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
      t.regs.submap l2 := by
  have hl0' : (l.updateEq (0, .loc n' m)).lookup 0 = some (.loc n' m) := by
    simp [HolFiniteMapExact.updateEq, FUPDATE_HOL]
  have hl1' : (l.updateEq (0, .loc n' m)).lookup 1 = some (.word w) := by
    simpa [HolFiniteMapExact.updateEq, FUPDATE_HOL] using hl1
  obtain ⟨ck, l2, hev, hhalt, hsub, hret⟩ :=
    alloc_correct_lemma (conf := c) (c := c) (anything := anything)
      ha hr hgc hbl hstack hl0' hl1'
  have htc : t.clock = s.clock :=
    (StackPropsAllocationConstants.allocConst w s t r ha).2.1
  refine ⟨ck + 1, l2, ?_, hsub⟩
  rw [evaluate_call]
  simp only [findCode_gcStub_compile]
  rw [if_neg (by simp)]
  have hstate : decClock (setVar 0 (.loc n' m) { s with
        useStore := true, useStack := true, useAlloc := false, clock := s.clock + (ck + 1),
        regs := l, gcFun := anything,
        code := sptFromAList (compile c (sptToAList s.code)) }) =
      { s with
        useStore := true, useStack := true, useAlloc := false, clock := s.clock + ck,
        regs := l.updateEq (0, .loc n' m), gcFun := anything,
        code := sptFromAList (compile c (sptToAList s.code)) } := by
    simp [decClock, setVar]
  rw [hstate, evaluate_seq, hev]
  rcases r with _ | r
  · have h0 := hret rfl
    simp only [StackSemControl.fixClock, htc, show min (s.clock + ck) s.clock = s.clock by omega]
    rw [evaluate_ret]
    simp only [getVar, h0]
    simp [evaluate_skip]
  · have hh := hhalt (by simp)
    simp only [Option.some.injEq] at hh
    subst hh
    simp [StackSemControl.fixClock, htc]

/-- Original `alloc_length_stack` (`stack_allocProofScript.sml:5146-5157`):
an allocation that does not halt keeps the stack length. HOL's `c` is the
requested word and `conf` the GC configuration; the `gc_fun` premise is kept
as in the source although the length argument only uses `dec_stack_length`. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml"
  "alloc_length_stack"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem alloc_length_stack {width : Nat} [NeZero width] {C F : Type}
    {c : BitVec width} {conf : Config} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)}
    (ha : StackSemAllocation.alloc c s = (r, t)) (_hgc : s.gcFun = wordGcFun conf)
    (hh : ∀ w, r ≠ some (.halt w)) :
    t.stack.length = s.stack.length := by
  have hg : ∀ g, StackSemAllocation.gc (setStore .allocSize (.word c) s) = some g →
      g.stack.length = s.stack.length := by
    intro g h
    simp only [StackSemAllocation.gc, setStore] at h
    by_cases hsp : s.stack.length < s.stackSpace
    · simp [hsp] at h
    simp only [hsp, if_false] at h
    split at h
    · simp at h
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i stack' hdec
    simp only [Option.some.injEq] at h
    subst h
    have hl := StackPropsStackLengths.decStackLength _ _ _ _ hdec
    simp only [List.length_append, List.length_take, ← hl, List.length_drop]
    omega
  simp only [StackSemAllocation.alloc] at ha
  split at ha
  · simp only [Prod.mk.injEq] at ha
    rw [← ha.2]
  rename_i g hgs
  have hlen := hg g hgs
  split at ha
  · simp only [Prod.mk.injEq] at ha
    rw [← ha.2, hlen]
  split at ha
  · simp only [Prod.mk.injEq] at ha
    rw [← ha.2, hlen]
  · simp only [Prod.mk.injEq] at ha
    rw [← ha.2, hlen]
  · simp only [Prod.mk.injEq] at ha
    exact absurd ha.1.symm (hh _)

end Flapjack.Compiler.Backend.StackAlloc.AllocCorrect

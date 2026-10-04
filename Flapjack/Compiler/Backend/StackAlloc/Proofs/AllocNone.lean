import Flapjack.Compiler.Backend.StackAlloc.Proofs.AllocSimple
import Flapjack.Compiler.Backend.StackAlloc.Proofs.Bitmap

/-!
# `stack_allocProof` `alloc_correct_lemma_None`

`alloc_correct_lemma_None` of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml` (5018-5076): with the
`None` collector, the StackSem `alloc` step (which keeps the stack, as
`enc_dec_stack` shows, and points `NextFree`, `TriggerGC` and `EndOfHeap` at the
current heap) is simulated by the straight-line `word_gc_code`, which halts
unless the request is for zero words.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackRemove (constInst)

namespace AllocNoneSupport

/-- Canonical finite-support codec of the owning StackSem state carrier, required
by the `fmap_as_finite_support` qualifier of `alloc_correct_lemma_None`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

end AllocNoneSupport

open Classical in
/-- Exact HOL `alloc_correct_lemma_None` (`stack_allocProofScript.sml:5018-5076`):
with the `None` collector, `alloc` is simulated by `word_gc_code`. HOL's free
`w s r t conf l ret c anything` are implicit; `fromAList`/`toAList` are
`sptFromAList`/`sptToAList`, `SUBMAP` is `HolFiniteMapExact.submap`, and
`dimword (:'a)` is `2 ^ width`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem alloc_correct_lemma_None {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    {c : DataToWord.Config} {w : BitVec width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} {l : HolFiniteMapExact Nat (WordLocW width)}
    {ret : WordLocW width} {anything : WordSemGcFun width} :
    StackSemAllocation.alloc w s = (r, t) ∧ r ≠ some .error ∧
      s.gcFun = wordGcFun conf ∧ conf.gcKind = .none ∧
      s.bitmaps.length < 2 ^ width - 1 ∧
      s.stack.length * (width / 8) < 2 ^ width ∧
      l.lookup 0 = some ret ∧ l.lookup 1 = some (.word w) →
    ∃ ck l2,
      evaluate (wordGcCode conf, { s with
          useStore := true, useStack := true, useAlloc := false
          clock := s.clock + ck, regs := l, gcFun := anything
          code := sptFromAList (compile c (sptToAList s.code)) }) =
        (r, { t with
          useStore := true, useStack := true, useAlloc := false
          code := sptFromAList (compile c (sptToAList s.code))
          regs := l2, gcFun := anything }) ∧
      (r ≠ none → r = some (.halt (.word 1))) ∧
      t.regs.submap l2 ∧
      (r = none → l2.lookup 0 = some ret) := by
  rintro ⟨hA, hr, hgc, hk, -, -, hl0, hl1⟩
  rw [StackSemAllocation.alloc] at hA
  simp only [StackSemAllocation.gc, setStore] at hA
  by_cases hsp : s.stack.length < s.stackSpace
  · simp only [hsp, if_true, Prod.mk.injEq] at hA
    exact absurd hA.1.symm hr
  simp only [hsp, if_false] at hA
  rcases he : StackSem.encStack s.bitmaps (s.stack.drop s.stackSpace) with _ | roots
  · simp only [he, Prod.mk.injEq] at hA
    exact absurd hA.1.symm hr
  simp only [he, hgc, wordGcFun, hk] at hA
  by_cases hc : wordGcFunAssum conf (s.store.updateEq (.allocSize, .word w))
  swap
  · simp only [hc, if_false, Prod.mk.injEq] at hA
    exact absurd hA.1.symm hr
  simp only [hc, if_true] at hA
  rcases hd : StackSem.decStack s.bitmaps roots (s.stack.drop s.stackSpace) with _ | x2
  · simp only [hd, Prod.mk.injEq] at hA
    exact absurd hA.1.symm hr
  have hx2 := enc_dec_stack s.bitmaps _ roots x2 ⟨he, hd⟩
  subst hx2
  simp only [hd] at hA
  obtain ⟨hdom, -, hwc, -⟩ := hc
  obtain ⟨curr, hcurr⟩ := (isWord_thm _).1 hwc
  have hlc : s.store.lookup .currHeap = some (.word curr) := by
    have h1 := hdom .currHeap (by simp)
    simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at h1
    have hc' := hcurr
    rw [holFapply_updateEq_ne _ _ _ _ (by decide)] at hc'
    rcases h : s.store.lookup .currHeap with _ | v
    · simp [h] at h1
    · simp [holFapply, h] at hc'
      rw [hc']
  rw [hcurr] at hA
  simp only [wordSemTheWord] at hA
  have hcode : (wordGcCode conf : HolProg width) =
      listSeqHOL [.set .allocSize 1, .get 2 .currHeap, .set .nextFree 2, .set .triggerGC 2,
        .set .endOfHeap 2, .ite .test 1 (.reg 1) .skip (.seq (constInst 1 1) (.halt 1))] := by
    simp only [wordGcCode, hk]
  by_cases hw0 : w = 0
  · subst hw0
    simp [StackSemAllocation.hasSpace, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq] at hA
    obtain ⟨rfl, rfl⟩ := hA
    refine ⟨0, l.updateEq (2, .word curr), ?_, by simp, ?_, ?_⟩
    · have h00 : (AndOp.and (0#width) (0#width) == 0#width) = true := by
        change (0#width &&& 0#width == 0#width) = true
        simp
      rw [hcode]
      simp [listSeqHOL, evaluate_seq, evaluate_set, evaluate_get, evaluate_ite, evaluate_skip,
        getVar, setVar, setStore, fixClock, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
        wordSemWordCmp, wordCmpHOL, StackSemRegisterTransfers.storeOfSyntax,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hl1, hlc, h00]
      apply regs_ext
      intro k
      simp [HolFiniteMapExact.lookup_updateEq, HolFiniteMapExact.lookup_updateListEq, FUPDATE_HOL,
        FUPDATE_LIST_HOL]
    · intro k v hkv
      simp [HolFiniteMapExact.lookup_empty] at hkv
    · intro _
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hl0]
  · have hw0' : ¬ w.toNat ≤ 0 := by
      intro h
      exact hw0 (BitVec.eq_of_toNat_eq (by simp; omega))
    simp [StackSemAllocation.hasSpace, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq, hw0'] at hA
    obtain ⟨rfl, rfl⟩ := hA
    have hww : (AndOp.and w w == 0#width) = false := by
      have : ¬ AndOp.and w w = 0#width := by
        change ¬ w &&& w = 0#width
        simpa using hw0
      simpa using this
    refine ⟨0, HolFiniteMapExact.empty, ?_, fun _ => rfl, ?_, fun h => by cases h⟩
    · rw [hcode]
      simp [listSeqHOL, evaluate_seq, evaluate_set, evaluate_get, evaluate_ite, evaluate_inst,
        evaluate_halt, constInst, StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
        StackSemExpressions.assign, StackSemExpressions.wordExp, getVar, setVar, setStore, fixClock, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
        wordSemWordCmp, wordCmpHOL, StackSemRegisterTransfers.storeOfSyntax, emptyEnv,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hl1, hlc, hww]
      apply regs_ext
      intro k
      simp [HolFiniteMapExact.lookup_updateEq, HolFiniteMapExact.lookup_updateListEq, FUPDATE_HOL,
        FUPDATE_LIST_HOL]
    · intro k v hkv
      simp [emptyEnv, HolFiniteMapExact.lookup_empty] at hkv

end Flapjack.Compiler.Backend.StackAlloc

import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadRegister
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Seq
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallHelpers
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateLaws

namespace Flapjack.WordToStackProofs.CompCorrect.Return
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Flapjack factoring of the original Return case's frame-release step.
The original full constructor must derive `count ≤ f` from its canonical
return convention and original maximum-variable premise. This helper retains
the entire state relation; it is not independently tagged as comp_correct. -/
theorem stateRelReturnFlush {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame count : Nat}
    {source : WordSemStateFiniteExact width (Nat × C) F}
    {target : StackSemStateFiniteExact width C F} {lens : List Nat}
    (related : stateRel ac k f frame source target lens 0) (countBound : count ≤ f) :
    stateRel ac k 0 0 (WordSemStateFiniteExact.flushState false source)
      {target with stackSpace := target.stackSpace + f - count} lens count := by
  unfold stateRel at related ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36,
    h37, h38, hloc⟩ := related
  simp only [WordSemStateFiniteExact.flushState]
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32,
    by omega, h34, by simp, by simp [sptWf], ?_, ?_, ?_⟩
  · rcases h37 with ⟨_, limit, maxima⟩
    refine ⟨by simp, limit, ?_⟩
    intro maximum bound
    obtain ⟨space, _, size, stackSize, sizeEq⟩ := maxima maximum bound
    have remaining : target.stack.length - (target.stackSpace + f - count) - 0 - count =
        target.stack.length - target.stackSpace - f - 0 := by omega
    rw [remaining]
    exact ⟨space, by simp, size, stackSize, sizeEq⟩
  · have released : target.stackSpace + f - count + count = target.stackSpace + f := by omega
    simpa only [Nat.add_zero, List.drop_zero, List.drop_drop, released] using h38
  · intro n value lookup
    simp [sptLookup] at lookup

/-- Flapjack factoring of the original Return convention/max-variable split.
All bounds here are consequences of the original full hypotheses, including
the zero-frame case; no additional range assumption is introduced. -/
theorem returnFacts {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame register : Nat} {values : List Nat}
    {source : WordSemStateFiniteExact width (Nat × C) F}
    {target : StackSemStateFiniteExact width C F} {lens : List Nat}
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k (.return register values : WordLangProgHOL (BitVec width)) = true)
    (maximum : maxVarHOL (.return register values : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    register % 2 = 0 ∧
    values = (List.range values.length).map (fun i => 2 * (i + 1)) ∧
    values.length < frame + k ∧ Compiler.Backend.WordToStack.numStackRet k values ≤ f := by
  simp only [postAllocConventionsHOL, Bool.and_eq_true] at conventions
  obtain ⟨physical, _, arguments⟩ := conventions
  rw [everyVarHOL] at physical
  rw [callArgConventionHOL] at arguments
  simp only [Bool.and_eq_true, beq_iff_eq] at physical arguments
  have even : register % 2 = 0 := by
    simpa only [isPhyVar, decide_eq_true_eq] using physical.1
  have lengthBound : values.length < frame + k := by
    rw [maxVarHOL, maxList] at maximum
    rcases Nat.eq_zero_or_pos values.length with empty | nonempty
    · omega
    · have member : 2 * ((values.length - 1) + 1) ∈ values := by
        have mapped : 2 * ((values.length - 1) + 1) ∈
            (List.range values.length).map (fun i => 2 * (i + 1)) := List.mem_map.mpr
          ⟨values.length - 1, List.mem_range.mpr (by omega),
            (rfl : 2 * ((values.length - 1) + 1) = 2 * ((values.length - 1) + 1))⟩
        rwa [← arguments] at mapped
      have upper := maxList_ge_of_mem values _ member
      omega
  have shape : if frame = 0 then f = 0 else f = frame + 1 := by
    unfold stateRel at related
    aesop (config := { enableSimp := false })
  refine ⟨even, arguments, lengthBound, ?_⟩
  unfold Compiler.Backend.WordToStack.numStackRet
  split at shape <;> omega

/-- Flapjack infrastructure for the complete optional observation of a
successful native read. No source index bound is assumed. -/
private theorem readAt {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (ns : List Nat) (xs : List (WordLocW width))
    (h : WordSemStateFiniteExact.getVars ns s = some xs) (i : Nat) :
    xs[i]? = (ns[i]?).bind (fun n => WordSemStateFiniteExact.getVar n s) := by
  induction ns generalizing xs i with
  | nil => simp [WordSemStateFiniteExact.getVars] at h; subst xs; simp
  | cons n ns ih =>
    cases hv : WordSemStateFiniteExact.getVar n s with
    | none => simp [WordSemStateFiniteExact.getVars, hv] at h
    | some v =>
      cases ht : WordSemStateFiniteExact.getVars ns s with
      | none => simp [WordSemStateFiniteExact.getVars, hv, ht] at h
      | some vs =>
        simp only [WordSemStateFiniteExact.getVars, hv, ht, Option.some.injEq] at h
        subst xs
        cases i with
        | zero => simp [hv]
        | succ i => simpa using ih vs ht i

/-- Flapjack factoring of every original Return-value physical placement.
Canonical source lookup and full state_rel supply actual register/spill values;
the release bound is derived by returnFacts in the full constructor. -/
theorem returnPlacements {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat} {names : List Nat}
    {values : List (WordLocW width)}
    {source : WordSemStateFiniteExact width (Nat × C) F}
    {target : StackSemStateFiniteExact width C F} {lens : List Nat}
    (related : stateRel ac k f frame source target lens 0)
    (canonical : names = (List.range names.length).map (fun i => 2 * (i + 1)))
    (reads : WordSemStateFiniteExact.getVars names source = some values)
    (countBound : Compiler.Backend.WordToStack.numStackRet k names ≤ f) :
    ∀ i, i < values.length →
      if i + 1 < k then target.regs.lookup (i + 1) = some (holEl i values)
      else (target.stack.drop (target.stackSpace + f -
        Compiler.Backend.WordToStack.numStackRet k names))[values.length - (i + 1)]? =
        some (holEl i values) := by
  have lengths := WordSemStateFiniteExact.getVarsLengthLemma names source values reads
  intro i bound
  have read := readAt source names values reads i
  have nameAt : names[i]? = some (2 * (i + 1)) := by
    have nbound : i < names.length := by omega
    rw [canonical]
    simp only [List.getElem?_map, List.getElem?_range, nbound, Option.map_some]
  rw [List.getElem?_eq_getElem bound, nameAt, Option.bind_some,
    ← holEl_eq_getElem i values bound] at read
  have placement := StateRelGetVar.stateRel_locals related (2 * (i + 1)) (holEl i values) read.symm
  have index : 2 * (i + 1) / 2 = i + 1 := by omega
  rw [index] at placement
  by_cases physical : i + 1 < k
  · rw [if_pos physical] at placement ⊢
    exact placement.2
  · rw [if_neg physical] at placement ⊢
    obtain ⟨_, slot, _⟩ := placement
    rw [Nat.add_zero, List.getElem?_take, List.getElem?_drop] at slot
    split at slot
    swap
    · cases slot
    rw [List.getElem?_drop]
    unfold Compiler.Backend.WordToStack.numStackRet at countBound ⊢
    have offset : target.stackSpace + f - (names.length + 1 - k) +
        (values.length - (i + 1)) = target.stackSpace + (f - 1 - (i + 1 - k)) := by omega
    rw [offset]
    exact slot

/-- Genuine canonical source codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Genuine canonical target codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness




/-- Complete original Return constructor simulation. Source reads and every
release/placement obligation are derived from the original full motive.
The native evaluator closure inherits reals_as_rational_cuts; this
structural case makes no additional numerical FP correspondence claim. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectReturn {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (register : Nat) (names : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Seq.Simulation ac (.return register names) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution, notError, related, conventions, flat,
    compilation, lengthBound, bitmapBound, bitmapPrefix, labels, maximum⟩
  rw [WordSemStateFiniteExact.evaluate] at execution
  cases sourceRead : WordSemStateFiniteExact.getVar register source with
  | none =>
    simp only [sourceRead, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  | some address =>
    cases address with
    | word word =>
      simp only [sourceRead, Prod.mk.injEq] at execution
      exact absurd execution.1.symm notError
    | loc first second =>
      cases sourceValues : WordSemStateFiniteExact.getVars names source with
      | none =>
        simp only [sourceRead, sourceValues, Prod.mk.injEq] at execution
        exact absurd execution.1.symm notError
      | some values =>
        simp only [sourceRead, sourceValues, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        obtain ⟨even, canonical, nameBound, countBound⟩ := returnFacts related conventions maximum
        rcases format : Compiler.Backend.WordToStackRegFormat.wReg1 register (k, f, frame) with ⟨loads, output⟩
        simp only [compNative, format, Prod.mk.injEq] at compilation
        obtain ⟨rfl, _⟩ := compilation
        obtain ⟨loaded, loadRun, clockSame, loadRelated, stackLength, spaceSame, bitmapSame,
          preserved, outputNotScratch, outputValue⟩ :=
          LoadRegister.evaluateWStackLoadWReg1 ac k f frame register output loads
            source target lens (.loc first second) format even sourceRead related
        let count := Compiler.Backend.WordToStack.numStackRet k names
        let free := Compiler.Backend.WordToStack.skipFree k f frame names
        let post : StackSemStateFiniteExact width C F :=
          {loaded with stackSpace := loaded.stackSpace + free}
        have freeSpace : loaded.stackSpace + free = loaded.stackSpace + f - count := by
          dsimp [free, count, Compiler.Backend.WordToStack.skipFree]
          omega
        have useStack : loaded.useStack = true := loadRelated.2.2.2.2.1
        have frameBound : loaded.stackSpace + f ≤ loaded.stack.length := by
          unfold stateRel at loadRelated
          aesop (config := { enableSimp := false })
        have freeBound : loaded.stackSpace + free ≤ loaded.stack.length := by
          dsimp [free, Compiler.Backend.WordToStack.skipFree]
          omega
        refine ⟨0, post, some (.result (.loc first second)), ?_, ?_⟩
        · simp only [Nat.add_zero]
          rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq, loadRun]
          simp only [StackSemControl.fixClock, clockSame, Nat.min_self]
          rw [CallHelpers.evaluateSeqStackFree free (.ret output) loaded
            ⟨useStack, by omega⟩]
          rw [StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_stackFree,
            if_neg (by simp [useStack]), if_neg (by omega)]
          simp only [StackSemControl.fixClock, Nat.min_self]
          rw [StackSemEvaluate.evaluate_ret]
          simp only [StackSemStateOps.getVar] at outputValue ⊢
          rw [outputValue]
        · have lengths := WordSemStateFiniteExact.getVarsLengthLemma names source values sourceValues
          have kLarge : 4 < k := related.2.2.2.2.2.2.2.2.2.1
          have extraEq : values.length - (k - 1) = count := by
            dsimp [count, Compiler.Backend.WordToStack.numStackRet]
            omega
          simp only [compCorrectResult, Option.map_some, compileResult,
            ne_eq, not_true_eq_false, ↓reduceIte]
          constructor
          · rw [extraEq]
            have relation := stateRelReturnFlush loadRelated countBound
            simpa only [post, freeSpace] using relation
          · have placements := returnPlacements loadRelated canonical sourceValues countBound
            simpa only [post, freeSpace] using placements

end Flapjack.WordToStackProofs.CompCorrect.Return



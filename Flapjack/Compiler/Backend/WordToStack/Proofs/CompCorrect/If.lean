import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Seq
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadRegisterTwo
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadRegisterClock
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadContinuations
import Flapjack.Compiler.Backend.WordToStack.Proofs.ConstantInstruction

namespace Flapjack.WordToStackProofs.CompCorrect.If
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStackRegFormat

/-- Flapjack-only operand parity predicate, with no separate HOL original. -/
def OperandEven {width : Nat} (operand : WordRegImm (BitVec width)) : Prop :=
  match operand with | .reg other => other % 2 = 0 | .imm _ => True

/-- Flapjack-only factoring of the literal evaluate_ind If source guards.
Both recursive conclusions retain the entire original comp_correct motive.
This is infrastructure for the full constructor theorem below, not a HOL port or
an assumption of a target run, result relation, or unconditional branch IH. -/
def OriginalInductionHypotheses {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (comparison : Cmp) (register : Nat)
    (operand : WordRegImm (BitVec width))
    (first second : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) : Prop :=
  (∀ v3 v4 x y value,
    (WordSemStateFiniteExact.getVar register source,
      WordSemStateFiniteExact.getVarImm operand source) = (v3, v4) ∧
    v3 = some x ∧ v4 = some y ∧ wordSemWordCmp comparison x y = some value ∧
    value = true → Seq.Simulation ac first source) ∧
  (∀ v3 v4 x y value,
    (WordSemStateFiniteExact.getVar register source,
      WordSemStateFiniteExact.getVarImm operand source) = (v3, v4) ∧
    v3 = some x ∧ v4 = some y ∧ wordSemWordCmp comparison x y = some value ∧
    ¬ value = true → Seq.Simulation ac second source)

/-- Flapjack infrastructure deriving the selected recursive simulation from
actual source execution and its original non-error premise. No branch success
or operand value is assumed independently, and both literal IH guards remain. -/
theorem selectedSourceBranch {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (comparison : Cmp) (register : Nat)
    (operand : WordRegImm (BitVec width))
    (first second : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (ih : OriginalInductionHypotheses ac comparison register operand first second source)
    (execution : WordSemStateFiniteExact.evaluate (.ite comparison register operand first second)
      source = (result, sourcePost))
    (nonerror : result ≠ some .error) :
    ∃ x y value,
      WordSemStateFiniteExact.getVar register source = some x ∧
      WordSemStateFiniteExact.getVarImm operand source = some y ∧
      wordSemWordCmp comparison x y = some value ∧
      WordSemStateFiniteExact.evaluate (if value then first else second) source =
        (result, sourcePost) ∧
      Seq.Simulation ac (if value then first else second) source := by
  cases left : WordSemStateFiniteExact.getVar register source with
  | none => simp [WordSemStateFiniteExact.evaluate, left] at execution; cases nonerror execution.1.symm
  | some x =>
    cases right : WordSemStateFiniteExact.getVarImm operand source with
    | none => simp [WordSemStateFiniteExact.evaluate, left, right] at execution; cases nonerror execution.1.symm
    | some y =>
      cases compared : wordSemWordCmp comparison x y with
      | none => simp [WordSemStateFiniteExact.evaluate, left, right, compared] at execution; cases nonerror execution.1.symm
      | some value =>
        refine ⟨x, y, value, rfl, rfl, compared, ?_, ?_⟩
        · cases value <;> simpa [WordSemStateFiniteExact.evaluate, left, right, compared] using execution
        · cases value
          · exact ih.2 _ _ x y false ⟨by simp [left, right], rfl, rfl, compared, by decide⟩
          · exact ih.1 _ _ x y true ⟨by simp [left, right], rfl, rfl, compared, rfl⟩

/-- Flapjack infrastructure: the actual condition-lowering branch of compNative,
factored without changing its load order or invalid-immediate materialization. -/
def conditionProgram {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (comparison : Cmp) (register : Nat)
    (operand : WordRegImm (BitVec width)) (frame : Nat × Nat × Nat)
    (first second : HolProg width) : HolProg width :=
  let (loads, physical) := wReg1 register frame
  match operand with
  | .reg other =>
      let (otherLoads, otherPhysical) := wReg2 other frame
      wStackLoadNative (loads ++ otherLoads) (.ite comparison physical (.reg otherPhysical) first second)
  | .imm word =>
      if ac.validImm (.inr comparison) word then
        wStackLoadNative loads (.ite comparison physical (.imm word) first second)
      else
        .seq (.inst (.const (frame.1 + 1) word))
          (wStackLoadNative loads (.ite comparison physical (.reg (frame.1 + 1)) first second))

/-- Flapjack infrastructure proving actual load-and-test routing for arbitrary
clock, from a proved prefix run and the actual native register comparison.
Used only internally; full constructor derives each input from original premises. -/
theorem loadConditionRun {width : Nat} [NeZero width] {C F : Type}
    (loads : List (Nat × Nat)) (target post : StackSemStateFiniteExact width C F)
    (comparison : Cmp) (register : Nat) (operand : HolRegImm width)
    (first second : HolProg width) (x y : WordLocW width) (value : Bool)
    (run : StackSemEvaluate.evaluate (wStackLoadNative loads .skip, target) = (none, post))
    (left : StackSemStateOps.getVar register post = some x)
    (right : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) post = some y)
    (compared : wordSemWordCmp comparison x y = some value) (clock : Nat) :
    StackSemEvaluate.evaluate
      (wStackLoadNative loads (.ite comparison register operand first second),
        {target with clock := clock}) =
    StackSemEvaluate.evaluate (if value then first else second, {post with clock := clock}) := by
  rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq,
    StackSemEvaluateClock.fixClockEvaluate, LoadRegisterClock.evaluateWStackLoadClock, run]
  simp only [Prod.map, id_eq]
  rw [StackSemEvaluate.evaluate_ite]
  have leftClock : StackSemStateOps.getVar register {post with clock := clock} = some x := left
  have rightClock : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
      {post with clock := clock} = some y := by
    cases operand <;> simpa [HolRegImm.toWordRegImm, StackSemStateOps.getVarImm,
      StackSemStateOps.getVar] using right
  rw [leftClock, rightClock]
  simp only [compared]
  cases value <;> rfl

/-- Flapjack infrastructure preparing the actual comparison path. All reads
and scratch-register preservation are consequences of the original relation
and source operands. Arbitrary-clock routing is proved for both continuations. -/
theorem prepareCondition {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (comparison : Cmp) (register : Nat)
    (operand : WordRegImm (BitVec width)) (k f frame : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (x y : WordLocW width) (value : Bool)
    (related : stateRel ac k f frame source target lens 0)
    (leftEven : register % 2 = 0)
    (rightEven : OperandEven operand)
    (left : WordSemStateFiniteExact.getVar register source = some x)
    (right : WordSemStateFiniteExact.getVarImm operand source = some y)
    (compared : wordSemWordCmp comparison x y = some value) :
    ∃ post : StackSemStateFiniteExact width C F,
      stateRel ac k f frame source post lens 0 ∧ target.clock = post.clock ∧
      target.bitmaps.IsPrefix post.bitmaps ∧ sptSubspt target.code post.code ∧
      ∀ (first second : HolProg width) (clock : Nat),
        StackSemEvaluate.evaluate
          (conditionProgram ac comparison register operand (k,f,frame) first second,
            {target with clock := clock}) =
        StackSemEvaluate.evaluate (if value then first else second, {post with clock := clock}) := by
  rcases regCompile : wReg1 register (k,f,frame) with ⟨loads, physical⟩
  cases operand with
  | reg other =>
    obtain ⟨middle, loadRun, firstClock, firstRel, _, _, _, _, physicalNe, firstRead⟩ :=
      LoadRegister.evaluateWStackLoadWReg1 ac k f frame register physical loads
        source target lens x regCompile leftEven left related
    rcases otherCompile : wReg2 other (k,f,frame) with ⟨otherLoads, otherPhysical⟩
    obtain ⟨post, otherRun, secondClock, _, secondRel, _, _, preserve, _, secondRead⟩ :=
      LoadRegisterTwo.evaluateWStackLoadWReg2 ac k f frame other otherPhysical otherLoads
        source middle lens y otherCompile rightEven right firstRel
    have bothRun : StackSemEvaluate.evaluate (wStackLoadNative (loads ++ otherLoads) .skip,target) =
        (none,post) := by
      rw [wStackLoadAppend, Function.comp_apply, LoadRegister.evaluateWStackLoadSeq,
        StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, loadRun]
      exact otherRun
    have mono := Flapjack.Compiler.Backend.StackProps.EvaluateMono.evaluateMono
      (wStackLoadNative (loads ++ otherLoads) .skip) target post none bothRun
    refine ⟨post, secondRel, firstClock.trans secondClock, mono.1, mono.2, ?_⟩
    intro first second clock
    simp only [conditionProgram, regCompile, otherCompile]
    exact loadConditionRun (loads ++ otherLoads) target post comparison physical (.reg otherPhysical) first second x y value bothRun
      ((preserve physical physicalNe).trans firstRead) secondRead compared clock
  | imm word =>
    simp only [WordSemStateFiniteExact.getVarImm, Option.some.injEq] at right
    subst y
    by_cases immediate : ac.validImm (.inr comparison) word = true
    · obtain ⟨post, loadRun, sameClock, postRel, _, _, _, _, _, firstRead⟩ :=
        LoadRegister.evaluateWStackLoadWReg1 ac k f frame register physical loads
          source target lens x regCompile leftEven left related
      have mono := Flapjack.Compiler.Backend.StackProps.EvaluateMono.evaluateMono
        (wStackLoadNative loads .skip) target post none loadRun
      refine ⟨post, postRel, sameClock, mono.1, mono.2, ?_⟩
      intro first second clock
      simp only [conditionProgram, regCompile, immediate, if_true]
      exact loadConditionRun loads target post comparison physical (.imm word) first second x (.word word) value loadRun firstRead rfl compared clock
    · obtain ⟨constantPost, constantRun, constantClock, constantRel, _, _, constantRead⟩ :=
        ConstantInstruction.evaluateConstInst ac k f frame 0 source target lens word related
      obtain ⟨post, loadRun, sameClock, postRel, _, _, _, preserve, _, firstRead⟩ :=
        LoadRegister.evaluateWStackLoadWReg1 ac k f frame register physical loads
          source constantPost lens x regCompile leftEven left constantRel
      have secondRead : StackSemStateOps.getVar (k+1) post = some (.word word) :=
        (preserve (k+1) (by omega)).trans constantRead
      have prefixRun : StackSemEvaluate.evaluate
          (.seq (.inst (.const (k+1) word)) (wStackLoadNative loads .skip),target) = (none,post) := by
        rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, constantRun]
        exact loadRun
      have mono := Flapjack.Compiler.Backend.StackProps.EvaluateMono.evaluateMono
        (.seq (.inst (.const (k+1) word)) (wStackLoadNative loads .skip)) target post none prefixRun
      refine ⟨post, postRel, constantClock.trans sameClock, mono.1, mono.2, ?_⟩
      intro first second clock
      simp only [conditionProgram, regCompile, immediate, Bool.false_eq_true, if_false]
      rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
        ConstantInstruction.evaluateConstInstClock, constantRun]
      simp only [Prod.map, id_eq]
      exact loadConditionRun loads constantPost post comparison physical (.reg (k+1)) first second x (.word word) value loadRun firstRead secondRead compared clock

/-- Flapjack factoring equation for the actual recursive compiler clause. -/
theorem compileCondition {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (comparison : Cmp) (register : Nat)
    (operand : WordRegImm (BitVec width)) (frame : Nat × Nat × Nat)
    (first second : WordLangProgHOL (BitVec width))
    (before middle after : AppList (BitVec width) × Nat) (q1 q2 : HolProg width)
    (firstCompile : compNative ac false first before frame = (q1,middle))
    (secondCompile : compNative ac false second middle frame = (q2,after)) :
    compNative ac false (.ite comparison register operand first second) before frame =
      (conditionProgram ac comparison register operand frame q1 q2, after) := by
  rcases h : wReg1 register frame with ⟨loads, physical⟩
  cases operand with
  | reg other =>
    rcases h2 : wReg2 other frame with ⟨otherLoads, otherPhysical⟩
    simp only [compNative, conditionProgram, h, h2, firstCompile, secondCompile]
  | imm word =>
    simp only [compNative, conditionProgram, h, firstCompile, secondCompile]
    split <;> rfl

/-- Flapjack infrastructure: actual condition-prefix instructions introduce no
code labels; both complete continuation label sets remain visible. -/
theorem conditionLabels {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (comparison : Cmp) (register : Nat)
    (operand : WordRegImm (BitVec width)) (frame : Nat × Nat × Nat)
    (first second : HolProg width) (label : Nat × Nat) :
    StackSem.getLabelsExact
      (conditionProgram ac comparison register operand frame first second) label ↔
      StackSem.getLabelsExact first label ∨ StackSem.getLabelsExact second label := by
  rcases h : wReg1 register frame with ⟨loads, physical⟩
  cases operand with
  | reg other =>
    rcases h2 : wReg2 other frame with ⟨otherLoads, otherPhysical⟩
    simp [conditionProgram,h,h2,getLabelsWStackLoad,StackSem.getLabelsExact]
  | imm word =>
    simp only [conditionProgram,h]
    split <;> simp [getLabelsWStackLoad,StackSem.getLabelsExact]

/-- Flapjack infrastructure extracting the original physical-operand parity. -/
private theorem physicalOperandEven {width : Nat} [NeZero width]
    (operand : WordRegImm (BitVec width))
    (physical : everyVarImmHOL isPhyVar operand = true) :
    OperandEven operand := by
  cases operand with
  | reg other => simpa [everyVarImmHOL,isPhyVar,OperandEven] using physical
  | imm word => trivial

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

/-- Complete original If constructor (6767–6903), retaining the whole original
comp_correct motive and the two literal evaluate_ind source guards. Source
non-error execution derives actual operands/comparison/selected branch. All
register, accepted-immediate and materialized-immediate routes are executed;
clock/prefix/code/frame obligations are derived, not additional premises.
Canonical finite maps and positive word carriers are explicitly qualified.
Inherits evaluator reals_as_rational_cuts assurance, without numerical FP
correspondence. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectIf {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (comparison : Cmp) (register : Nat)
    (operand : WordRegImm (BitVec width))
    (first second : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : OriginalInductionHypotheses ac comparison register operand first second source) :
    Seq.Simulation ac (.ite comparison register operand first second) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution, notError, related, conventions, flat,
    compilation, lengthBound, bitmapBound, bitmapPrefix, labels, maxBound⟩
  obtain ⟨x,y,value,left,right,compared,selectedRun,selectedIH⟩ :=
    selectedSourceBranch ac comparison register operand first second source sourcePost result ih execution notError
  have conventionParts := conventions
  simp only [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
    callArgConventionHOL,Bool.and_eq_true] at conventionParts
  rcases conventionParts with ⟨⟨⟨⟨leftPhy,rightPhy⟩,firstVar⟩,secondVar⟩,
    ⟨⟨firstStack,secondStack⟩,⟨firstCall,secondCall⟩⟩⟩
  have leftEven : register % 2 = 0 := by simpa [isPhyVar] using leftPhy
  have rightEven := physicalOperandEven operand rightPhy
  obtain ⟨loaded,loadedRel,sameClock,bitmapMono,codeMono,routing⟩ :=
    prepareCondition ac comparison register operand k f frame source target lens x y value
      related leftEven rightEven left right compared
  rcases firstCompile : compNative ac false first (bs,n) (k,f,frame) with ⟨q1,middle⟩
  rcases secondCompile : compNative ac false second middle (k,f,frame) with ⟨q2,after⟩
  have compiledFactor := compileCondition ac comparison register operand (k,f,frame)
    first second (bs,n) middle after q1 q2 firstCompile secondCompile
  obtain ⟨compiledEq,bitmapEq⟩ := Prod.mk.inj (compiledFactor.symm.trans compilation)
  subst compiled
  have firstAccounting := compImpLength ac false first (bs,n) (k,f,frame) q1 middle
    ⟨firstCompile,lengthBound⟩
  have selectedConventions : postAllocConventionsHOL k (if value then first else second) = true := by
    cases value <;> simp [postAllocConventionsHOL,firstVar,secondVar,firstStack,secondStack,firstCall,secondCall]
  have selectedFlat : flatExpConventions (if value then first else second) = true := by
    simp only [flatExpConventions,Bool.and_eq_true] at flat
    cases value <;> simp [flat.1,flat.2]
  have selectedMax : maxVarHOL (if value then first else second) < 2*frame+2*k := by
    unfold maxVarHOL at maxBound
    have max3Eq (a b c : Nat) : max3HOL a b c = max a (max b c) := by
      unfold max3HOL
      split_ifs <;> omega
    rw [max3Eq] at maxBound
    cases value <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
  have selectedCompile :
      compNative ac false (if value then first else second)
        (if value then (bs,n) else middle) (k,f,frame) =
      (if value then q1 else q2, if value then middle else after) := by
    cases value <;> simp [firstCompile,secondCompile]
  have selectedLength : (appListAppend (if value then (bs,n) else middle).1).length ≤
      (if value then (bs,n) else middle).2 := by
    cases value <;> simp [lengthBound,firstAccounting.1]
  have selectedGap : (if value then (bs,n) else middle).2 -
      (appListAppend (if value then (bs,n) else middle).1).length = n-(appListAppend bs).length := by
    cases value <;> simp [firstAccounting.2]
  have selectedBitmapBound : (if value then (bs,n) else middle).2 -
      (appListAppend (if value then (bs,n) else middle).1).length ≤ loaded.bitmaps.length := by
    rw [selectedGap]
    exact bitmapBound.trans bitmapMono.length_le
  have selectedPrefix : (appListAppend (if value then middle else after).1).IsPrefix
      (loaded.bitmaps.drop ((if value then (bs,n) else middle).2 -
        (appListAppend (if value then (bs,n) else middle).1).length)) := by
    rw [selectedGap]
    have finalPrefix : (appListAppend after.1).IsPrefix
        (loaded.bitmaps.drop (n-(appListAppend bs).length)) := by
      rw [bitmapEq]
      exact bitmapPrefix.trans (bitmapMono.drop _)
    cases value
    · exact finalPrefix
    · exact (compImpIsPrefix ac false second middle (k,f,frame) q2 after secondCompile).trans finalPrefix
  have selectedLabels : ∀ loc, StackSem.getLabelsExact (if value then q1 else q2) loc →
      StackSem.locCheckExact loaded.code loc := by
    intro loc member
    apply LocationLabels.locCheckSubset target.code loaded.code codeMono loc
    apply labels loc
    apply (conditionLabels ac comparison register operand (k,f,frame) q1 q2 loc).2
    cases value
    · exact Or.inr member
    · exact Or.inl member
  obtain ⟨extraClock,post,targetResult,targetRun,conclusion⟩ :=
    selectedIH k f frame sourcePost loaded result
      (if value then (bs,n) else middle).1 (if value then middle else after).1
      (if value then (bs,n) else middle).2 (if value then middle else after).2
      (if value then q1 else q2) lens
      ⟨selectedRun,notError,loadedRel,selectedConventions,selectedFlat,selectedCompile,
        selectedLength,selectedBitmapBound,selectedPrefix,selectedLabels,selectedMax⟩
  refine ⟨extraClock,post,targetResult,?_,conclusion⟩
  rw [routing q1 q2 (target.clock+extraClock),sameClock]
  exact targetRun

end Flapjack.WordToStackProofs.CompCorrect.If

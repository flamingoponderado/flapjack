import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Control
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompLength
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompilePrefix
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateClock
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateClock

namespace Flapjack.WordToStackProofs.CompCorrect.Seq
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Flapjack-only factoring of the entire original comp_correct induction motive
(5719–5751), at a fixed source program and state. All original quantified
parameters, premises and the full result/resource conclusion are retained.
There is no separate HOL declaration for this factoring. -/
def Simulation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (program : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) : Prop :=
  ∀ (k f frame : Nat)
    (sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat),
    (WordSemStateFiniteExact.evaluate program source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k program = true ∧ flatExpConventions program = true ∧
      compNative ac false program (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL program < 2 * frame + 2 * k) →
    ∃ (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens

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

/-- Original Seq proof's first-source non-NONE branch (6430–6461).
The source case guard is the original proof's split; both original guarded
induction hypotheses are retained. The conclusion is the entire original
clock-existential simulation, including every resource and result branch.
Evaluator closure inherits reals_as_rational_cuts; no numerical FP
correspondence is asserted by this structural branch. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectSeqFirstNonNone {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (first second : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : (∀ result middle,
      (result, middle) = WordSemStateFiniteExact.evaluate first source ∧ result = none →
        Simulation ac second middle) ∧ Simulation ac first source)
    (firstNonNone : (WordSemStateFiniteExact.evaluate first source).1 ≠ none) :
    Simulation ac (.seq first second) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution, notError, related, conventions, flat,
    compilation, lengthBound, bitmapBound, bitmapPrefix, labels, maxBound⟩
  rcases firstCompile : compNative ac false first (bs, n) (k, f, frame) with
    ⟨firstCode, middleBitmaps⟩
  rcases secondCompile : compNative ac false second middleBitmaps (k, f, frame) with
    ⟨secondCode, finalBitmaps⟩
  simp only [compNative, firstCompile, secondCompile] at compilation
  obtain ⟨compiledEq, bitmapEq⟩ := Prod.mk.inj compilation
  subst compiled
  have firstPrefix := compImpIsPrefix ac false second middleBitmaps (k, f, frame)
    secondCode finalBitmaps secondCompile
  rw [bitmapEq] at firstPrefix
  have firstLabels : ∀ loc, StackSem.getLabelsExact firstCode loc →
      StackSem.locCheckExact target.code loc := by
    intro loc member
    apply labels loc
    rw [StackSem.getLabelsExact]
    exact Or.inl member
  have firstConventions : postAllocConventionsHOL k first = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL,
      callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    exact ⟨conventions.1.1, conventions.2.1.1, conventions.2.2.1⟩
  have firstFlat : flatExpConventions first = true := by
    simp only [flatExpConventions, Bool.and_eq_true] at flat
    exact flat.1
  have firstMax : maxVarHOL first < 2 * frame + 2 * k := by
    simp only [maxVarHOL] at maxBound
    omega
  rw [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate] at execution
  rcases firstRun : WordSemStateFiniteExact.evaluate first source with ⟨firstResult, middle⟩
  rw [firstRun] at firstNonNone execution
  cases firstResult with
  | none => exact False.elim (firstNonNone rfl)
  | some value =>
    obtain ⟨resultEq, sourceEq⟩ := Prod.mk.inj execution
    subst result
    subst sourcePost
    obtain ⟨clock, targetPost, targetResult, targetRun, conclusion⟩ :=
      ih.2 k f frame middle target (some value) bs middleBitmaps.1 n middleBitmaps.2
        firstCode lens ⟨firstRun, notError, related, firstConventions, firstFlat,
          firstCompile, lengthBound, bitmapBound, firstPrefix.trans bitmapPrefix,
          firstLabels, firstMax⟩
    have targetNonNone : targetResult ≠ none := by
      intro eq
      subst targetResult
      simp [compCorrectResult] at conclusion
    refine ⟨clock, targetPost, targetResult, ?_, conclusion⟩
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, targetRun]
    cases targetResult with
    | none => exact False.elim (targetNonNone rfl)
    | some output => rfl

end Flapjack.WordToStackProofs.CompCorrect.Seq

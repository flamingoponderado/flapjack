import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Results
import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRel
import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef

namespace Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Inhabitation for total HOL EL; no choice of its unspecified value. -/
local instance {width : Nat} [NeZero width] : Nonempty (WordLocW width) := ⟨.word 0⟩

/-- Flapjack-only factoring of the entire original comp_correct conclusion
(5719–5751). It has no standalone HOL declaration: every case below proves
this full result, including the unmatched resource-limit branch, both Return
placement clauses and the original exception-frame existential. No simulation
or target execution is assumed by this predicate. -/
noncomputable def compCorrectResult {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (sourceResult : Option (WordSemResult width))
    (targetResult : Option (StackSemResult width)) (lens : List Nat) : Prop := by
  classical
  exact if sourceResult.map compileResult ≠ targetResult then
    targetResult = some (.halt (.word 2)) ∧
    List.IsPrefix target.ffi.ioEvents sourcePost.ffi.ioEvents ∧
    sourcePost.stackMax.getD (sourcePost.stackLimit + 1) > sourcePost.stackLimit
  else
    match sourceResult with
    | none => stateRel ac k f frame sourcePost target lens 0
    | some (.result _ values) =>
        stateRel ac k 0 0 sourcePost target lens (values.length - (k - 1)) ∧
        (∀ i, i < values.length →
          if i + 1 < k then target.regs.lookup (i + 1) = some (Flapjack.holEl i values)
          else (target.stack.drop target.stackSpace)[values.length - (i + 1)]? =
            some (Flapjack.holEl i values))
    | some (.exception _ value) =>
        ∃ nonGc gc,
          stateRel ac k 0 0 (pushLocals nonGc gc sourcePost) target
            (lens.drop (lens.length - (source.handler + 1))) 0 ∧
          sourcePost.locals = sptUnion (sptFromAList gc) (sptFromAList nonGc) ∧
          target.regs.lookup 1 = some value
    | some (.break _) => stateRel ac k f frame sourcePost target lens 0
    | some (.continue _) => stateRel ac k f frame sourcePost target lens 0
    | some _ => sourcePost.ffi = target.ffi ∧ sourcePost.clock = target.clock

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

/-- Full original comp_correct Skip case. All original premises and the
entire conclusion are retained; native target execution is derived with zero
extra clock. Evaluator closure inherits reals_as_rational_cuts; this structural
case asserts no numerical FP correspondence. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectSkip {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate .skip source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k (.skip : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions (.skip : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false .skip (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL (.skip : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  have execution := premises.1
  simp only [WordSemStateFiniteExact.evaluate] at execution
  obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
  have compilation := premises.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative] at programEq
  subst compiled
  subst result
  subst sourcePost
  refine ⟨0, target, none, ?_, ?_⟩
  · simp only [Nat.add_zero, StackSemEvaluate.evaluate_skip]
  · simpa only [compCorrectResult, compileResult, Option.map_some, Option.map_none,
      ne_eq, not_true_eq_false, ↓reduceIte] using premises.2.2.1

/-- Full original comp_correct Break case. All original premises and the
entire conclusion are retained; native target execution is derived with zero
extra clock. Evaluator closure inherits reals_as_rational_cuts; this structural
case asserts no numerical FP correspondence. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectBreak {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (label : Nat) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate (.break label) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k ((.break label) : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions ((.break label) : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false (.break label) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL ((.break label) : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  have execution := premises.1
  simp only [WordSemStateFiniteExact.evaluate] at execution
  obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
  have compilation := premises.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative] at programEq
  subst compiled
  subst result
  subst sourcePost
  refine ⟨0, target, some (.break label), ?_, ?_⟩
  · simp only [Nat.add_zero, StackSemEvaluate.evaluate_break]
  · simpa only [compCorrectResult, compileResult, Option.map_some, Option.map_none,
      ne_eq, not_true_eq_false, ↓reduceIte] using premises.2.2.1

/-- Full original comp_correct Continue case. All original premises and the
entire conclusion are retained; native target execution is derived with zero
extra clock. Evaluator closure inherits reals_as_rational_cuts; this structural
case asserts no numerical FP correspondence. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectContinue {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (label : Nat) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate (.continue label) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k ((.continue label) : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions ((.continue label) : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false (.continue label) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL ((.continue label) : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  have execution := premises.1
  simp only [WordSemStateFiniteExact.evaluate] at execution
  obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
  have compilation := premises.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative] at programEq
  subst compiled
  subst result
  subst sourcePost
  refine ⟨0, target, some (.continue label), ?_, ?_⟩
  · simp only [Nat.add_zero, StackSemEvaluate.evaluate_continue]
  · simpa only [compCorrectResult, compileResult, Option.map_some, Option.map_none,
      ne_eq, not_true_eq_false, ↓reduceIte] using premises.2.2.1

end Flapjack.WordToStackProofs.CompCorrect

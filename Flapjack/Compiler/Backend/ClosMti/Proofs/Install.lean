import Flapjack.Compiler.Backend.ClosMti.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
import Flapjack.SemanticPrimitivesProps.ResultRelation

/-! Installation simulation for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem BackendProps SemanticPrimitivesHOL

/-- Non-type-error installation outcomes are simulated by the transformed
oracle. This helper supplies the successful and timeout cases of the full
installation simulation below. -/
theorem doInstall_nonType_related {C F : Type} (source target : State C F)
    (sourceValues targetValues : List ClosSem.Value)
    (result : Result (List ClosLang.Exp) ClosSem.Value)
    (final : State C F) (states : StateRel source target)
    (values : List.Forall₂ (ValueRel source.maxApp) sourceValues targetValues)
    (run : doInstall sourceValues source = (result, final))
    (notType : result ≠ .err (.abort .typeError)) :
    ∃ expressions targetFinal,
      doInstall targetValues target =
        (if source.clock = 0 then .err (.abort .timeoutError)
          else .val (introList source.maxApp expressions), targetFinal) ∧
      result = (if source.clock = 0 then .err (.abort .timeoutError) else .val expressions) ∧
      expressions ≠ [] ∧ CodeRel source.maxApp expressions (introList source.maxApp expressions) ∧
      final.maxApp = source.maxApp ∧ StateRel final targetFinal := by
  classical
  obtain ⟨byteValue, wordValue, bytes, words, config, expressions, auxiliary, nextConfig,
    valueEq, bytesRun, wordsRun, oracleRun, compileRun, _, _, nextEq, nonempty, finalEq, resultEq⟩ :=
    doInstall_nonType_parts sourceValues source final result run notType
  subst sourceValues
  cases values with
  | cons bytesRel rest =>
    cases rest with
    | cons wordsRel rest =>
      cases rest
      rename_i targetByte targetWord
      have targetBytes : valueToBytes targetByte = some bytes := by
        rw [← ClosProps.simpleValRel_valueToBytes (ValueRel source.maxApp) byteValue targetByte
          ⟨simpleValRel source.maxApp, bytesRel⟩, bytesRun]
      have targetWords : valueToWords targetWord = some words := by
        rw [← ClosProps.simpleValRel_valueToWords wordValue targetWord (ValueRel source.maxApp)
          ⟨simpleValRel source.maxApp, wordsRel⟩, wordsRun]
      have prior := states
      obtain ⟨safe, sourceCode, targetCode, maxEq, positive, clockEq, ffiEq,
        globals, refs, compilerEq, oracleEq⟩ := prior
      have safeNow := safe 0
      rw [oracleRun] at safeNow
      obtain ⟨rfl, safeExpressions⟩ := safeNow
      have targetOracle : target.compileOracle 0 = (config, introList source.maxApp expressions, []) := by
        rw [oracleEq]
        simp [pureCo, compileInc, oracleRun]
      rw [compilerEq] at compileRun
      have targetCompile : target.compile config (introList source.maxApp expressions, []) =
          some (bytes, words, nextConfig) := by
        simpa [pureCc, compileInc] using compileRun
      have targetNextEq : (holShiftSeq 1 target.compileOracle 0).1 = nextConfig := by
        rw [oracleEq]
        simpa [holShiftSeq, pureCo] using nextEq
      have targetNonempty : introList source.maxApp expressions ≠ [] := by
        intro empty
        have length := introList_length source.maxApp expressions
        rw [empty] at length
        simp at length
        exact nonempty (List.eq_nil_of_length_eq_zero length.symm)
      have sourceEmpty : source.code.updateListEq [] = source.code := by cases source.code; rfl
      have targetEmpty : target.code.updateListEq [] = target.code := by cases target.code; rfl
      let targetFinal : State C F :=
        { target with compileOracle := holShiftSeq 1 target.compileOracle, clock := target.clock - 1 }
      refine ⟨expressions, targetFinal, ?_, resultEq, nonempty, ⟨safeExpressions, rfl⟩, ?_, ?_⟩
      · simp [doInstall, targetBytes, targetWords, targetOracle, targetCompile,
            targetNextEq, targetNonempty, targetFinal, clockEq, targetEmpty]
        split <;> rfl
      · simp [finalEq]
      · rw [finalEq]
        have rel := stateRel_shiftClock states (source.clock - 1) 1
        simpa [targetFinal, clockEq, sourceEmpty] using rel

/-- If the source installation fails with a type error, the transformed
installation also fails with a type error and leaves its state unchanged.
This is a Lean-side case of the installation simulation. -/
theorem doInstall_typeError_related {C F : Type} (source target : State C F)
    (sourceValues targetValues : List ClosSem.Value) (states : StateRel source target)
    (values : List.Forall₂ (ValueRel source.maxApp) sourceValues targetValues)
    (sourceError : (doInstall sourceValues source).1 = .err (.abort .typeError)) :
    doInstall targetValues target = (.err (.abort .typeError), target) := by
  classical
  by_contra failure
  have targetNotType : (doInstall targetValues target).1 ≠ .err (.abort .typeError) := by
    intro isType
    unfold doInstall at isType failure
    repeat' first | split at isType | split at failure | simp_all
  obtain ⟨byteValue, wordValue, bytes, words, config, expressions, auxiliary, nextConfig,
    valueEq, bytesRun, wordsRun, oracleRun, compileRun, _, _, nextEq, nonempty, _, _⟩ :=
    doInstall_nonType_parts targetValues target (doInstall targetValues target).2
      (doInstall targetValues target).1 (Prod.eta _) targetNotType
  subst targetValues
  cases values with
  | cons bytesRel rest =>
    cases rest with
    | cons wordsRel rest =>
      cases rest
      rename_i sourceByte sourceWord
      have sourceBytes : valueToBytes sourceByte = some bytes := by
        rw [ClosProps.simpleValRel_valueToBytes (ValueRel source.maxApp) sourceByte byteValue
          ⟨simpleValRel source.maxApp, bytesRel⟩, bytesRun]
      have sourceWords : valueToWords sourceWord = some words := by
        rw [ClosProps.simpleValRel_valueToWords sourceWord wordValue (ValueRel source.maxApp)
          ⟨simpleValRel source.maxApp, wordsRel⟩, wordsRun]
      obtain ⟨safe, _, _, _, _, _, _, _, _, compilerEq, oracleEq⟩ := states
      cases sourceOracle : source.compileOracle 0 with
      | mk sourceConfig program =>
        cases program with
        | mk sourceExpressions sourceAuxiliary =>
          have empty : sourceAuxiliary = [] := by
            simpa [sourceOracle] using (safe 0).1
          subst sourceAuxiliary
          have targetOracle : target.compileOracle 0 =
              (sourceConfig, introList source.maxApp sourceExpressions, []) := by
            rw [oracleEq]
            simp [pureCo, compileInc, sourceOracle]
          rw [targetOracle] at oracleRun
          simp only [Prod.mk.injEq] at oracleRun
          obtain ⟨rfl, rfl, rfl⟩ := oracleRun
          have sourceCompile : source.compile sourceConfig (sourceExpressions, []) =
              some (bytes, words, nextConfig) := by
            rw [compilerEq]
            simpa [pureCc, compileInc] using compileRun
          have sourceNextEq : (holShiftSeq 1 source.compileOracle 0).1 = nextConfig := by
            rw [oracleEq] at nextEq
            simpa [holShiftSeq, pureCo] using nextEq
          have sourceNonempty : sourceExpressions ≠ [] := by
            intro empty
            apply nonempty
            subst sourceExpressions
            have length := introList_length source.maxApp []
            exact List.eq_nil_of_length_eq_zero (by simpa using length)
          simp [doInstall, sourceBytes, sourceWords, sourceOracle, sourceCompile,
            sourceNextEq, sourceNonempty] at sourceError
          split at sourceError <;> simp_all

/-- Installation is simulated in both the error and success cases for the
proof-side closure semantics. Errors are identical here because installation
can only abort; successful programs are related by multi-argument introduction.
The source-shaped theorem below states the original error relation. -/
theorem doInstall_related {C F : Type} (source target : State C F)
    (sourceValues targetValues : List ClosSem.Value)
    (result : Result (List ClosLang.Exp) ClosSem.Value) (final : State C F)
    (states : StateRel source target)
    (values : List.Forall₂ (ValueRel source.maxApp) sourceValues targetValues)
    (run : doInstall sourceValues source = (result, final)) :
    match (generalizing := false) result with
    | .err error => ∃ targetFinal,
        doInstall targetValues target = (.err error, targetFinal) ∧
        final.maxApp = source.maxApp ∧ StateRel final targetFinal
    | .val expressions => ∃ targetExpressions targetFinal,
        final.maxApp = source.maxApp ∧ StateRel final targetFinal ∧ expressions ≠ [] ∧
        CodeRel source.maxApp expressions targetExpressions ∧
        doInstall targetValues target = (.val targetExpressions, targetFinal) := by
  classical
  by_cases typeError : result = .err (.abort .typeError)
  · have sourceFinal : final = source := by
      rw [typeError] at run
      unfold doInstall at run
      repeat' first | split at run | simp_all
    have targetRun := doInstall_typeError_related source target sourceValues targetValues states values
      (by rw [run, typeError])
    subst final
    clear run
    subst result
    exact ⟨target, targetRun, rfl, states⟩
  · obtain ⟨expressions, targetFinal, targetRun, resultEq, nonempty, code, maxEq, related⟩ :=
      doInstall_nonType_related source target sourceValues targetValues result final
        states values run typeError
    by_cases zero : source.clock = 0
    · simp only [zero, if_pos] at resultEq targetRun
      clear run typeError
      subst result
      exact ⟨targetFinal, targetRun, maxEq, related⟩
    · simp only [zero, if_false] at resultEq targetRun
      clear run typeError
      subst result
      exact ⟨introList source.maxApp expressions, targetFinal,
        maxEq, related, nonempty, code, targetRun⟩

/-- Installation errors are aborts; the installation operation cannot raise
an exception value. -/
theorem doInstall_error_abort {C F : Type} (values : List ClosSem.Value)
    (state final : State C F) (error : ErrorResult ClosSem.Value)
    (run : doInstall values state = (.err error, final)) :
    ∃ reason, error = .abort reason := by
  classical
  unfold doInstall at run
  repeat' first | split at run | simp_all
  all_goals exact ⟨_, run.1.symm⟩

namespace InstallLemma
/-- The closure state uses the canonical finite-support maps. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end InstallLemma

/-- Installation preserves related closure states and relates both error and
success outcomes. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "do_install_lemma"
  (fmap_as_finite_support := [refs, code])]
theorem doInstallLemma {C F : Type} (source target : State C F)
    (sourceValues targetValues : List ClosSem.Value)
    (related : StateRel source target ∧
      List.Forall₂ (ValueRel source.maxApp) sourceValues targetValues) :
    match (generalizing := false) doInstall sourceValues source with
    | (.err error, final) => ∃ targetError targetFinal,
        doInstall targetValues target = (.err targetError, targetFinal) ∧
        SemanticPrimitivesProps.excRel (ValueRel source.maxApp) error targetError ∧
        final.maxApp = source.maxApp ∧ StateRel final targetFinal
    | (.val expressions, final) => ∃ targetExpressions targetFinal,
        (final.maxApp = source.maxApp ∧ StateRel final targetFinal) ∧
        expressions ≠ [] ∧ CodeRel source.maxApp expressions targetExpressions ∧
        doInstall targetValues target = (.val targetExpressions, targetFinal) := by
  cases run : doInstall sourceValues source with
  | mk result final =>
    have simulation := doInstall_related source target sourceValues targetValues
      result final related.1 related.2 run
    cases result with
    | err error =>
      obtain ⟨reason, rfl⟩ := doInstall_error_abort sourceValues source final error run
      obtain ⟨targetFinal, targetRun, maxEq, states⟩ := simulation
      exact ⟨.abort reason, targetFinal, targetRun, rfl, maxEq, states⟩
    | val expressions => simpa only [and_assoc] using simulation

/-- Invert the installation simulation from a target outcome. This is a
Lean-side consequence of the source-shaped installation lemma, used by the
backward evaluator simulation. -/
theorem doInstall_reverse_related {C F : Type} (source target : State C F)
    (sourceValues targetValues : List ClosSem.Value)
    (targetResult : Result (List ClosLang.Exp) ClosSem.Value) (targetFinal : State C F)
    (states : StateRel source target)
    (values : List.Forall₂ (ValueRel source.maxApp) sourceValues targetValues)
    (run : doInstall targetValues target = (targetResult, targetFinal)) :
    match (generalizing := false) targetResult with
    | .err targetError => ∃ sourceError sourceFinal,
        doInstall sourceValues source = (.err sourceError, sourceFinal) ∧
        SemanticPrimitivesProps.excRel (ValueRel source.maxApp) sourceError targetError ∧
        sourceFinal.maxApp = source.maxApp ∧ StateRel sourceFinal targetFinal
    | .val targetExpressions => ∃ sourceExpressions sourceFinal,
        (sourceFinal.maxApp = source.maxApp ∧ StateRel sourceFinal targetFinal) ∧
        sourceExpressions ≠ [] ∧ CodeRel source.maxApp sourceExpressions targetExpressions ∧
        doInstall sourceValues source = (.val sourceExpressions, sourceFinal) := by
  have forward := doInstallLemma source target sourceValues targetValues ⟨states, values⟩
  cases sourceRun : doInstall sourceValues source with
  | mk sourceResult sourceFinal =>
    cases sourceResult with
    | err sourceError =>
      simp only [sourceRun] at forward
      obtain ⟨targetError, middle, targetRun, errors, maxEq, related⟩ := forward
      rw [run] at targetRun
      simp only [Prod.mk.injEq] at targetRun
      obtain ⟨rfl, rfl⟩ := targetRun
      exact ⟨sourceError, sourceFinal, rfl, errors, maxEq, related⟩
    | val sourceExpressions =>
      simp only [sourceRun] at forward
      obtain ⟨targetExpressions, middle, ⟨maxEq, related⟩, nonempty, code, targetRun⟩ := forward
      rw [run] at targetRun
      simp only [Prod.mk.injEq] at targetRun
      obtain ⟨rfl, rfl⟩ := targetRun
      exact ⟨sourceExpressions, sourceFinal, ⟨maxEq, related⟩, nonempty, code, rfl⟩

end Flapjack.Compiler.Backend.ClosMti

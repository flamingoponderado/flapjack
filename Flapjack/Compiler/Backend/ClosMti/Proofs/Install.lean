import Flapjack.Compiler.Backend.ClosMti.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.Install

/-! Installation simulation for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem BackendProps SemanticPrimitivesHOL

/-- Non-type-error installation outcomes are simulated by the transformed
oracle. This is a partial Lean-side result: the source theorem also covers
type errors and has not yet been assembled. -/
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

end Flapjack.Compiler.Backend.ClosMti

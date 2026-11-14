module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.StateRelation
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
public import Flapjack.Compiler.Backend.Semantics.ClosProps.DecodeRelations

@[expose] public section

/-! Decoder prerequisites for the closure-numbering installation case. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack.Compiler.Backend.ClosSem
open Flapjack Flapjack.Compiler.Backend.BackendProps

/-- Related values yield identical byte decoding results, including failure. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "v_to_bytes"]
theorem valueToBytes_related (maxApp : Nat) (source target : Value)
    (related : ValueRel maxApp source target) : valueToBytes source = valueToBytes target :=
  ClosProps.simpleValRel_valueToBytes (ValueRel maxApp) source target ⟨simpleValRel maxApp, related⟩

/-- Related values yield identical 64-bit word decoding results, including failure. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "v_to_words"]
theorem valueToWords_related (maxApp : Nat) (source target : Value)
    (related : ValueRel maxApp source target) : valueToWords source = valueToWords target :=
  ClosProps.simpleValRel_valueToWords source target (ValueRel maxApp) ⟨simpleValRel maxApp, related⟩

/-- Advancing both compile oracles preserves the numbering state relation.
Installation also updates the clock and code; those steps are separate from
this oracle invariant. -/
theorem stateRel_shiftOracle {C F : Type} {source : State (Nat × C) F} {target : State C F}
    (related : StateRel source target) (amount : Nat) :
    StateRel { source with compileOracle := holShiftSeq amount source.compileOracle }
      { target with compileOracle := holShiftSeq amount target.compileOracle } := by
  rcases related with ⟨clock, ffi, maxApp, compiler, oracle, refs, globals, safe, sourceCode, targetCode⟩
  refine ⟨clock, ffi, maxApp, compiler, ?_, refs, globals, ?_, sourceCode, targetCode⟩
  · simp only
    rw [oracle]
    rfl
  · intro index
    exact safe (index + amount)

/-- Every incremental numbering result begins with its original location. -/
theorem compileInc_nonempty (number : Nat) (expressions : List ClosLang.Exp) :
    (compileInc number expressions).2 ≠ [] := by
  simp only [compileInc, makeEven]
  split <;> simp

/-- Successful or timed-out installation is simulated by the numbered
oracle entry. This uses the proof-side state and value relations; their HOL
carrier correspondence and the enclosing evaluator theorem remain open. -/
theorem doInstall_related {C F : Type} (source : State (Nat × C) F) (target : State C F)
    (sourceValues targetValues : List Value) (result : Flapjack.SemanticPrimitivesHOL.Result (List ClosLang.Exp) Value)
    (final : State (Nat × C) F) (states : StateRel source target)
    (values : List.Forall₂ (ValueRel source.maxApp) sourceValues targetValues)
    (run : doInstall sourceValues source = (result, final))
    (notType : result ≠ .err (.abort .typeError)) :
    ∃ expressions targetFinal,
      doInstall targetValues target =
        (if source.clock = 0 then .err (.abort .timeoutError)
          else .val (compileInc (source.compileOracle 0).1.1 expressions).2, targetFinal) ∧
      result = (if source.clock = 0 then .err (.abort .timeoutError) else .val expressions) ∧
      ¬ ClosProps.containsAppSome source.maxApp expressions ∧
      final.maxApp = source.maxApp ∧ StateRel final targetFinal := by
  classical
  obtain ⟨byteValue, wordValue, bytes, words, config, expressions, auxiliary, nextConfig,
    valueEq, bytesRun, wordsRun, oracleRun, compileRun, _, _, nextEq, _, finalEq, resultEq⟩ :=
    doInstall_nonType_parts sourceValues source final result run notType
  subst sourceValues
  cases values with
  | cons bytesRel rest =>
    cases rest with
    | cons wordsRel rest =>
      cases rest
      rename_i targetByte targetWord
      have targetBytes : valueToBytes targetByte = some bytes := by
        rw [← valueToBytes_related source.maxApp byteValue targetByte bytesRel, bytesRun]
      have targetWords : valueToWords targetWord = some words := by
        rw [← valueToWords_related source.maxApp wordValue targetWord wordsRel, wordsRun]
      have safe := states.2.2.2.2.2.2.2.1 0
      rw [oracleRun] at safe
      obtain ⟨rfl, safeExpressions⟩ := safe
      cases config with
      | mk number config =>
        cases numbered : compileInc number expressions with
        | mk nextNumber numberedExpressions =>
          have targetOracle : target.compileOracle 0 = (config, numberedExpressions, []) := by
            rw [states.2.2.2.2.1]
            simp [stateCo, ignoreTable, oracleRun, numbered]
          rw [states.2.2.2.1] at compileRun
          cases targetCompile : target.compile config (numberedExpressions, []) with
          | none => simp [stateCc, ignoreTable, numbered, targetCompile] at compileRun
          | some output =>
            obtain ⟨targetBytesOut, targetWordsOut, targetNext⟩ := output
            simp [stateCc, ignoreTable, numbered, targetCompile] at compileRun
            obtain ⟨rfl, rfl, rfl⟩ := compileRun
            have targetNextEq : (holShiftSeq 1 target.compileOracle 0).1 = targetNext := by
              have oracleEq := states.2.2.2.2.1
              rw [oracleEq]
              simpa [holShiftSeq, stateCo] using congrArg Prod.snd nextEq
            have nonempty : numberedExpressions ≠ [] := by
              have h := compileInc_nonempty number expressions
              simpa [numbered] using h
            have sourceEmpty : source.code.updateListEq [] = source.code := by
              cases source.code
              rfl
            have targetEmpty : target.code.updateListEq [] = target.code := by
              cases target.code
              rfl
            let targetFinal : State C F := { target with compileOracle := holShiftSeq 1 target.compileOracle, clock := target.clock - 1 }
            refine ⟨expressions, targetFinal, ?_, resultEq, safeExpressions, ?_, ?_⟩
            · have clockEq := states.1
              by_cases zero : target.clock = 0 <;>
                simp [doInstall, targetBytes, targetWords, targetOracle, targetCompile,
                  targetNextEq, nonempty, targetFinal, clockEq, oracleRun, numbered, targetEmpty, zero]
            · simp [finalEq]
            · rw [finalEq]
              have h := stateRel_withClock (source.clock - 1) (stateRel_shiftOracle states 1)
              simpa [targetFinal, states.1, sourceEmpty] using h

end Flapjack.Compiler.Backend.ClosNumber

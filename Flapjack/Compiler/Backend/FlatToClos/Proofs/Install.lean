import Flapjack.Compiler.Backend.FlatToClos.Proofs.StateRelation
import Flapjack.Compiler.Backend.FlatToClos.Proofs.InstallDecoding

/-! Dynamic installation prerequisites for flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendProps

/-- Invert a successful flat Eval request. The decoded inputs and compiler
output are retained for the corresponding closure installation. -/
theorem doEval_success_parts {C : Type} (values : List FlatSem.Value)
    (config next : FlatSem.InstallConfig C) (decs : List FlatLang.Exp) (value : FlatSem.Value)
    (run : FlatSem.doEval values config = some (decs, next, value)) :
    ∃ bytesValue wordsValue bytes words compilerState nextState,
      values = [bytesValue, wordsValue] ∧
      FlatSem.valueToBytes bytesValue = some bytes ∧
      FlatSem.valueToWords wordsValue = some words ∧
      config.compileOracle 0 = (compilerState, decs) ∧
      config.compile compilerState decs = some (bytes, words, nextState) ∧
      decs ≠ [] ∧ (Flapjack.holShiftSeq 1 config.compileOracle 0).1 = nextState ∧
      next = { config with compileOracle := Flapjack.holShiftSeq 1 config.compileOracle } ∧
      value = FlatSem.unitValue := by
  classical
  cases values with
  | nil => simp [FlatSem.doEval] at run
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.doEval] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [FlatSem.doEval] at run
      | nil =>
        cases byteResult : FlatSem.valueToBytes first with
        | none => simp [FlatSem.doEval, byteResult] at run
        | some bytes =>
          cases wordResult : FlatSem.valueToWords second with
          | none => simp [FlatSem.doEval, byteResult, wordResult] at run
          | some words =>
            cases oracleResult : config.compileOracle 0 with
            | mk compilerState program =>
              cases compilerResult : config.compile compilerState program with
              | none => simp [FlatSem.doEval, byteResult, wordResult, oracleResult, compilerResult] at run
              | some output =>
                obtain ⟨compiledBytes, compiledWords, nextState⟩ := output
                simp only [FlatSem.doEval, byteResult, wordResult, oracleResult, compilerResult] at run
                split at run
                · rename_i checks
                  simp only [Option.some.injEq, Prod.mk.injEq] at run
                  obtain ⟨rfl, rfl, rfl⟩ := run
                  obtain ⟨rfl, rfl, nonempty, nextEq⟩ := checks
                  exact ⟨first, second, bytes, words, compilerState, nextState,
                    rfl, byteResult, wordResult, rfl, compilerResult, nonempty, nextEq, rfl, rfl⟩
                · simp at run

/-- A successful flat Eval request installs its translated declarations in
the related closure state. This proof-side simulation remains untagged until
the value, state, and evaluator carriers have been reviewed against HOL. -/
theorem doEval_install {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (sourceValues : List FlatSem.Value) (targetValues : List ClosSem.Value)
    (decs : List FlatLang.Exp) (nextConfig : FlatSem.InstallConfig C) (value : FlatSem.Value)
    (run : FlatSem.doEval sourceValues source.evalConfig = some (decs, nextConfig, value))
    (states : StateRel source target) (values : List.Forall₂ ValueRel sourceValues targetValues) :
    ∃ advanced : ClosSem.State C F,
      StateRel { source with evalConfig := nextConfig } advanced ∧
      value = FlatSem.unitValue ∧ FlatProps.noMatDecs decs = true ∧
      ClosSem.doInstall targetValues target =
        (if target.clock = 0 then
          (.err (.abort .timeoutError), ClosSem.decClock 1 advanced)
        else
          (.val (compileDecs decs ++ compileDecs [.con .none none []]), ClosSem.decClock 1 advanced)) := by
  classical
  obtain ⟨bytesValue, wordsValue, bytes, words, compilerState, nextState, sourceEq,
    bytesDecoded, wordsDecoded, oracleResult, compilerResult, nonempty, nextEq, configEq, valueEq⟩ :=
    doEval_success_parts sourceValues source.evalConfig nextConfig decs value run
  subst sourceValues
  cases values with
  | cons bytesRelated rest =>
    cases rest with
    | cons wordsRelated rest =>
      cases rest
      rename_i targetBytes targetWords
      have targetBytesDecoded := installBytes_related bytesValue targetBytes bytesRelated bytes bytesDecoded
      have targetWordsDecoded := installWords_related wordsValue targetWords wordsRelated words wordsDecoded
      rcases states.2.2.2.2.2.2 with ⟨safe, oracleEq, compileEq⟩
      have oracleTarget : target.compileOracle 0 =
          (compilerState, incCompileDecsProofSide decs) := by
        rw [oracleEq]
        simp [Function.comp_apply, pureCo, oracleResult]
      have compilerTarget : target.compile compilerState (incCompileDecsProofSide decs) =
          some (bytes, words, nextState) := by
        rw [compileEq] at compilerResult
        exact compilerResult
      have nextTarget : (Flapjack.holShiftSeq 1 target.compileOracle 0).1 = nextState := by
        rw [oracleEq]
        simpa [Flapjack.holShiftSeq, Function.comp_apply, pureCo] using nextEq
      have safeDecs : FlatProps.noMatDecs decs = true := by
        simpa [oracleResult] using safe 0
      let advanced : ClosSem.State C F :=
        { target with compileOracle := Flapjack.holShiftSeq 1 target.compileOracle }
      refine ⟨advanced, ?_, valueEq, safeDecs, ?_⟩
      · rw [configEq]
        exact stateRel_shiftInstall states 1
      · have emptyUpdate : target.code.updateListEq [] = target.code := by
          cases target.code
          rfl
        simp only [incCompileDecsProofSide, compileDecs, compile, compileExps] at compilerTarget
        simp [ClosSem.doInstall, targetBytesDecoded, targetWordsDecoded, oracleTarget,
          incCompileDecsProofSide, compilerTarget, nextTarget, advanced, ClosSem.decClock,
          FlatToClos.compileDecs, FlatToClos.compile, FlatToClos.compileExps,
          emptyUpdate]

end Flapjack.Compiler.Backend.FlatToClos

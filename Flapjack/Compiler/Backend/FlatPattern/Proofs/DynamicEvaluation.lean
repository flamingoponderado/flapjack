import Flapjack.Compiler.Backend.FlatProps.SimpleConversions
import Flapjack.Compiler.Backend.FlatPattern.Proofs.FunctionApplication

/-! Dynamic compiler input preservation for the flat pattern pass. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Related installation configurations expose corresponding oracle entries. -/
theorem installConfRel_oracle {C : Type} (cfg : Config) (source target : FlatSem.InstallConfig C)
    (related : installConfRel cfg source target) (index : Nat) :
    target.compileOracle index = ((source.compileOracle index).1,
      (source.compileOracle index).2.map (compileDec cfg)) := by
  have h := congrFun related.1 index
  simpa [BackendProps.pureCo, Function.comp_def] using h

/-- Related installation configurations produce the same compiled artifact
when the target receives the translated declarations. -/
theorem installConfRel_compile {C : Type} (cfg : Config) (source target : FlatSem.InstallConfig C)
    (related : installConfRel cfg source target) (compilerState : C) (declarations : List FlatLang.Exp) :
    source.compile compilerState declarations = target.compile compilerState (declarations.map (compileDec cfg)) := by
  have h := congrFun (congrFun related.2 compilerState) declarations
  simpa [BackendProps.pureCc] using h

/-- Successful dynamic evaluation transfers through the original state and
value relations, producing the compiled declarations and related result. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "do_eval_thm"]
theorem doEval_thm {C F : Type} (sourceValues : List FlatSem.Value)
    (sourceState : FlatSem.State C F) (declarations : List FlatLang.Exp)
    (sourceNext : FlatSem.InstallConfig C) (result : FlatSem.Value) (cfg : Config)
    (targetState : FlatSem.State C F) (targetValues : List FlatSem.Value)
    (premises : FlatSem.doEval sourceValues sourceState.evalConfig = some (declarations, sourceNext, result) ∧
      StateRel cfg sourceState targetState ∧ List.Forall₂ ValueRel sourceValues targetValues) :
    ∃ targetResult targetDeclarations targetNext,
      FlatSem.doEval targetValues targetState.evalConfig = some (targetDeclarations, targetNext, targetResult) ∧
      StateRel cfg { sourceState with evalConfig := sourceNext } { targetState with evalConfig := targetNext } ∧
      ValueRel result targetResult ∧ targetDeclarations = declarations.map (compileDec cfg) := by
  obtain ⟨run, states, valuesRel⟩ := premises
  let source := sourceState.evalConfig
  let target := targetState.evalConfig
  have configs : installConfRel cfg source target := states.2.2.2.2
  change FlatSem.doEval sourceValues source = some (declarations, sourceNext, result) at run
  cases sourceValues with
  | nil => simp [FlatSem.doEval] at run
  | cons byteValue rest =>
    cases rest with
    | nil => simp [FlatSem.doEval] at run
    | cons wordValue rest =>
      cases rest with
      | cons _ _ => simp [FlatSem.doEval] at run
      | nil =>
        cases valuesRel with
        | cons bytesRel tailRel =>
          cases tailRel with
          | cons wordsRel endRel =>
            cases endRel
            rename_i targetByte targetWord
            cases bytesRun : FlatSem.valueToBytes byteValue with
            | none => simp [FlatSem.doEval, bytesRun] at run
            | some bytes =>
              cases wordsRun : FlatSem.valueToWords wordValue with
              | none => simp [FlatSem.doEval, bytesRun, wordsRun] at run
              | some words =>
                have targetBytes := FlatProps.simpleValueToBytes ValueRel simpleValueRel_valueRel byteValue targetByte bytes bytesRel bytesRun
                have targetWords := FlatProps.simpleValueToWords ValueRel simpleValueRel_valueRel wordValue targetWord words wordsRel wordsRun
                cases oracle : source.compileOracle 0 with
                | mk compilerState decs =>
                  cases compilation : source.compile compilerState decs with
                  | none => simp [FlatSem.doEval, bytesRun, wordsRun, oracle, compilation] at run
                  | some output =>
                    obtain ⟨compiledBytes, compiledWords, nextState⟩ := output
                    by_cases accepted : bytes = compiledBytes ∧ words = compiledWords ∧ decs ≠ [] ∧
                        (Flapjack.holShiftSeq 1 source.compileOracle 0).1 = nextState
                    · have sourceShape : (decs, { source with compileOracle := Flapjack.holShiftSeq 1 source.compileOracle }, FlatSem.unitValue) =
                          (declarations, sourceNext, result) := by
                        simpa [FlatSem.doEval, bytesRun, wordsRun, oracle, compilation, accepted] using run
                      cases sourceShape
                      have targetOracle : target.compileOracle 0 = (compilerState, declarations.map (compileDec cfg)) := by
                        simpa [oracle] using installConfRel_oracle cfg source target configs 0
                      have targetCompilation : target.compile compilerState (declarations.map (compileDec cfg)) =
                          some (compiledBytes, compiledWords, nextState) := by
                        rw [← installConfRel_compile cfg source target configs compilerState declarations]
                        exact compilation
                      have nextOracle : (Flapjack.holShiftSeq 1 target.compileOracle 0).1 = nextState := by
                        have h := installConfRel_oracle cfg source target configs 1
                        simpa [Flapjack.holShiftSeq, Function.comp_def] using congrArg Prod.fst h |>.trans accepted.2.2.2
                      have mappedNonempty : declarations.map (compileDec cfg) ≠ [] := by
                        intro empty
                        exact accepted.2.2.1 (List.map_eq_nil_iff.mp empty)
                      let targetNext := { target with compileOracle := Flapjack.holShiftSeq 1 target.compileOracle }
                      refine ⟨FlatSem.unitValue, declarations.map (compileDec cfg), targetNext, ?_, ?_, ?_, rfl⟩
                      · change FlatSem.doEval [targetByte, targetWord] target =
                          some (declarations.map (compileDec cfg), targetNext, FlatSem.unitValue)
                        simp [FlatSem.doEval, targetBytes, targetWords, targetOracle, targetCompilation,
                          accepted.1, accepted.2.1, mappedNonempty, nextOracle, targetNext]
                      · rcases states with ⟨clock, refs, ffi, globals, _⟩
                        exact ⟨clock, refs, ffi, globals, installConfRel_shift cfg source target 1 configs⟩
                      · apply (valueRel_conv none [] _).2
                        exact ⟨[], rfl, .nil⟩
                    · simp [FlatSem.doEval, bytesRun, wordsRun, oracle, compilation, accepted] at run

/-- Invalid dynamic-compiler inputs cause a type error. -/
theorem evaluate_eval_bad {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (values : List FlatSem.Value) (argsRun : FlatSem.evaluate env state args.reverse = (next, .val values))
    (decoded : FlatSem.doEval values.reverse next.evalConfig = none) :
    FlatSem.evaluate env state [.app trace (.src .eval) args] =
      ({ next with clock := min state.clock next.clock }, .err (.abort .typeError)) := by
  simp [FlatSem.evaluate, argsRun, FlatSem.fixClock, decoded]

/-- A successful installation at zero clock times out before declarations run. -/
theorem evaluate_eval_timeout {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (values : List FlatSem.Value) (declarations : List FlatLang.Exp) (config : FlatSem.InstallConfig C) (result : FlatSem.Value)
    (argsRun : FlatSem.evaluate env state args.reverse = (next, .val values))
    (decoded : FlatSem.doEval values.reverse next.evalConfig = some (declarations, config, result))
    (zero : min state.clock next.clock = 0) :
    FlatSem.evaluate env state [.app trace (.src .eval) args] =
      ({ next with clock := min state.clock next.clock, evalConfig := config }, .err (.abort .timeoutError)) := by
  simp [FlatSem.evaluate, argsRun, FlatSem.fixClock, decoded, zero]

/-- A successful installation with remaining clock evaluates its declarations
and returns either their error or the installation result. -/
theorem evaluate_eval_declarations {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next final : FlatSem.State C F) (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (values : List FlatSem.Value) (declarations : List FlatLang.Exp) (config : FlatSem.InstallConfig C) (result : FlatSem.Value)
    (outcome : Option (SemanticPrimitivesHOL.ErrorResult FlatSem.Value))
    (argsRun : FlatSem.evaluate env state args.reverse = (next, .val values))
    (decoded : FlatSem.doEval values.reverse next.evalConfig = some (declarations, config, result))
    (nonzero : min state.clock next.clock ≠ 0)
    (declsRun : FlatSem.evaluateDecs
      (FlatSem.decClock { next with clock := min state.clock next.clock, evalConfig := config }) declarations = (final, outcome)) :
    FlatSem.evaluate env state [.app trace (.src .eval) args] =
      (final, match outcome with | none => .val [result] | some error => .err error) := by
  cases outcome <;> simp [FlatSem.evaluate, argsRun, FlatSem.fixClock, decoded, nonzero, declsRun]

end Flapjack.Compiler.Backend.FlatPattern

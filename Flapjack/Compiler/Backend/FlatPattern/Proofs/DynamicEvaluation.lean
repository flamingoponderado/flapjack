import Flapjack.Compiler.Backend.FlatProps.SimpleConversions
import Flapjack.Compiler.Backend.FlatPattern.Proofs.FunctionApplication

/-! Dynamic compiler input preservation for the flat pattern pass. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- A related literal-only value list has identical literal elements. -/
theorem related_literal_list {left right : List FlatSem.Value}
    (related : List.Forall₂ ValueRel left right)
    (literals : ∀ value ∈ left, ∃ literal, value = .litv literal) : right = left := by
  induction related with
  | nil => rfl
  | @cons head head' tail tail' headRel tailRel ih =>
    obtain ⟨literal, rfl⟩ := literals head (by simp)
    have headEq := (valueRel_lit literal head').1 headRel
    have tailEq := ih (by intro value member; exact literals value (List.mem_cons_of_mem _ member))
    simp [headEq, tailEq]

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

/-- Dynamic evaluation returns translated declarations, the same unit value,
and related shifted configurations whenever the source succeeds. -/
theorem doEval_simulation {C : Type} (cfg : Config) (source target : FlatSem.InstallConfig C)
    (sourceValues targetValues : List FlatSem.Value)
    (valuesRel : List.Forall₂ ValueRel sourceValues targetValues) (configs : installConfRel cfg source target)
    (declarations : List FlatLang.Exp) (sourceNext : FlatSem.InstallConfig C) (result : FlatSem.Value)
    (run : FlatSem.doEval sourceValues source = some (declarations, sourceNext, result)) :
    ∃ targetNext, FlatSem.doEval targetValues target = some (declarations.map (compileDec cfg), targetNext, result) ∧
      installConfRel cfg sourceNext targetNext ∧ ValueRel result result := by
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
                      refine ⟨targetNext, ?_, installConfRel_shift cfg source target 1 configs, ?_⟩
                      · simp [FlatSem.doEval, targetBytes, targetWords, targetOracle, targetCompilation,
                          accepted.1, accepted.2.1, mappedNonempty, nextOracle, targetNext]
                      · apply (valueRel_conv none [] _).2
                        exact ⟨[], rfl, .nil⟩
                    · simp [FlatSem.doEval, bytesRun, wordsRun, oracle, compilation, accepted] at run

/-- Updating both related states with related installation configurations
preserves the state relation. -/
theorem stateRel_update_install {C F : Type} (cfg : Config) (source target : FlatSem.State C F)
    (sourceNext targetNext : FlatSem.InstallConfig C) (states : StateRel cfg source target)
    (configs : installConfRel cfg sourceNext targetNext) :
    StateRel cfg { source with evalConfig := sourceNext } { target with evalConfig := targetNext } := by
  rcases states with ⟨clock, refs, ffi, globals, _⟩
  exact ⟨clock, refs, ffi, globals, configs⟩

/-- Dynamic evaluation on related states yields translated declarations and
related post-installation states. -/
theorem doEval_state_simulation {C F : Type} (cfg : Config) (source target : FlatSem.State C F)
    (sourceValues targetValues : List FlatSem.Value) (states : StateRel cfg source target)
    (values : List.Forall₂ ValueRel sourceValues targetValues)
    (declarations : List FlatLang.Exp) (sourceConfig : FlatSem.InstallConfig C) (result : FlatSem.Value)
    (run : FlatSem.doEval sourceValues source.evalConfig = some (declarations, sourceConfig, result)) :
    ∃ targetConfig targetResult,
      FlatSem.doEval targetValues target.evalConfig = some (declarations.map (compileDec cfg), targetConfig, targetResult) ∧
      StateRel cfg { source with evalConfig := sourceConfig } { target with evalConfig := targetConfig } ∧
      ValueRel result targetResult := by
  obtain ⟨targetConfig, targetRun, configs, resultRel⟩ :=
    doEval_simulation cfg source.evalConfig target.evalConfig sourceValues targetValues values states.2.2.2.2
      declarations sourceConfig result run
  exact ⟨targetConfig, result, targetRun, stateRel_update_install cfg source target sourceConfig targetConfig states configs, resultRel⟩

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

import Flapjack.Compiler.Backend.FlatPattern.Proofs.FunctionApplication

/-! Dynamic compiler input preservation for the flat pattern pass. The flat
evaluator and the proof-side value/state relations remain pending HOL review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Decoding a flat list is inverted by the canonical list constructor. -/
theorem valueToList_inverse (value : FlatSem.Value) (values : List FlatSem.Value)
    (decoded : FlatSem.valueToList value = some values) : FlatSem.listToValue values = value := by
  cases value with
  | litv _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ => simp [FlatSem.valueToList] at decoded
  | conv stamp fields =>
    cases stamp with
    | none => simp [FlatSem.valueToList] at decoded
    | some stamp =>
      obtain ⟨tag, typeId⟩ := stamp
      cases fields with
      | nil =>
        by_cases valid : tag = BackendCommon.nilTag ∧ typeId = some FlatSem.listId
        · simp [FlatSem.valueToList, valid] at decoded
          subst values
          rcases valid with ⟨rfl, rfl⟩
          rfl
        · simp [FlatSem.valueToList, valid] at decoded
      | cons head rest =>
        cases rest with
        | nil => simp [FlatSem.valueToList] at decoded
        | cons tail rest =>
          cases rest with
          | cons _ _ => simp [FlatSem.valueToList] at decoded
          | nil =>
            by_cases valid : tag = BackendCommon.consTag ∧ typeId = some FlatSem.listId
            · cases tailDecoded : FlatSem.valueToList tail with
              | none => simp [FlatSem.valueToList, valid, tailDecoded] at decoded
              | some tailValues =>
                simp [FlatSem.valueToList, valid, tailDecoded] at decoded
                subst values
                have tailEq := valueToList_inverse tail tailValues tailDecoded
                rcases valid with ⟨rfl, rfl⟩
                simp [FlatSem.listToValue, tailEq]
            · simp [FlatSem.valueToList, valid] at decoded
termination_by sizeOf value

/-- Related flat lists decode to related element lists. -/
theorem listToValue_related (values : List FlatSem.Value) (target : FlatSem.Value)
    (related : ValueRel (FlatSem.listToValue values) target) :
    ∃ targetValues, target = FlatSem.listToValue targetValues ∧ List.Forall₂ ValueRel values targetValues := by
  induction values generalizing target with
  | nil =>
    obtain ⟨fields, rfl, fieldsRel⟩ := (valueRel_conv (some (BackendCommon.nilTag, some FlatSem.listId)) [] target).1 related
    cases fieldsRel
    exact ⟨[], rfl, .nil⟩
  | cons head tail ih =>
    obtain ⟨fields, rfl, fieldsRel⟩ := (valueRel_conv (some (BackendCommon.consTag, some FlatSem.listId))
      [head, FlatSem.listToValue tail] target).1 related
    cases fieldsRel with
    | cons headRel tailRel =>
      cases tailRel with
      | cons listRel endRel =>
        cases endRel
        rename_i targetHead targetTail
        obtain ⟨targetValues, rfl, valuesRel⟩ := ih targetTail listRel
        exact ⟨targetHead :: targetValues, rfl, .cons headRel valuesRel⟩

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

/-- A flat list of literal values is unchanged by the value relation. -/
theorem literalList_valueRel_eq (values : List FlatSem.Value) (target : FlatSem.Value)
    (literals : ∀ value ∈ values, ∃ literal, value = .litv literal)
    (related : ValueRel (FlatSem.listToValue values) target) : target = FlatSem.listToValue values := by
  obtain ⟨targetValues, targetEq, valuesRel⟩ := listToValue_related values target related
  have equal := related_literal_list valuesRel literals
  simpa [equal] using targetEq

/-- Byte-list decoding agrees on related flat values. -/
theorem valueToBytes_related (value target : FlatSem.Value) (related : ValueRel value target)
    (bytes : List (BitVec 8)) (decoded : FlatSem.valueToBytes value = some bytes) :
    FlatSem.valueToBytes target = some bytes := by
  have listDecoded := (FlatSem.valueToBytes_eq_some value bytes).1 decoded
  have encoded := valueToList_inverse value _ listDecoded
  have targetEq : target = value := by
    rw [← encoded] at related ⊢
    apply literalList_valueRel_eq _ target ?_ related
    intro item member
    obtain ⟨byte, _, rfl⟩ := List.mem_map.mp member
    exact ⟨.word8 byte, rfl⟩
  simpa [targetEq] using decoded

/-- Word-list decoding agrees on related flat values. -/
theorem valueToWords_related (value target : FlatSem.Value) (related : ValueRel value target)
    (words : List (BitVec 64)) (decoded : FlatSem.valueToWords value = some words) :
    FlatSem.valueToWords target = some words := by
  have listDecoded := (FlatSem.valueToWords_eq_some value words).1 decoded
  have encoded := valueToList_inverse value _ listDecoded
  have targetEq : target = value := by
    rw [← encoded] at related ⊢
    apply literalList_valueRel_eq _ target ?_ related
    intro item member
    obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
    exact ⟨.word64 word, rfl⟩
  simpa [targetEq] using decoded

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
                have targetBytes := valueToBytes_related byteValue targetByte bytesRel bytes bytesRun
                have targetWords := valueToWords_related wordValue targetWord wordsRel words wordsRun
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

/-- Dynamic evaluation simulates installed declarations using the
smaller-clock declaration induction hypothesis. -/
theorem compile_eval_simulation_at_clock {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (args : List FlatLang.Exp) (clock : Nat)
    (argumentsIH : ∀ expression ∈ args, ExpressionSimulation (C := C) (F := F) cfg stateCfg expression)
    (decsIH : ∀ (source target sourceFinal : FlatSem.State C F) (declarations : List FlatLang.Exp)
      (outcome : Option (SemanticPrimitivesHOL.ErrorResult FlatSem.Value)),
      source.clock < clock → FlatSem.evaluateDecs source declarations = (sourceFinal, outcome) →
      StateRel stateCfg source target → outcome ≠ some (.abort .typeError) →
      ∃ targetFinal targetOutcome, FlatSem.evaluateDecs target (declarations.map (compileDec stateCfg)) =
        (targetFinal, targetOutcome) ∧ StateRel stateCfg sourceFinal targetFinal ∧ optionRel FlatErrorRel outcome targetOutcome) :
    ∀ (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value) (source target sourceFinal : FlatSem.State C F)
      (sourceResult : Result (List FlatSem.Value) FlatSem.Value) (n : Nat),
      source.clock = clock →
      FlatSem.evaluate sourceEnv source [.app trace (.src .eval) args] = (sourceFinal, sourceResult) →
      EnvRel n sourceEnv targetEnv → StateRel stateCfg source target →
      (compileExp cfg (.app trace (.src .eval) args)).1 < n →
      sourceResult ≠ .err (.abort .typeError) →
      ∃ targetFinal targetResult,
        FlatSem.evaluate targetEnv target [(compileExp cfg (.app trace (.src .eval) args)).2.2] =
          (targetFinal, targetResult) ∧ StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n clockEq sourceEval envs states bound safe
  have argsBound : (compileExps cfg args).1 < n := by simpa [compileExp_app] using bound
  have reversedBound := compileExps_reverse_bound cfg args n argsBound
  have reversedIH : ∀ expression ∈ args.reverse, ExpressionSimulation (C := C) (F := F) cfg stateCfg expression := by
    intro expression member
    exact argumentsIH expression (by simpa using member)
  have argsSim := compileExps_simulation cfg stateCfg args.reverse reversedIH
  have compiledReverse : (compileExps cfg args.reverse).2.2 = (compileExps cfg args).2.2.reverse := by
    simp [compileExps_rows, List.map_reverse]
  cases argsRun : FlatSem.evaluate sourceEnv source args.reverse with
  | mk sourceNext argsResult =>
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      have outer := evaluate_app_args_error sourceEnv source sourceNext trace (.src .eval) args (.abort .typeError) argsRun
      rw [sourceEval] at outer
      exact safe (congrArg Prod.snd outer)
    obtain ⟨targetNext, targetArgsResult, targetArgsRun, nextStates, related⟩ := argsSim
      sourceEnv targetEnv source target sourceNext argsResult n argsRun envs states reversedBound argsSafe
    cases related with
    | error errorsRel =>
      rename_i leftError rightError
      have sourceOuter := evaluate_app_args_error sourceEnv source sourceNext trace (.src .eval) args leftError argsRun
      have targetOuter := evaluate_app_args_error targetEnv target targetNext trace (.src .eval)
        (compileExps cfg args).2.2 rightError (by simpa [compiledReverse] using targetArgsRun)
      have equal := sourceEval.symm.trans sourceOuter
      cases equal
      exact ⟨_, _, by simpa [compileExp_app] using targetOuter,
        stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates, .error errorsRel⟩
    | values valuesRel =>
      rename_i sourceValues targetValues
      let sourceFixed := { sourceNext with clock := min source.clock sourceNext.clock }
      let targetFixed := { targetNext with clock := min target.clock targetNext.clock }
      have fixedStates : StateRel stateCfg sourceFixed targetFixed :=
        stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates
      cases decoded : FlatSem.doEval sourceValues.reverse sourceNext.evalConfig with
      | none =>
        have bad := evaluate_eval_bad sourceEnv source sourceNext trace args sourceValues argsRun decoded
        rw [sourceEval] at bad
        exact (safe (congrArg Prod.snd bad)).elim
      | some payload =>
        obtain ⟨declarations, sourceConfig, result⟩ := payload
        obtain ⟨targetConfig, targetValue, targetDecoded, installedStates, valueRel⟩ :=
          doEval_state_simulation stateCfg sourceFixed targetFixed sourceValues.reverse targetValues.reverse fixedStates
            (valueRel_reverse valuesRel) declarations sourceConfig result decoded
        have targetClock : targetFixed.clock = sourceFixed.clock := fixedStates.1
        by_cases zero : sourceFixed.clock = 0
        · have targetZero : targetFixed.clock = 0 := by omega
          have sourceOuter := evaluate_eval_timeout sourceEnv source sourceNext trace args sourceValues declarations
            sourceConfig result argsRun decoded zero
          have targetOuter := evaluate_eval_timeout targetEnv target targetNext trace (compileExps cfg args).2.2 targetValues
            (declarations.map (compileDec stateCfg)) targetConfig targetValue
            (by simpa [compiledReverse] using targetArgsRun) targetDecoded targetZero
          have equal := sourceEval.symm.trans sourceOuter
          cases equal
          exact ⟨_, _, by simpa [compileExp_app] using targetOuter, installedStates, .error (.abort .timeoutError)⟩
        · have targetNonzero : targetFixed.clock ≠ 0 := by omega
          let sourceInstalled := { sourceFixed with evalConfig := sourceConfig }
          let targetInstalled := { targetFixed with evalConfig := targetConfig }
          have smaller : (FlatSem.decClock sourceInstalled).clock < clock := by
            have clamped := Nat.min_le_left source.clock sourceNext.clock
            have positive : 0 < min source.clock sourceNext.clock := Nat.pos_of_ne_zero zero
            simp only [FlatSem.decClock, sourceInstalled, sourceFixed]
            omega
          have declStates := stateRel_decClock stateCfg sourceInstalled targetInstalled installedStates
          cases declsRun : FlatSem.evaluateDecs (FlatSem.decClock sourceInstalled) declarations with
          | mk sourceLast outcome =>
            have outcomeSafe : outcome ≠ some (.abort .typeError) := by
              intro bad
              subst outcome
              have sourceOuter := evaluate_eval_declarations sourceEnv source sourceNext sourceLast trace args sourceValues
                declarations sourceConfig result (some (.abort .typeError)) argsRun decoded zero declsRun
              rw [sourceEval] at sourceOuter
              exact safe (congrArg Prod.snd sourceOuter)
            obtain ⟨targetLast, targetOutcome, targetDeclsRun, finalRel, outcomeRel⟩ := decsIH
              (FlatSem.decClock sourceInstalled) (FlatSem.decClock targetInstalled) sourceLast declarations outcome
              smaller declsRun declStates outcomeSafe
            cases outcome with
            | none =>
              cases targetOutcome with
              | some error => simp [optionRel] at outcomeRel
              | none =>
                have sourceOuter := evaluate_eval_declarations sourceEnv source sourceNext sourceLast trace args sourceValues
                  declarations sourceConfig result none argsRun decoded zero declsRun
                have targetOuter := evaluate_eval_declarations targetEnv target targetNext targetLast trace (compileExps cfg args).2.2
                  targetValues (declarations.map (compileDec stateCfg)) targetConfig targetValue none
                  (by simpa [compiledReverse] using targetArgsRun) targetDecoded targetNonzero targetDeclsRun
                have equal := sourceEval.symm.trans sourceOuter
                cases equal
                exact ⟨targetLast, _, by simpa [compileExp_app] using targetOuter, finalRel, .values (.cons valueRel .nil)⟩
            | some error =>
              cases targetOutcome with
              | none => simp [optionRel] at outcomeRel
              | some targetError =>
                have errorsRel : FlatErrorRel error targetError := by simpa [optionRel] using outcomeRel
                have sourceOuter := evaluate_eval_declarations sourceEnv source sourceNext sourceLast trace args sourceValues
                  declarations sourceConfig result (some error) argsRun decoded zero declsRun
                have targetOuter := evaluate_eval_declarations targetEnv target targetNext targetLast trace (compileExps cfg args).2.2
                  targetValues (declarations.map (compileDec stateCfg)) targetConfig targetValue (some targetError)
                  (by simpa [compiledReverse] using targetArgsRun) targetDecoded targetNonzero targetDeclsRun
                have equal := sourceEval.symm.trans sourceOuter
                cases equal
                exact ⟨targetLast, _, by simpa [compileExp_app] using targetOuter, finalRel, .error errorsRel⟩

end Flapjack.Compiler.Backend.FlatPattern

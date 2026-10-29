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

end Flapjack.Compiler.Backend.FlatPattern

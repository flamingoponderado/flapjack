module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.DirectCall
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.BlockLists
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.CodeLocations
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.InstallSafety
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.StateRelation.Original
public import Flapjack.Compiler.Backend.Semantics.ClosProps.InstallStep
public import Flapjack.Compiler.Backend.Semantics.ClosProps.DecodeRelations

@[expose] public section

/-! Dynamic installation under closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL (Result)

namespace InstallProofPort
/-- The closure state uses canonical finite-support maps. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end InstallProofPort

/-- Related values have equal byte-decoding results, including failure. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "v_to_bytes"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem valueToBytes_related (value nextValue : Value) (related : ValueRel value nextValue) :
    valueToBytes value = valueToBytes nextValue :=
  ClosProps.simpleValRel_valueToBytes ValueRel value nextValue ⟨valueRelSimple, related⟩

/-- Related values have equal word-decoding results, including failure. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "v_to_words"
  (nested_list_rel_as_mutual := [FunctionsRel])]
theorem valueToWords_related (value nextValue : Value) (related : ValueRel value nextValue) :
    valueToWords value = valueToWords nextValue :=
  ClosProps.simpleValRel_valueToWords value nextValue ValueRel ⟨valueRelSimple, related⟩

/-- Updating a pair of related code lookups with corresponding annotated
entries preserves their relation, including repeated keys. -/
theorem codeUpdates_related (source target : Nat → Option (Nat × ClosLang.Exp))
    (entries : List (Nat × Nat × ClosLang.Exp))
    (related : ∀ key, optionRel CodeRel (source key) (target key)) :
    ∀ key, optionRel CodeRel (FUPDATE_LIST_HOL source entries key)
      (FUPDATE_LIST_HOL target (compile entries) key) := by
  induction entries generalizing source target with
  | nil => simpa [compile, FUPDATE_LIST_HOL] using related
  | cons entry rest ih =>
    obtain ⟨key, arity, body⟩ := entry
    simp only [compile, FUPDATE_LIST_HOL_cons]
    apply ih
    intro other
    by_cases same : other = key
    · subst other
      simp [FUPDATE_HOL, optionRel, CodeRel]
    · simpa [FUPDATE_HOL, same] using related other

/-- Installing annotated code and advancing both oracles preserves the
candidate state relation. -/
theorem stateRel_install {C F : Type} (source target : State C F) (entries : List (Nat × Nat × ClosLang.Exp))
    (states : StateRel source target) :
    StateRel { source with code := source.code.updateListEq entries, compileOracle := holShiftSeq 1 source.compileOracle, clock := source.clock - 1 }
      { target with code := target.code.updateListEq (compile entries), compileOracle := holShiftSeq 1 target.compileOracle, clock := target.clock - 1 } := by
  refine ⟨by simp [states.1], states.2.1, states.2.2.1, ?_, states.2.2.2.2.1,
    states.2.2.2.2.2.1, states.2.2.2.2.2.2.1, ?_⟩
  · funext n
    simp [holShiftSeq, states.2.2.2.1]
  · intro key
    simp only [HolFiniteMapExact.lookup_updateListEq]
    exact codeUpdates_related source.code.lookup target.code.lookup entries states.2.2.2.2.2.2.2 key

/-- Annotation preserves the identifiers of dynamically installed entries. -/
theorem compile_keys (entries : List (Nat × Nat × ClosLang.Exp)) :
    (compile entries).map Prod.fst = entries.map Prod.fst := by
  induction entries with
  | nil => rfl
  | cons first rest ih =>
    obtain ⟨key, arity, body⟩ := first
    simp [compile]

private theorem targetNonType_sourceNonType {C F : Type} (source target : State C F)
    (values nextValues : List Value) (targetResult : Result (List ClosLang.Exp) Value)
    (targetNext : State C F) (valuesRel : List.Forall₂ ValueRel values nextValues)
    (states : StateRel source target) (targetRun : doInstall nextValues target = (targetResult, targetNext))
    (targetNonType : targetResult ≠ .err (.abort .typeError)) :
    (doInstall values source).1 ≠ .err (.abort .typeError) := by
  classical
  obtain ⟨nextByte, nextWord, bytes, words, config, targetProgram, targetAux, nextConfig,
    targetValues, targetBytes, targetWords, targetOracle, targetCompile, targetFresh,
    targetNodup, targetConfig, targetNonempty, _, _⟩ :=
      doInstall_nonType_parts nextValues target targetNext targetResult targetRun targetNonType
  subst nextValues
  cases valuesRel with
  | cons byteRel rest =>
    cases rest with
    | cons wordRel rest =>
      cases rest
      rename_i byteValue wordValue
      have bytesRun : valueToBytes byteValue = some bytes := by
        rw [valueToBytes_related byteValue nextByte byteRel, targetBytes]
      have wordsRun : valueToWords wordValue = some words := by
        rw [valueToWords_related wordValue nextWord wordRel, targetWords]
      cases oracleRun : source.compileOracle 0 with
      | mk sourceConfig program =>
        cases program with
        | mk expressions auxiliary =>
          have targetOracleEq : target.compileOracle 0 =
              (sourceConfig, annotateList 0 expressions, compile auxiliary) := by
            rw [states.2.2.2.1]
            simp [pureCo, compileInc, oracleRun]
          rw [targetOracleEq] at targetOracle
          cases targetOracle
          have sourceFresh : ∀ index ∈ auxiliary.map Prod.fst, source.code.lookup index = none := by
            intro index member
            have targetNone := targetFresh index (by simpa [compile_keys] using member)
            have rel := states.2.2.2.2.2.2.2 index
            cases left : source.code.lookup index <;> cases right : target.code.lookup index <;>
              simp_all [optionRel]
          have sourceNodup : (auxiliary.map Prod.fst).Nodup := by
            simpa [compile_keys] using targetNodup
          have sourceCompile : source.compile config (expressions, auxiliary) =
              some (bytes, words, nextConfig) := by
            rw [states.2.2.2.2.1]
            simpa [pureCc, compileInc] using targetCompile
          have sourceConfigNext : (holShiftSeq 1 source.compileOracle 0).1 = nextConfig := by
            simpa [holShiftSeq, states.2.2.2.1, pureCo] using targetConfig
          have sourceNonempty : expressions ≠ [] := by
            intro empty
            apply targetNonempty
            apply List.eq_nil_of_length_eq_zero
            simpa [empty] using annotateList_length 0 expressions
          have valid : (∀ index ∈ auxiliary.map Prod.fst, source.code.lookup index = none) ∧
              (auxiliary.map Prod.fst).Nodup := ⟨sourceFresh, sourceNodup⟩
          simp only [doInstall, bytesRun, wordsRun, oracleRun]
          rw [if_pos valid, sourceCompile]
          by_cases zero : source.clock = 0 <;>
            simp [sourceConfigNext, sourceNonempty, zero]

/-- Related installations have related results and final states, including errors. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "do_install_thm"
  (nested_list_rel_as_mutual := [FunctionsRel]) (fmap_as_finite_support := [refs, code])]
theorem doInstall_full {C F : Type} (source target : State C F)
    (values nextValues : List Value) (result : Result (List ClosLang.Exp) Value)
    (next : State C F) (nextResult : Result (List ClosLang.Exp) Value) (nextTarget : State C F)
    (premises : StateRelSource source target ∧ List.Forall₂ ValueRel values nextValues ∧
      doInstall values source = (result, next) ∧ doInstall nextValues target = (nextResult, nextTarget)) :
    Flapjack.SemanticPrimitivesProps.resultRel (fun e1 e2 => e2 = annotateSource 0 e1) (· = ·) result nextResult ∧
      StateRelSource next nextTarget := by
  obtain ⟨states, valuesRel, sourceRun, targetRun⟩ := premises
  have oldStates := (stateRelSource_iff source target).mp states
  by_cases typeError : result = .err (.abort .typeError)
  · subst result
    have targetError : nextResult = .err (.abort .typeError) := by
      by_contra notError
      have nonType := targetNonType_sourceNonType source target values nextValues nextResult nextTarget
        valuesRel oldStates targetRun notError
      rw [sourceRun] at nonType
      exact nonType rfl
    subst nextResult
    have sourceEq := doInstall_typeError_state values source next sourceRun
    have targetEq := doInstall_typeError_state nextValues target nextTarget targetRun
    subst next
    subst nextTarget
    exact ⟨by simp [Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel], states⟩
  ·
    have nonTypeStep : ∃ targetResult targetState,
        doInstall nextValues target = (targetResult, targetState) ∧ StateRel next targetState ∧
        Flapjack.SemanticPrimitivesProps.resultRel (fun e1 e2 => e2 = annotateList 0 e1) (· = ·) result targetResult := by
      classical
      obtain ⟨byteValue, wordValue, bytes, words, config, expressions, auxiliary, nextConfig,
        valuesEq, bytesRun, wordsRun, oracleRun, compileRun, fresh, nodup, nextConfigEq, nonempty, nextEq, resultEq⟩ :=
          doInstall_nonType_parts values source next result sourceRun typeError
      subst values
      cases valuesRel with
      | cons byteRel tail =>
        cases tail with
        | cons wordRel tail =>
          cases tail
          rename_i nextByte nextWord
          have nextBytes : valueToBytes nextByte = some bytes := by
            rw [← valueToBytes_related byteValue nextByte byteRel, bytesRun]
          have nextWords : valueToWords nextWord = some words := by
            rw [← valueToWords_related wordValue nextWord wordRel, wordsRun]
          have targetOracle : target.compileOracle 0 = (config, annotateList 0 expressions, compile auxiliary) := by
            rw [oldStates.2.2.2.1]
            simp [oracleRun, pureCo, compileInc]
          have targetFresh : ∀ key ∈ (compile auxiliary).map Prod.fst, target.code.lookup key = none := by
            intro key member
            have sourceNone := fresh key (by simpa [compile_keys] using member)
            have rel := oldStates.2.2.2.2.2.2.2 key
            cases targetLookup : target.code.lookup key <;> simp_all [optionRel]
          have targetNodup : ((compile auxiliary).map Prod.fst).Nodup := by simpa [compile_keys] using nodup
          have targetFreshEntries : ∀ key arity body, (key, arity, body) ∈ compile auxiliary →
              target.code.lookup key = none := by
            intro key arity body member
            apply targetFresh key
            exact List.mem_map.mpr ⟨(key, arity, body), member, rfl⟩
          have targetCompile : target.compile config (annotateList 0 expressions, compile auxiliary) =
              some (bytes, words, nextConfig) := by
            have h := compileRun
            rw [oldStates.2.2.2.2.1] at h
            simpa [pureCc, compileInc] using h
          have targetConfig : (holShiftSeq 1 target.compileOracle 0).1 = nextConfig := by
            simpa [holShiftSeq, oldStates.2.2.2.1, pureCo] using nextConfigEq
          have targetNonempty : annotateList 0 expressions ≠ [] := by
            intro empty
            have size := annotateList_length 0 expressions
            rw [empty] at size
            have : expressions = [] := by simpa using size.symm
            exact nonempty this
          let nextTarget := { target with code := target.code.updateListEq (compile auxiliary), compileOracle := holShiftSeq 1 target.compileOracle, clock := target.clock - 1 }
          refine ⟨if source.clock = 0 then .err (.abort .timeoutError) else .val (annotateList 0 expressions),
            nextTarget, ?_, ?_, ?_⟩
          · by_cases zero : source.clock = 0
            · have targetZero : target.clock = 0 := by simpa [← oldStates.1] using zero
              simp [doInstall, nextBytes, nextWords, targetOracle, targetNodup,
                targetCompile, targetConfig, targetNonempty, zero, targetZero, nextTarget]
              exact targetFreshEntries
            · have targetNonzero : target.clock ≠ 0 := by simpa [← oldStates.1] using zero
              simp [doInstall, nextBytes, nextWords, targetOracle, targetNodup,
                targetCompile, targetConfig, targetNonempty, zero, targetNonzero, nextTarget]
              exact targetFreshEntries
          · simpa [nextEq, nextTarget] using stateRel_install source target auxiliary oldStates
          · rw [resultEq]
            split <;> simp [Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]
    obtain ⟨targetResult, targetState, targetRun', targetRelated, resultRelated⟩ := nonTypeStep
    rw [targetRun] at targetRun'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj targetRun'
    refine ⟨?_, (stateRelSource_iff _ _).mpr targetRelated⟩
    have annotateEq : annotateSource 0 = annotateList 0 := by
      funext es
      exact (annotateSource_sing_eq 0 (.var .none 0) es).2
    simpa [annotateEq] using resultRelated


/-- Nonempty related lists have related HOL last elements. -/
theorem holLast_related {left right : List Value}
    (related : List.Forall₂ ValueRel left right) (nonempty : left ≠ []) :
    ValueRel (@holLast Value ⟨unitValue⟩ left) (@holLast Value ⟨unitValue⟩ right) := by
  induction related with
  | nil => exact (nonempty rfl).elim
  | @cons first nextFirst rest nextRest head tail ih =>
    cases tail with
    | nil => simpa [holLast] using head
    | @cons second nextSecond tail nextTail nextHead restRel =>
      simp only [holLast]
      exact ih (by simp)

/-- The installed program runs at a smaller clock, with the empty
environment and the annotated oracle program. -/
theorem runInstalled_related {C F : Type} (source target : State C F) (values nextValues : List Value)
    (result : Result (List Value) Value) (final : State C F)
    (run : runInstalled values source = (result, final)) (noType : result ≠ .err (.abort .typeError))
    (states : StateRel source target) (valuesRel : List.Forall₂ ValueRel values nextValues)
    (code : CodeSafe source) (oracle : OracleSafe source)
    (programIH : ∀ (program : List ClosLang.Exp) (state : State C F), state.clock < source.clock →
      EvalSimulationAt state program) :
    ∃ targetResult targetFinal, runInstalled nextValues target = (targetResult, targetFinal) ∧
      ResultRel result targetResult ∧ StateRel final targetFinal := by
  cases installRun : doInstall values source with
  | mk installResult installed =>
    have installNoType : installResult ≠ .err (.abort .typeError) := by
      intro bad
      subst installResult
      simp [runInstalled, installRun] at run
      exact noType run.1.symm
    obtain ⟨targetInstallResult, targetInstalled, targetInstallRun⟩ :
        ∃ targetResult targetState, doInstall nextValues target = (targetResult, targetState) := by
      cases h : doInstall nextValues target with
      | mk targetResult targetState => exact ⟨targetResult, targetState, rfl⟩
    have ⟨resultRel, installedRelSource⟩ := doInstall_full source target values nextValues
      installResult installed targetInstallResult targetInstalled
      ⟨(stateRelSource_iff source target).mpr states, valuesRel, installRun, targetInstallRun⟩
    have installedRel := (stateRelSource_iff installed targetInstalled).mp installedRelSource
    have annotateEq : annotateSource 0 = annotateList 0 := by
      funext es
      exact (annotateSource_sing_eq 0 (.var .none 0) es).2
    rw [annotateEq] at resultRel
    let outcome : Result (List ClosLang.Exp) Value → Result (List ClosLang.Exp) Value → Prop :=
      fun left right => match left, right with
        | .err (.abort .timeoutError), .err (.abort .timeoutError) => True
        | .val program, .val nextProgram => nextProgram = annotateList 0 program
        | _, _ => False
    have installRel : outcome installResult targetInstallResult := by
      obtain ⟨_, _, _, _, _, expressions, _, _, _, _, _, _, _, _, _, _, _, _, resultEq⟩ :=
        doInstall_nonType_parts values source installed installResult installRun installNoType
      have shapeFn : ∀ (left right : Result (List ClosLang.Exp) Value) (clock : Nat)
          (program : List ClosLang.Exp),
          left = (if clock = 0 then .err (.abort .timeoutError) else .val program) →
          Flapjack.SemanticPrimitivesProps.resultRel (fun e1 e2 => e2 = annotateList 0 e1) (· = ·) left right →
          outcome left right := by
        intro left right clock program shape related
        subst left
        unfold outcome
        by_cases zero : clock = 0
        · simp only [zero, if_true] at related ⊢
          cases right with
          | val val => simp [Flapjack.SemanticPrimitivesProps.resultRel] at related
          | err error =>
            cases error with
            | raise value => simp [Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel] at related
            | abort abort =>
              cases abort <;> simp_all [Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel]
        · simp only [zero, if_false] at related ⊢
          cases right <;> simp_all [Flapjack.SemanticPrimitivesProps.resultRel]
      exact shapeFn installResult targetInstallResult source.clock expressions resultEq resultRel
    have installedSafe := doInstall_preserves_safe_all values source installed installResult installRun code oracle
    cases installResult with
    | err error =>
      cases error with
      | raise value => cases targetInstallResult <;> simp [outcome] at installRel
      | abort abort =>
        cases abort <;> cases targetInstallResult <;> simp [outcome] at installRel
        rename_i nextError
        cases nextError <;> try simp at installRel
        rename_i nextAbort
        cases nextAbort <;> try simp at installRel
        simp [runInstalled, installRun] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨.err (.abort .timeoutError), targetInstalled, by simp [runInstalled, targetInstallRun], rfl, installedRel⟩
    | val program =>
      cases targetInstallResult with
      | err error => cases error <;> simp [outcome] at installRel
      | val nextProgram =>
        have programEq : nextProgram = annotateList 0 program := by simpa [outcome] using installRel
        subst nextProgram
        obtain ⟨_, _, _, _, _, expressions, _, _, _, _, _, oracleEntry, _, _, _, _, nonempty, _, resultEq⟩ :=
          doInstall_nonType_parts values source installed (.val program) installRun (by simp)
        have programEq : program = expressions := by
          split at resultEq <;> simp_all
        subst expressions
        have smaller : installed.clock < source.clock := by
          have clock := doInstall_success_clock values source installed program installRun
          omega
        cases programRun : evaluate program [] installed with
        | mk programResult last =>
          have programNoType : programResult ≠ .err (.abort .typeError) := by
            intro bad
            subst programResult
            simp [runInstalled, installRun, programRun] at run
            exact noType run.1.symm
          have vars : ∀ n, altFv n program = true → EnvOk 0 0 .ln [] [] n := by
            exact envSetDefault {n | altFv n program = true} []
          obtain ⟨targetProgramResult, targetLast, targetProgramRun, programRel, lastRel⟩ :=
            programIH program installed smaller [] [] targetInstalled programResult last 0 0 .ln
              programRun programNoType (by simp) vars (by simpa [oracleEntry] using (oracle 0).1)
              installedSafe.1 installedSafe.2 installedRel
          have targetRun : evaluate (annotateList 0 program) [] targetInstalled = (targetProgramResult, targetLast) := by
            simpa [annotateList, altFree] using targetProgramRun
          cases programResult with
          | err error =>
            simp [runInstalled, installRun, programRun] at run
            obtain ⟨rfl, rfl⟩ := run
            cases targetProgramResult with
            | val values => cases error <;> simp [ResultRel, Flapjack.SemanticPrimitivesProps.resultRel] at programRel
            | err targetError =>
              exact ⟨.err targetError, targetLast, by simp [runInstalled, targetInstallRun, targetRun], programRel, lastRel⟩
          | val returned =>
            cases targetProgramResult with
            | err error => cases error <;> simp [ResultRel, Flapjack.SemanticPrimitivesProps.resultRel] at programRel
            | val targetReturned =>
              have returnedNonempty : returned ≠ [] := by
                intro empty
                subst returned
                have size := (evaluate_length (C := C) (F := F)).1 program [] installed last [] programRun
                have : program = [] := List.eq_nil_of_length_eq_zero size.symm
                exact nonempty this
              have lastValues := holLast_related programRel returnedNonempty
              simp [runInstalled, installRun, programRun] at run
              obtain ⟨rfl, rfl⟩ := run
              exact ⟨.val [@holLast Value ⟨unitValue⟩ targetReturned], targetLast,
                by simp [runInstalled, targetInstallRun, targetRun], .cons lastValues .nil, lastRel⟩

/-- Installation expressions compose argument simulation with the
smaller-clock installed-program induction case. -/
theorem evaluate_install_step {C F : Type} (trace : BackendCommon.Tra) (args : List ClosLang.Exp)
    (source : State C F) (argsIH : EvalSimulationAt source args)
    (programIH : ∀ (program : List ClosLang.Exp) (state : State C F), state.clock < source.clock →
      EvalSimulationAt state program) : EvalSimulationAt source [.op trace .install args] := by
  intro env nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have argsVars : ∀ n, altFv n args = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    simpa [altFv_op] using present
  have argsSafe : everyFnVarsNone args := by simpa [everyFnVarsNone, fnVarsNoneExp] using safe
  rw [evaluate_install_eq] at run
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    rw [argsRun] at run
    cases argsResult with
    | err error =>
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env nextEnv target (.err error) sourceNext m l index argsRun noType length argsVars argsSafe code oracle states
      cases targetResult with
      | val values => cases error <;> simp [ResultRel, Flapjack.SemanticPrimitivesProps.resultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        rw [altFree_op]
        simp only [shiftList, shiftSing]
        rw [evaluate_install_eq, targetRun]
    | val values =>
      have valuesNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env nextEnv target (.val values) middle m l index argsRun valuesNoType length argsVars argsSafe code oracle states
      cases targetResult with
      | err error => cases error <;> simp [ResultRel, Flapjack.SemanticPrimitivesProps.resultRel] at resultRel
      | val nextValues =>
        have middleSafe := (evaluate_preserves_safe.1 args) env source (.val values) middle argsRun code oracle
        have middleClock : middle.clock ≤ source.clock := by
          have h := evaluate_clock_le args env source
          simpa [argsRun] using h
        obtain ⟨targetInstalledResult, targetLast, targetInstallRun, installRel, lastRel⟩ :=
          runInstalled_related middle targetMiddle values.reverse nextValues.reverse result sourceNext run noType middleRel
            (List.forall₂_reverse_iff.mpr resultRel) middleSafe.1 middleSafe.2 (by
              intro program state smaller
              exact programIH program state (by omega))
        refine ⟨targetInstalledResult, targetLast, ?_, installRel, lastRel⟩
        rw [altFree_op]
        simp only [shiftList, shiftSing]
        rw [evaluate_install_eq, targetRun]
        exact targetInstallRun

end Flapjack.Compiler.Backend.ClosAnnotate

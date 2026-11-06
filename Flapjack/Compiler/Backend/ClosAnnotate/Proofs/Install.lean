import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.DirectCall
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.CodeLocations

/-! Dynamic installation under closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Lists of numeric values cannot change under the candidate value relation. -/
theorem related_number_list (numbers : List Int) (values : List Value)
    (related : List.Forall₂ ValueRel (numbers.map Value.number) values) :
    values = numbers.map Value.number := by
  induction numbers generalizing values with
  | nil => cases related; rfl
  | cons number numbers ih =>
    cases related with
    | cons head tail =>
      cases head
      simp only [List.map_cons, List.cons.injEq, true_and]
      exact ih _ tail

/-- Lists of 64-bit words cannot change under the candidate value relation. -/
theorem related_word_list (words : List (BitVec 64)) (values : List Value)
    (related : List.Forall₂ ValueRel (words.map Value.word64) values) :
    values = words.map Value.word64 := by
  induction words generalizing values with
  | nil => cases related; rfl
  | cons word words ih =>
    cases related with
    | cons head tail =>
      cases head
      simp only [List.map_cons, List.cons.injEq, true_and]
      exact ih _ tail

/-- A valid byte payload decodes identically in a related value. -/
theorem valueToBytes_related (value nextValue : Value) (bytes : List (BitVec 8))
    (related : ValueRel value nextValue) (decoded : valueToBytes value = some bytes) :
    valueToBytes nextValue = some bytes := by
  have source := (valueToBytes_eq_some value bytes).mp decoded
  have relation := valueToList_related value nextValue related
  cases target : valueToList nextValue with
  | none => simp [source, target, optionRel] at relation
  | some values =>
    have listRel : List.Forall₂ ValueRel (bytes.map (fun b => .number b.toNat)) values := by
      simpa [source, target, optionRel] using relation
    have same : values = bytes.map (fun b => .number b.toNat) := by
      have listRel' : List.Forall₂ ValueRel
          ((bytes.map (fun b => (b.toNat : Int))).map Value.number) values := by
        simpa [List.map_map] using listRel
      simpa [List.map_map, Function.comp_def] using related_number_list (bytes.map (fun b => (b.toNat : Int))) values listRel'
    apply (valueToBytes_eq_some nextValue bytes).mpr
    simpa [same] using target

/-- A valid word payload decodes identically in a related value. -/
theorem valueToWords_related (value nextValue : Value) (words : List (BitVec 64))
    (related : ValueRel value nextValue) (decoded : valueToWords value = some words) :
    valueToWords nextValue = some words := by
  have source := (valueToWords_eq_some value words).mp decoded
  have relation := valueToList_related value nextValue related
  cases target : valueToList nextValue with
  | none => simp [source, target, optionRel] at relation
  | some values =>
    have listRel : List.Forall₂ ValueRel (words.map Value.word64) values := by
      simpa [source, target, optionRel] using relation
    have same := related_word_list words values listRel
    apply (valueToWords_eq_some nextValue words).mpr
    simpa [same] using target

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

/-- Related installation outcomes are matching timeouts or annotated programs. -/
def InstallResultRel : Result (List ClosLang.Exp) Value → Result (List ClosLang.Exp) Value → Prop
  | .err (.abort .timeoutError), .err (.abort .timeoutError) => True
  | .val program, .val nextProgram => nextProgram = annotateList 0 program
  | _, _ => False

/-- A non-type-error installation runs with the same payload and status in
the target, installs annotated code and leaves related states. -/
theorem doInstall_related_nonType {C F : Type} (source target : State C F)
    (values nextValues : List Value) (result : Result (List ClosLang.Exp) Value) (next : State C F)
    (valuesRel : List.Forall₂ ValueRel values nextValues) (states : StateRel source target)
    (run : doInstall values source = (result, next)) (noType : result ≠ .err (.abort .typeError)) :
    ∃ nextResult nextTarget,
      doInstall nextValues target = (nextResult, nextTarget) ∧ StateRel next nextTarget ∧
      InstallResultRel result nextResult := by
  classical
  obtain ⟨byteValue, wordValue, bytes, words, config, expressions, auxiliary, nextConfig,
    valuesEq, bytesRun, wordsRun, oracleRun, compileRun, fresh, nodup, nextConfigEq, nonempty, nextEq, resultEq⟩ :=
      doInstall_nonType_parts values source next result run noType
  subst values
  cases valuesRel with
  | cons byteRel tail =>
    cases tail with
    | cons wordRel tail =>
      cases tail
      rename_i nextByte nextWord
      have nextBytes := valueToBytes_related byteValue nextByte bytes byteRel bytesRun
      have nextWords := valueToWords_related wordValue nextWord words wordRel wordsRun
      have targetOracle : target.compileOracle 0 = (config, annotateList 0 expressions, compile auxiliary) := by
        rw [states.2.2.2.1]
        simp [oracleRun, pureCo, compileInc]
      have targetFresh : ∀ key ∈ (compile auxiliary).map Prod.fst, target.code.lookup key = none := by
        intro key member
        have sourceNone := fresh key (by simpa [compile_keys] using member)
        have rel := states.2.2.2.2.2.2.2 key
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
        rw [states.2.2.2.2.1] at h
        simpa [pureCc, compileInc] using h
      have targetConfig : (holShiftSeq 1 target.compileOracle 0).1 = nextConfig := by
        simpa [holShiftSeq, states.2.2.2.1, pureCo] using nextConfigEq
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
        · have targetZero : target.clock = 0 := by simpa [← states.1] using zero
          simp [doInstall, nextBytes, nextWords, targetOracle, targetNodup,
            targetCompile, targetConfig, targetNonempty, zero, targetZero, nextTarget]
          exact targetFreshEntries
        · have targetNonzero : target.clock ≠ 0 := by simpa [← states.1] using zero
          simp [doInstall, nextBytes, nextWords, targetOracle, targetNodup,
            targetCompile, targetConfig, targetNonempty, zero, targetNonzero, nextTarget]
          exact targetFreshEntries
      · simpa [nextEq, nextTarget] using stateRel_install source target auxiliary states
      · rw [resultEq]
        split <;> simp [InstallResultRel]

/-- Continue an installation by evaluating the installed program. -/
noncomputable def runInstalled {C F : Type} (values : List Value) (state : State C F) : EvalResult C F :=
  match doInstall values state with
  | (.err error, next) => (.err error, next)
  | (.val program, next) =>
    let (result, last) := evaluate program [] next
    match result with
    | .err error => (.err error, last)
    | .val values => (.val [@holLast Value ⟨unitValue⟩ values], last)

/-- Installation evaluates its arguments before the compiler and program. -/
theorem evaluate_install_eq {C F : Type} (trace : BackendCommon.Tra) (args : List ClosLang.Exp)
    (env : List Value) (state : State C F) :
    evaluate [.op trace .install args] env state =
      match evaluate args env state with
      | (.err error, next) => (.err error, next)
      | (.val values, next) => runInstalled values.reverse next := by
  rw [evaluate, fixClock_evaluate]
  cases evaluated : evaluate args env state with
  | mk result next =>
    cases result with
    | err error => rfl
    | val values =>
      dsimp only
      unfold runInstalled
      split <;> simp_all
      split <;> simp_all
      rfl

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
    obtain ⟨targetInstallResult, targetInstalled, targetInstallRun, installedRel, installRel⟩ :=
      doInstall_related_nonType source target values nextValues installResult installed valuesRel states installRun installNoType
    have installedSafe := doInstall_preserves_safe_all values source installed installResult installRun code oracle
    cases installResult with
    | err error =>
      cases error with
      | raise value => cases targetInstallResult <;> simp [InstallResultRel] at installRel
      | abort abort =>
        cases abort <;> cases targetInstallResult <;> simp [InstallResultRel] at installRel
        rename_i nextError
        cases nextError <;> try simp at installRel
        rename_i nextAbort
        cases nextAbort <;> try simp at installRel
        simp [runInstalled, installRun] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨.err (.abort .timeoutError), targetInstalled, by simp [runInstalled, targetInstallRun], rfl, installedRel⟩
    | val program =>
      cases targetInstallResult with
      | err error => cases error <;> simp [InstallResultRel] at installRel
      | val nextProgram =>
        have programEq : nextProgram = annotateList 0 program := installRel
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
            intro n _
            exact .outside 0 0 .ln [] [] n (by omega)
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
            | val values => cases error <;> simp [ResultRel] at programRel
            | err targetError =>
              exact ⟨.err targetError, targetLast, by simp [runInstalled, targetInstallRun, targetRun], programRel, lastRel⟩
          | val returned =>
            cases targetProgramResult with
            | err error => cases error <;> simp [ResultRel] at programRel
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
      | val values => cases error <;> simp [ResultRel] at resultRel
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
      | err error => cases error <;> simp [ResultRel] at resultRel
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

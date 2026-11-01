import Flapjack.Compiler.Backend.ClosToBvl.Proofs.SourceChain
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Semantics

/-! Observable behavior of source programs and their installed entry chains. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.SemanticPrimitivesHOL

/-- Discarding all but the final value does not change an observable outcome. -/
theorem sourceChainResult_outcome (result : Result (List ClosSem.Value) ClosSem.Value) (outcome : HolOutcome) :
    resultObservesOutcome (sourceChainResult result) outcome ↔ resultObservesOutcome result outcome := by
  cases result with
  | val values => rfl
  | err error => cases error with
    | raise value => rfl
    | abort reason => cases reason <;> rfl

/-- The chain projection reflects type errors. -/
theorem sourceChainResult_typeError (result : Result (List ClosSem.Value) ClosSem.Value)
    (error : sourceChainResult result = .err (.abort .typeError)) : result = .err (.abort .typeError) := by
  cases result <;> simp [sourceChainResult] at error ⊢
  exact error

/-- Clocked evaluation of a source expression list is simulated by calling
its installed chain, with the same FFI state. -/
theorem sourceChain_initial_simulation {C F : Type} (ffi : HolFfiState F) (maxApp start : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (oracle : CompileOracle C) (compiler : Compiler C)
    (expressions : List ClosLang.Exp) (nonempty : expressions ≠ [])
    (fresh : ∀ key, start ≤ key → key < start + expressions.length → code.lookup key = none)
    (ordered : Flapjack.Compiler.Backend.BackendProps.oracleMonotonic oracleCodeNames (· < ·)
      ({ key | start ≤ key ∧ key < start + expressions.length } ∪ codeDomain code) oracle) :
    ∀ clock result final,
      evaluate expressions [] (initialState ffi maxApp code oracle compiler clock) = (result, final) →
      result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        evaluate [.call .none 0 start []] []
          (initialState ffi maxApp (sourceCodeWithChain start expressions code) oracle compiler (clock + extra)) =
          (sourceChainResult result, targetFinal) ∧ final.ffi = targetFinal.ffi := by
  intro clock result final run noType
  obtain ⟨extra, targetFinal, targetRun, finalRel⟩ :=
    evaluate_sourceCodeWithChain_call expressions start (initialState ffi maxApp code oracle compiler clock) final result
      nonempty fresh ordered run noType
  refine ⟨extra, targetFinal, ?_, ?_⟩
  · simpa [initialState] using targetRun
  · have same := finalRel.1
    rw [same]

/-- For a non-failing nonempty source, a generated chain call has the same
proof-side whole-program behavior. The evaluator and map carriers still need
review against the original HOL semantics. -/
theorem sourceChain_semantics_eq {C F : Type} (ffi : HolFfiState F) (maxApp start : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (oracle : CompileOracle C) (compiler : Compiler C)
    (expressions : List ClosLang.Exp) (nonempty : expressions ≠ [])
    (fresh : ∀ key, start ≤ key → key < start + expressions.length → code.lookup key = none)
    (ordered : Flapjack.Compiler.Backend.BackendProps.oracleMonotonic oracleCodeNames (· < ·)
      ({ key | start ≤ key ∧ key < start + expressions.length } ∪ codeDomain code) oracle)
    (nonfail : semantics ffi maxApp code oracle compiler expressions ≠ .fail) :
    semantics ffi maxApp (sourceCodeWithChain start expressions code) oracle compiler [.call .none 0 start []] =
      semantics ffi maxApp code oracle compiler expressions := by
  classical
  let targetCode := sourceCodeWithChain start expressions code
  let targetProgram := [ClosLang.Exp.call .none 0 start []]
  have sourceSafe := (semantics_ne_fail_iff ffi maxApp code oracle compiler expressions).mp nonfail
  have simulation := sourceChain_initial_simulation ffi maxApp start code oracle compiler expressions nonempty fresh ordered
  have targetSafe : ∀ clock, (evaluate targetProgram [] (initialState ffi maxApp targetCode oracle compiler clock)).1 ≠
      .err (.abort .typeError) := by
    intro clock targetError
    cases sourceRun : evaluate expressions [] (initialState ffi maxApp code oracle compiler clock) with
    | mk sourceResult sourceFinal =>
      have noType : sourceResult ≠ .err (.abort .typeError) := by simpa [sourceRun] using sourceSafe clock
      obtain ⟨extra, targetFinal, targetRun, _⟩ := simulation clock sourceResult sourceFinal sourceRun noType
      cases targetRun0 : evaluate targetProgram [] (initialState ffi maxApp targetCode oracle compiler clock) with
      | mk targetResult targetFinal0 =>
        have resultEq : targetResult = .err (.abort .typeError) := by simpa [targetRun0] using targetError
        subst targetResult
        have shifted := evaluate_initial_addClock ffi maxApp clock extra targetCode oracle compiler targetProgram
          (.err (.abort .typeError)) targetFinal0 targetRun0 (by simp)
        change evaluate targetProgram [] (initialState ffi maxApp targetCode oracle compiler (clock + extra)) = _ at targetRun
        rw [targetRun] at shifted
        have resultEq : sourceChainResult sourceResult = .err (.abort .typeError) := (Prod.mk.inj shifted).1
        exact noType (sourceChainResult_typeError sourceResult resultEq)
  have terminatingEq : terminatingObservation ffi maxApp code oracle compiler expressions =
      terminatingObservation ffi maxApp targetCode oracle compiler targetProgram := by
    funext behavior
    apply propext
    constructor
    · rintro ⟨clock, result, final, outcome, run, observes, behaviorEq⟩
      have noType : result ≠ .err (.abort .typeError) := by simpa [run] using sourceSafe clock
      obtain ⟨extra, targetFinal, targetRun, ffiEq⟩ := simulation clock result final run noType
      have sourceOutcome : resultObservesOutcome result outcome := by
        cases result with
        | val value => exact observes
        | err error => cases error with
          | raise value => exact observes
          | abort reason => cases reason <;> exact observes
      have targetOutcome := (sourceChainResult_outcome result outcome).mpr sourceOutcome
      refine ⟨clock + extra, sourceChainResult result, targetFinal, outcome, targetRun, ?_, ?_⟩
      · cases projected : sourceChainResult result with
        | val value => simpa [projected, resultObservesOutcome] using targetOutcome
        | err error => cases error with
          | raise value => simpa [projected, resultObservesOutcome] using targetOutcome
          | abort reason => cases reason <;> simp [projected, resultObservesOutcome] at targetOutcome ⊢ <;> assumption
      · simpa [ffiEq] using behaviorEq
    · rintro ⟨clock, targetResult, targetFinal, outcome, targetRun, observes, behaviorEq⟩
      have targetOutcome : resultObservesOutcome targetResult outcome := by
        cases targetResult with
        | val value => exact observes
        | err error => cases error with
          | raise value => exact observes
          | abort reason => cases reason <;> exact observes
      have notTimeout := resultObservesOutcome_notTimeout targetResult outcome targetOutcome
      cases sourceRun : evaluate expressions [] (initialState ffi maxApp code oracle compiler clock) with
      | mk sourceResult sourceFinal =>
        have noType : sourceResult ≠ .err (.abort .typeError) := by simpa [sourceRun] using sourceSafe clock
        obtain ⟨extra, final2, targetRun2, ffiEq⟩ := simulation clock sourceResult sourceFinal sourceRun noType
        have shifted := evaluate_initial_addClock ffi maxApp clock extra targetCode oracle compiler targetProgram
          targetResult targetFinal targetRun notTimeout
        change evaluate targetProgram [] (initialState ffi maxApp targetCode oracle compiler (clock + extra)) = _ at targetRun2
        rw [targetRun2] at shifted
        obtain ⟨resultEq, stateEq⟩ := Prod.mk.inj shifted
        have finalFfi : sourceFinal.ffi = targetFinal.ffi := by rw [ffiEq, stateEq]
        have sourceOutcome := (sourceChainResult_outcome sourceResult outcome).mp (resultEq ▸ targetOutcome)
        refine ⟨clock, sourceResult, sourceFinal, outcome, sourceRun, ?_, by simpa [finalFfi] using behaviorEq⟩
        cases sourceResult with
        | val value => exact sourceOutcome
        | err error => cases error with
          | raise value => exact sourceOutcome
          | abort reason => cases reason <;> exact sourceOutcome
  have traceEq :
      HolLList.buildLprefixLub (fun trace => ∃ clock,
        trace = HolLList.fromList (evaluate expressions [] (initialState ffi maxApp code oracle compiler clock)).2.ffi.ioEvents) =
      HolLList.buildLprefixLub (fun trace => ∃ clock,
        trace = HolLList.fromList (evaluate targetProgram [] (initialState ffi maxApp targetCode oracle compiler clock)).2.ffi.ioEvents) := by
    apply clocked_traces_lub_eq
    · exact evaluate_initial_ioEvents_mono ffi maxApp code oracle compiler expressions
    · exact evaluate_initial_ioEvents_mono ffi maxApp targetCode oracle compiler targetProgram
    · intro clock
      cases sourceRun : evaluate expressions [] (initialState ffi maxApp code oracle compiler clock) with
      | mk result final =>
        have noType : result ≠ .err (.abort .typeError) := by simpa [sourceRun] using sourceSafe clock
        obtain ⟨extra, targetFinal, targetRun, ffiEq⟩ := simulation clock result final sourceRun noType
        exact ⟨extra, by simp [targetProgram, targetCode, targetRun, ffiEq]⟩
  change semantics ffi maxApp targetCode oracle compiler targetProgram = _
  unfold semantics
  simp only [show ¬ ∃ clock, (evaluate expressions [] (initialState ffi maxApp code oracle compiler clock)).1 = .err (.abort .typeError) from
    fun ⟨clock, error⟩ => sourceSafe clock error,
    show ¬ ∃ clock, (evaluate targetProgram [] (initialState ffi maxApp targetCode oracle compiler clock)).1 = .err (.abort .typeError) from
    fun ⟨clock, error⟩ => targetSafe clock error, if_false]
  rw [terminatingEq, traceEq]

/-- Combining the generated chain with an association-list program produces
the same source map as installing the chain over the program's initial map. -/
theorem initialSourceCode_chain_append (start : Nat) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) :
    initialSourceCode (chainExps start expressions ++ program) =
      sourceCodeWithChain start expressions (initialSourceCode program) := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  simp [initialSourceCode, sourceCodeWithChain, HolFiniteMapExact.updateListEq,
    FUPDATE_LIST_HOL, List.foldl_append]

/-- Installed compiled entries and stubs connect the original source list to
the BVL entry point, subject to the existing compiler and oracle invariants. -/
theorem compiledProgram_sourceChain_semantics {C F : Type} (ffi : HolFfiState F)
    (maxApp sourceStart targetStart : Nat) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) (sourceOracle : ClosSem.CompileOracle C)
    (sourceCompiler : ClosSem.Compiler C) (targetCode : Spt (Nat × Bvl.Exp))
    (targetOracle : BvlSem.CompileOracle C) (targetCompiler : BvlSem.Compiler C)
    (nonempty : expressions ≠ [])
    (fresh : ∀ key, sourceStart ≤ key → key < sourceStart + expressions.length →
      (initialSourceCode program).lookup key = none)
    (ordered : Flapjack.Compiler.Backend.BackendProps.oracleMonotonic oracleCodeNames (· < ·)
      ({ key | sourceStart ≤ key ∧ key < sourceStart + expressions.length } ∪
        codeDomain (initialSourceCode program)) sourceOracle)
    (nonfail : ClosSem.semantics ffi maxApp (initialSourceCode program) sourceOracle sourceCompiler expressions ≠ .fail)
    (installed : codeInstalled (compileProgExpsHOL maxApp (chainExps sourceStart expressions ++ program)) targetCode)
    (locations : ∀ name arity body, (name, arity, body) ∈ chainExps sourceStart expressions ++ program →
      ClosProps.everyFnLocationSome [body])
    (varsAnnotated : ∀ name arity body, (name, arity, body) ∈ chainExps sourceStart expressions ++ program →
      ClosProps.everyFnVarsSome [body])
    (generic : ∀ n, n < maxApp → sptLookup (genericAppFnLocation n) targetCode =
      some (n + 2, generateGenericApp maxApp n))
    (partialStubs : ∀ total n, total < maxApp ∧ n < total →
      sptLookup (partialAppFnLocation maxApp total n) targetCode =
        some (total - n + 1, generatePartialAppClosureFn total n))
    (force : sptLookup (numStubs maxApp - 2) targetCode = some (2, forceThunkCode))
    (oracleInv : compileOracleInv maxApp (initialSourceCode (chainExps sourceStart expressions ++ program))
      sourceCompiler sourceOracle targetCode targetCompiler targetOracle)
    (entry : sptLookup targetStart targetCode = some (0, initGlobals maxApp (sourceStart + numStubs maxApp))) :
    BvlSem.semantics ffi targetCode targetOracle targetCompiler targetStart =
      ClosSem.semantics ffi maxApp (initialSourceCode program) sourceOracle sourceCompiler expressions := by
  have chainEq := sourceChain_semantics_eq ffi maxApp sourceStart (initialSourceCode program) sourceOracle sourceCompiler
    expressions nonempty fresh ordered nonfail
  have chainNonfail : ClosSem.semantics ffi maxApp (initialSourceCode (chainExps sourceStart expressions ++ program))
      sourceOracle sourceCompiler [.call .none 0 sourceStart []] ≠ .fail := by
    rw [initialSourceCode_chain_append, chainEq]
    exact nonfail
  have compiled := compiledProgram_entry_semantics ffi maxApp sourceStart targetStart
    (chainExps sourceStart expressions ++ program) sourceOracle sourceCompiler targetCode targetOracle targetCompiler
    chainNonfail installed locations varsAnnotated generic partialStubs force oracleInv entry
  rw [initialSourceCode_chain_append, chainEq] at compiled
  exact compiled

end Flapjack.Compiler.Backend.ClosToBvl

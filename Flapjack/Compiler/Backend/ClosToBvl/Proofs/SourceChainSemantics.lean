import Flapjack.Compiler.Backend.ClosToBvl.Proofs.SourceChain
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.StubCode
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.NumberAndAnnotate
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ChainEvaluation
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.AnnotationInvariants
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.NumberedPrepared

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

/-- The executable prepared compiler preserves source-list behavior when its
chained source program and emitted tree satisfy the stated invariants. -/
theorem compilePrepared_sourceChain_semantics {C F : Type} (ffi : HolFfiState F)
    (original current output : Config) (expressions nameExpressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString) (sourceOracle : ClosSem.CompileOracle C)
    (sourceCompiler : ClosSem.Compiler C) (targetOracle : BvlSem.CompileOracle C)
    (targetCompiler : BvlSem.Compiler C)
    (compile : compilePrepared? original current nameExpressions (chainExps current.start expressions ++ program) =
      some (output, compiled, names))
    (nonempty : expressions ≠ [])
    (fresh : ∀ key, current.start ≤ key → key < current.start + expressions.length →
      (initialSourceCode program).lookup key = none)
    (ordered : Flapjack.Compiler.Backend.BackendProps.oracleMonotonic oracleCodeNames (· < ·)
      ({ key | current.start ≤ key ∧ key < current.start + expressions.length } ∪
        codeDomain (initialSourceCode program)) sourceOracle)
    (nonfail : ClosSem.semantics ffi current.maxApp (initialSourceCode program) sourceOracle sourceCompiler expressions ≠ .fail)
    (distinct : (compiled.map Prod.fst).Nodup)
    (locations : ∀ name arity body, (name, arity, body) ∈ chainExps current.start expressions ++ program →
      ClosProps.everyFnLocationSome [body])
    (varsAnnotated : ∀ name arity body, (name, arity, body) ∈ chainExps current.start expressions ++ program →
      ClosProps.everyFnVarsSome [body])
    (oracleInv : compileOracleInv current.maxApp (initialSourceCode (chainExps current.start expressions ++ program))
      sourceCompiler sourceOracle (sptFromAList compiled) targetCompiler targetOracle) :
    BvlSem.semantics ffi (sptFromAList compiled) targetOracle targetCompiler output.start =
      ClosSem.semantics ffi current.maxApp (initialSourceCode program) sourceOracle sourceCompiler expressions := by
  have chainEq := sourceChain_semantics_eq ffi current.maxApp current.start (initialSourceCode program)
    sourceOracle sourceCompiler expressions nonempty fresh ordered nonfail
  have chainNonfail : ClosSem.semantics ffi current.maxApp
      (initialSourceCode (chainExps current.start expressions ++ program)) sourceOracle sourceCompiler
      [.call .none 0 current.start []] ≠ .fail := by
    rw [initialSourceCode_chain_append, chainEq]
    exact nonfail
  have compiledEq := compilePrepared_tree_semantics ffi original current output nameExpressions
    (chainExps current.start expressions ++ program) compiled names sourceOracle sourceCompiler targetOracle targetCompiler
    compile chainNonfail distinct locations varsAnnotated oracleInv
  rw [initialSourceCode_chain_append, chainEq] at compiledEq
  exact compiledEq

/-- Numbering, annotation, chaining and the prepared closure compiler
preserve the source batch's behavior when the generated code and oracle
invariants hold. This is conditional proof-side composition. -/
theorem compilePrepared_numbered_source_semantics {C F : Type} (ffi : HolFfiState F)
    (original current output : Config) (number : Nat) (program : List ClosLang.Exp)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : ClosSem.CompileOracle (Nat × C)) (targetCompiler : BvlSem.Compiler C)
    (targetOracle : BvlSem.CompileOracle C)
    (nonempty : program ≠ [])
    (notFail : ClosSem.semantics ffi current.maxApp HolFiniteMapExact.empty oracle
      (BackendProps.stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (BackendProps.pureCc ClosAnnotate.compileInc (BackendProps.pureCc (compileInc current.maxApp) targetCompiler))) program ≠ .fail)
    (numberSafe : ¬ ClosProps.containsAppSome current.maxApp program)
    (varsSafe : ClosProps.everyFnVarsNone program)
    (oracleSafe : ∀ index, (oracle index).2.2 = [] ∧
      ¬ ClosProps.containsAppSome current.maxApp (oracle index).2.1 ∧ ClosProps.everyFnVarsNone (oracle index).2.1)
    (compile : let annotated := (extractName (ClosAnnotate.compileInc ((ClosNumber.compileInc number program).2, [])).1).2
      compilePrepared? original current program (chainExps current.start annotated) = some (output, compiled, names))
    (ordered : let annotated := (extractName (ClosAnnotate.compileInc ((ClosNumber.compileInc number program).2, [])).1).2
      BackendProps.oracleMonotonic oracleCodeNames (· < ·)
        ({ key | current.start ≤ key ∧ key < current.start + annotated.length } ∪ codeDomain HolFiniteMapExact.empty)
        (BackendProps.pureCo ClosAnnotate.compileInc ∘ BackendProps.stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle))
    (distinct : (compiled.map Prod.fst).Nodup)
    (oracleInv : let annotated := (extractName (ClosAnnotate.compileInc ((ClosNumber.compileInc number program).2, [])).1).2
      compileOracleInv current.maxApp (initialSourceCode (chainExps current.start annotated))
        (BackendProps.pureCc (compileInc current.maxApp) targetCompiler)
        (BackendProps.pureCo ClosAnnotate.compileInc ∘ BackendProps.stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
        (sptFromAList compiled) targetCompiler targetOracle) :
    BvlSem.semantics ffi (sptFromAList compiled) targetOracle targetCompiler output.start =
      ClosSem.semantics ffi current.maxApp HolFiniteMapExact.empty oracle
        (BackendProps.stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
          (BackendProps.pureCc ClosAnnotate.compileInc (BackendProps.pureCc (compileInc current.maxApp) targetCompiler))) program := by
  let annotated := (extractName (ClosAnnotate.compileInc ((ClosNumber.compileInc number program).2, [])).1).2
  let sourceOracle := BackendProps.pureCo ClosAnnotate.compileInc ∘ BackendProps.stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
  let sourceCompiler := BackendProps.pureCc (compileInc current.maxApp) targetCompiler
  have annotatedEq := incremental_number_annotate_semantics ffi current.maxApp number oracle sourceCompiler program
    nonempty notFail numberSafe varsSafe oracleSafe
  have annotatedShape : annotated = ClosAnnotate.annotateList 0 (ClosNumber.renumberList
      (let next := number + max program.length 1; if next % 2 = 0 then next else next + 1) program).2 := by
    have extraction := extract_numbered_annotated number program
    dsimp only at extraction
    simp only [List.isEmpty_iff, nonempty, ↓reduceIte] at extraction
    exact congrArg Prod.snd extraction
  have annotatedNonempty : annotated ≠ [] := by
    intro empty
    have len := ClosAnnotate.annotateList_length 0 (ClosNumber.renumberList
      (let next := number + max program.length 1; if next % 2 = 0 then next else next + 1) program).2
    rw [← annotatedShape, empty] at len
    have : program.length = 0 := by simpa [ClosNumber.renumberList_length] using len.symm
    exact nonempty (List.eq_nil_of_length_eq_zero this)
  have annotatedLocations : ClosProps.everyFnLocationSome annotated := by
    rw [annotatedShape]
    exact ClosAnnotate.annotateList_locations 0 _ (ClosNumber.renumberList_locations _ _)
  have annotatedVars : ClosProps.everyFnVarsSome annotated := by
    rw [annotatedShape]
    exact ClosAnnotate.annotateList_varsSome 0 _
  have chainLocations := (chainExps_annotations current.start annotated).1.mpr annotatedLocations
  have chainVars := (chainExps_annotations current.start annotated).2.mpr annotatedVars
  have locations : ∀ name arity body, (name, arity, body) ∈ chainExps current.start annotated →
      ClosProps.everyFnLocationSome [body] := by
    intro name arity body member
    apply ClosNumber.locations_member _ _ chainLocations
    exact List.mem_map.mpr ⟨(name, arity, body), member, rfl⟩
  have varsAnnotated : ∀ name arity body, (name, arity, body) ∈ chainExps current.start annotated →
      ClosProps.everyFnVarsSome [body] := by
    intro name arity body member
    have bodyMember : body ∈ (chainExps current.start annotated).map (fun (_, _, exp) => exp) :=
      List.mem_map.mpr ⟨(name, arity, body), member, rfl⟩
    have memberVars : ∀ (bodies : List ClosLang.Exp) (body : ClosLang.Exp),
        ClosProps.everyFnVarsSome bodies → body ∈ bodies → ClosProps.everyFnVarsSome [body] := by
      intro bodies body all member
      induction bodies with
      | nil => simp at member
      | cons first rest ih =>
        simp only [ClosProps.everyFnVarsSome] at all
        simp only [List.mem_cons] at member
        cases member with
        | inl same => subst body; simpa [ClosProps.everyFnVarsSome] using all.1
        | inr tail => exact ih all.2 tail
    exact memberVars _ _ chainVars bodyMember
  have annotatedNonfail : ClosSem.semantics ffi current.maxApp HolFiniteMapExact.empty sourceOracle sourceCompiler annotated ≠ .fail := by
    rw [annotatedEq]
    exact notFail
  have emptyCode : initialSourceCode [] = HolFiniteMapExact.empty := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    simp [initialSourceCode, HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL]
  have result := compilePrepared_sourceChain_semantics ffi original current output annotated program [] compiled names
    sourceOracle sourceCompiler targetOracle targetCompiler (by simpa [annotated] using compile) annotatedNonempty
    (by intro key _ _; simp [emptyCode, HolFiniteMapExact.empty]) (by simpa [emptyCode, sourceOracle, annotated] using ordered)
    (by simpa [emptyCode] using annotatedNonfail) distinct (by simpa using locations)
    (by simpa using varsAnnotated) (by simpa [annotated, sourceOracle, sourceCompiler] using oracleInv)
  rw [emptyCode] at result
  exact result.trans annotatedEq

/-- The numbered and annotated future oracle has annotated source bodies;
numbering supplies the locations and annotation supplies the variable sets. -/
theorem numberedOracle_locations {C : Type} (oracle : ClosSem.CompileOracle (Nat × C))
    (emptyAux : ∀ index, (oracle index).2.2 = []) :
    ∀ index,
      let entry := (BackendProps.stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle index).2
      ClosProps.everyFnLocationSome entry.1 ∧
        ∀ item ∈ entry.2, ClosProps.everyFnLocationSome [item.2.2] := by
  intro index
  constructor
  · simpa [BackendProps.stateCo, ClosNumber.ignoreTable] using
      ClosNumber.compileInc_locations (oracle index).1.1 (oracle index).2.1
  · simp [BackendProps.stateCo, ClosNumber.ignoreTable, emptyAux index]

/-- Ordered intervals and distinct future labels establish the compiler-oracle
invariant for the composed numbering, annotation and BVL passes. -/
theorem numbered_compileOracleInv_of_boundaries {C : Type} (maxApp : Nat)
    (sourceCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (oracle : ClosSem.CompileOracle (Nat × C)) (targetCode : Spt (Nat × Bvl.Exp))
    (targetCompiler : BvlSem.Compiler C) (boundary : Nat → Nat)
    (emptyAux : ∀ index, (oracle index).2.2 = [])
    (monotone : ∀ {i j}, i ≤ j → boundary i ≤ boundary j)
    (initialBelow : ∀ location, sptMem location targetCode → location < boundary 0)
    (distinct : ∀ index, ((compileInc maxApp (ClosAnnotate.compileInc
      ((BackendProps.stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle index).2))).map Prod.fst).Nodup)
    (ranges : ∀ index location, location ∈ (compileInc maxApp (ClosAnnotate.compileInc
      ((BackendProps.stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle index).2))).map Prod.fst →
      boundary index ≤ location ∧ location < boundary (index + 1)) :
    compileOracleInv maxApp sourceCode (BackendProps.pureCc (compileInc maxApp) targetCompiler)
      (BackendProps.pureCo ClosAnnotate.compileInc ∘ BackendProps.stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
      targetCode targetCompiler
      (BackendProps.pureCo (compileInc maxApp) ∘ BackendProps.pureCo ClosAnnotate.compileInc ∘
        BackendProps.stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) := by
  exact compileOracleInv_of_annotated_boundaries maxApp sourceCode
    (BackendProps.stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) targetCode targetCompiler boundary
    monotone initialBelow distinct ranges (numberedOracle_locations oracle emptyAux)

/-- Behavior preservation with the compiler-oracle invariant derived from
future label intervals. The source-chain ordering and target intervals remain
explicit until they are derived from the compilation configuration. -/
theorem compilePrepared_numbered_source_semantics_of_boundaries {C F : Type} (ffi : HolFfiState F)
    (original current output : Config) (number : Nat) (program : List ClosLang.Exp)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : ClosSem.CompileOracle (Nat × C)) (targetCompiler : BvlSem.Compiler C) (boundary : Nat → Nat)
    (nonempty : program ≠ [])
    (notFail : ClosSem.semantics ffi current.maxApp HolFiniteMapExact.empty oracle
      (BackendProps.stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (BackendProps.pureCc ClosAnnotate.compileInc (BackendProps.pureCc (compileInc current.maxApp) targetCompiler))) program ≠ .fail)
    (numberSafe : ¬ ClosProps.containsAppSome current.maxApp program)
    (varsSafe : ClosProps.everyFnVarsNone program)
    (oracleSafe : ∀ index, (oracle index).2.2 = [] ∧
      ¬ ClosProps.containsAppSome current.maxApp (oracle index).2.1 ∧ ClosProps.everyFnVarsNone (oracle index).2.1)
    (compile : let annotated := (extractName (ClosAnnotate.compileInc ((ClosNumber.compileInc number program).2, [])).1).2
      compilePrepared? original current program (chainExps current.start annotated) = some (output, compiled, names))
    (ordered : let annotated := (extractName (ClosAnnotate.compileInc ((ClosNumber.compileInc number program).2, [])).1).2
      BackendProps.oracleMonotonic oracleCodeNames (· < ·)
        ({ key | current.start ≤ key ∧ key < current.start + annotated.length } ∪ codeDomain HolFiniteMapExact.empty)
        (BackendProps.pureCo ClosAnnotate.compileInc ∘ BackendProps.stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle))
    (distinct : (compiled.map Prod.fst).Nodup)
    (monotone : ∀ {i j}, i ≤ j → boundary i ≤ boundary j)
    (initialBelow : ∀ location ∈ compiled.map Prod.fst, location < boundary 0)
    (ranges : ∀ index location, location ∈ (compileInc current.maxApp (ClosAnnotate.compileInc
      ((BackendProps.stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle index).2))).map Prod.fst →
      boundary index ≤ location ∧ location < boundary (index + 1)) :
    BvlSem.semantics ffi (sptFromAList compiled)
      (BackendProps.pureCo (compileInc current.maxApp) ∘ BackendProps.pureCo ClosAnnotate.compileInc ∘
        BackendProps.stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) targetCompiler output.start =
      ClosSem.semantics ffi current.maxApp HolFiniteMapExact.empty oracle
        (BackendProps.stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
          (BackendProps.pureCc ClosAnnotate.compileInc (BackendProps.pureCc (compileInc current.maxApp) targetCompiler))) program := by
  apply compilePrepared_numbered_source_semantics ffi original current output number program compiled names oracle
    targetCompiler _ nonempty notFail numberSafe varsSafe oracleSafe compile ordered distinct
  dsimp only
  apply numbered_compileOracleInv_of_boundaries current.maxApp _ oracle _ targetCompiler boundary
    (fun index => (oracleSafe index).1) monotone
  · intro location member
    exact initialBelow location (emitted_tree_location_mem compiled location member)
  · intro index
    have distinctFuture := numberedAnnotatedOracle_labels_nodup_emptyAux current.maxApp oracle
      (fun i => (oracleSafe i).1) index
    simpa [BackendProps.pureCo, Function.comp_def] using distinctFuture
  · exact ranges

/-- Consistent numbering-oracle states supply the future intervals and
source-chain ordering when the original oracle carries no auxiliary code. -/
theorem compilePrepared_numbered_source_semantics_of_stateOracle {C F : Type} (ffi : HolFfiState F)
    (original current output : Config) (number : Nat) (program : List ClosLang.Exp)
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : ClosSem.CompileOracle (Nat × C)) (targetCompiler : BvlSem.Compiler C)
    (nonempty : program ≠ [])
    (notFail : ClosSem.semantics ffi current.maxApp HolFiniteMapExact.empty oracle
      (BackendProps.stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (BackendProps.pureCc ClosAnnotate.compileInc (BackendProps.pureCc (compileInc current.maxApp) targetCompiler))) program ≠ .fail)
    (numberSafe : ¬ ClosProps.containsAppSome current.maxApp program)
    (varsSafe : ClosProps.everyFnVarsNone program)
    (oracleSafe : ∀ index, (oracle index).2.2 = [] ∧
      ¬ ClosProps.containsAppSome current.maxApp (oracle index).2.1 ∧ ClosProps.everyFnVarsNone (oracle index).2.1)
    (compile : let annotated := (extractName (ClosAnnotate.compileInc ((ClosNumber.compileInc number program).2, [])).1).2
      compilePrepared? original current program (chainExps current.start annotated) = some (output, compiled, names))
    (distinct : (compiled.map Prod.fst).Nodup)
    (oracleState : BackendProps.isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (initialBelow : ∀ location ∈ compiled.map Prod.fst, location < (oracle 0).1.1 + numStubs current.maxApp) :
    BvlSem.semantics ffi (sptFromAList compiled)
      (BackendProps.pureCo (compileInc current.maxApp) ∘ BackendProps.pureCo ClosAnnotate.compileInc ∘
        BackendProps.stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) targetCompiler output.start =
      ClosSem.semantics ffi current.maxApp HolFiniteMapExact.empty oracle
        (BackendProps.stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
          (BackendProps.pureCc ClosAnnotate.compileInc (BackendProps.pureCc (compileInc current.maxApp) targetCompiler))) program := by
  apply compilePrepared_numbered_source_semantics_of_boundaries ffi original current output number program compiled names
    oracle targetCompiler (fun i => (oracle i).1.1 + numStubs current.maxApp)
    nonempty notFail numberSafe varsSafe oracleSafe compile ?_ distinct ?_ initialBelow
  · intro index location member
    have bound := numberedAnnotatedOracle_labels_range current.maxApp oracle oracleState
      (by intro i entry member; simp [(oracleSafe i).1] at member) index location
      (by simpa [BackendProps.pureCo, Function.comp_def] using member)
    exact bound
  · dsimp only
    constructor <;> intro i
    · intro j x y _ member _
      simp [oracleCodeNames, BackendProps.pureCo, BackendProps.stateCo,
        ClosNumber.ignoreTable, ClosAnnotate.compileInc, ClosAnnotate.compile, (oracleSafe i).1] at member
    · intro x y _ member
      simp [oracleCodeNames, BackendProps.pureCo, BackendProps.stateCo,
        ClosNumber.ignoreTable, ClosAnnotate.compileInc, ClosAnnotate.compile, (oracleSafe i).1] at member
  · intro i j order
    have h := numberingOracle_state_monotone oracle oracleState order
    omega

end Flapjack.Compiler.Backend.ClosToBvl

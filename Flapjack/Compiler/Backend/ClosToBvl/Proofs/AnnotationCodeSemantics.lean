import Flapjack.Compiler.Backend.ClosToBvl.Proofs.SourceChainSemantics
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.SemanticsCorrect

/-! Annotation of installed closure programs and their observable behavior. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps

/-- Annotating every association-list entry preserves its first-match lookup,
including when the source program contains duplicate labels. -/
theorem initialSourceCode_compile (program : List (Nat × Nat × ClosLang.Exp)) :
    initialSourceCode (ClosAnnotate.compile program) =
      (initialSourceCode program).map2 (fun entry => (entry.2.1, ClosAnnotate.annotateSing entry.2.1 entry.2.2)) := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  induction program with
  | nil => simp [ClosAnnotate.compile, initialSourceCode, HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL]
  | cons first rest ih =>
    obtain ⟨name, arity, body⟩ := first
    simp only [ClosAnnotate.compile, List.map_cons]
    simp only [HolFiniteMapExact.lookup_map2]
    rw [initialSourceCode_cons_lookup, initialSourceCode_cons_lookup]
    by_cases same : key = name
    · simp [same]
    · simp only [same, ↓reduceIte]
      simpa [ClosAnnotate.compile] using ih

/-- A source association-list map and its annotated counterpart satisfy the
annotation state relation at every initial clock. -/
theorem initialState_annotated_code_related {C F : Type} (ffi : HolFfiState F) (maxApp clock : Nat)
    (program : List (Nat × Nat × ClosLang.Exp)) (oracle : CompileOracle C) (compiler : Compiler C) :
    ClosAnnotate.StateRel
      (initialState ffi maxApp (initialSourceCode program) oracle (pureCc ClosAnnotate.compileInc compiler) clock)
      (initialState ffi maxApp (initialSourceCode (ClosAnnotate.compile program))
        (pureCo ClosAnnotate.compileInc ∘ oracle) compiler clock) := by
  simp only [ClosAnnotate.StateRel, initialState, true_and, List.Forall₂.nil]
  constructor
  · intro key
    simp [ClosAnnotate.OptionRel, HolFiniteMapExact.empty]
  · intro key
    rw [initialSourceCode_compile]
    simp only [HolFiniteMapExact.lookup_map2]
    cases h : (initialSourceCode program).lookup key with
    | none => simp [ClosAnnotate.OptionRel]
    | some value =>
      obtain ⟨arity, body⟩ := value
      simp [ClosAnnotate.OptionRel, ClosAnnotate.CodeRel]

/-- Every installed source body is annotation-safe when the association-list
bodies are safe. -/
theorem initialSourceCode_annotationSafe {C F : Type} (ffi : HolFfiState F) (maxApp clock : Nat)
    (program : List (Nat × Nat × ClosLang.Exp)) (oracle : CompileOracle C) (compiler : Compiler C)
    (safe : ∀ name arity body, (name, arity, body) ∈ program → everyFnVarsNone [body]) :
    ClosAnnotate.CodeSafe (initialState ffi maxApp (initialSourceCode program) oracle compiler clock) := by
  intro name arity body lookup
  exact safe name arity body (initialSourceCode_lookup_mem program name arity body lookup)

/-- Annotation preserves observable behavior with an installed source program,
under the evaluator's annotation-safety conditions. -/
theorem annotation_installed_semantics {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : List (Nat × Nat × ClosLang.Exp)) (oracle : CompileOracle C) (compiler : Compiler C)
    (program : List ClosLang.Exp) (safe : everyFnVarsNone program)
    (codeSafe : ∀ name arity body, (name, arity, body) ∈ code → everyFnVarsNone [body])
    (oracleSafe : ∀ n, everyFnVarsNone (oracle n).2.1 ∧
      everyFnVarsNone ((oracle n).2.2.map (fun (_, _, body) => body)))
    (nonfail : semantics ffi maxApp (initialSourceCode code) oracle (pureCc ClosAnnotate.compileInc compiler) program ≠ .fail) :
    semantics ffi maxApp (initialSourceCode code) oracle (pureCc ClosAnnotate.compileInc compiler) program =
      semantics ffi maxApp (initialSourceCode (ClosAnnotate.compile code))
        (pureCo ClosAnnotate.compileInc ∘ oracle) compiler (ClosAnnotate.annotateList 0 program) := by
  apply ClosAnnotate.semantics_eq_of_related
  intro clock
  let source := initialState ffi maxApp (initialSourceCode code) oracle (pureCc ClosAnnotate.compileInc compiler) clock
  let target := initialState ffi maxApp (initialSourceCode (ClosAnnotate.compile code))
    (pureCo ClosAnnotate.compileInc ∘ oracle) compiler clock
  let outcome := evaluate program [] source
  have noType : outcome.1 ≠ .err (.abort .typeError) := by
    exact (semantics_ne_fail_iff ffi maxApp (initialSourceCode code) oracle
      (pureCc ClosAnnotate.compileInc compiler) program).mp nonfail clock
  obtain ⟨targetResult, targetNext, targetRun, results, nextRel⟩ :=
    ClosAnnotate.annotate_correct program source target [] outcome.1 outcome.2 (by exact Prod.eta _) noType safe
      (initialSourceCode_annotationSafe ffi maxApp clock code oracle (pureCc ClosAnnotate.compileInc compiler) codeSafe)
      oracleSafe (initialState_annotated_code_related ffi maxApp clock code oracle compiler)
  rw [targetRun]
  exact ⟨results, nextRel.2.1⟩

/-- Chaining preserves the absence of variable annotations in closure bodies. -/
theorem chainExps_varsNone (start : Nat) (expressions : List ClosLang.Exp) :
    everyFnVarsNone ((chainExps start expressions).map (fun (_, _, body) => body)) ↔
      everyFnVarsNone expressions := by
  induction expressions generalizing start with
  | nil => simp [chainExps, everyFnVarsNone, fnVarsNoneExp]
  | cons first rest ih =>
    cases rest with
    | nil => simp [chainExps, everyFnVarsNone]
    | cons second tail =>
      have step := ih (start + 1)
      simp [chainExps, everyFnVarsNone, fnVarsNoneExp, step]

/-- Executing an installed chain before and after annotating its entries has
the same observable behavior for a non-failing program. -/
theorem annotation_chain_call_semantics {C F : Type} (ffi : HolFfiState F) (maxApp start : Nat)
    (expressions : List ClosLang.Exp) (oracle : CompileOracle C) (compiler : Compiler C)
    (safe : everyFnVarsNone expressions)
    (oracleSafe : ∀ n, everyFnVarsNone (oracle n).2.1 ∧
      everyFnVarsNone ((oracle n).2.2.map (fun (_, _, body) => body)))
    (nonfail : semantics ffi maxApp (initialSourceCode (chainExps start expressions)) oracle
      (pureCc ClosAnnotate.compileInc compiler) [.call .none 0 start []] ≠ .fail) :
    semantics ffi maxApp (initialSourceCode (chainExps start expressions)) oracle
      (pureCc ClosAnnotate.compileInc compiler) [.call .none 0 start []] =
      semantics ffi maxApp (initialSourceCode (ClosAnnotate.compile (chainExps start expressions)))
        (pureCo ClosAnnotate.compileInc ∘ oracle) compiler [.call .none 0 start []] := by
  have chainSafe := (chainExps_varsNone start expressions).mpr safe
  have memberSafe : ∀ (bodies : List ClosLang.Exp) (body : ClosLang.Exp),
      everyFnVarsNone bodies → body ∈ bodies → everyFnVarsNone [body] := by
    intro bodies body all member
    induction bodies with
    | nil => simp at member
    | cons first rest ih =>
      simp only [everyFnVarsNone] at all
      simp only [List.mem_cons] at member
      cases member with
      | inl same => subst body; simpa [everyFnVarsNone] using all.1
      | inr tail => exact ih all.2 tail
  have codeSafe : ∀ name arity body, (name, arity, body) ∈ chainExps start expressions →
      everyFnVarsNone [body] := by
    intro name arity body member
    exact memberSafe _ body chainSafe (List.mem_map.mpr ⟨(name, arity, body), member, rfl⟩)
  have eq := annotation_installed_semantics ffi maxApp (chainExps start expressions) oracle compiler
    [.call .none 0 start []] (by simp [everyFnVarsNone, fnVarsNoneExp]) codeSafe oracleSafe nonfail
  simpa [ClosAnnotate.annotateList, ClosAnnotate.altFreeList, ClosAnnotate.altFreeSing,
    ClosAnnotate.shiftList, ClosAnnotate.shiftSing] using eq

/-- For a nonempty source batch, annotating the installed chain after its
construction preserves source behavior. This matches the order used by the
no-optimization closure compiler. -/
theorem source_to_annotatedChain_semantics {C F : Type} (ffi : HolFfiState F) (maxApp start : Nat)
    (expressions : List ClosLang.Exp) (oracle : CompileOracle C) (compiler : Compiler C)
    (nonempty : expressions ≠ []) (safe : everyFnVarsNone expressions)
    (oracleSafe : ∀ n, everyFnVarsNone (oracle n).2.1 ∧
      everyFnVarsNone ((oracle n).2.2.map (fun (_, _, body) => body)))
    (emptyAux : ∀ n, (oracle n).2.2 = [])
    (nonfail : semantics ffi maxApp HolFiniteMapExact.empty oracle
      (pureCc ClosAnnotate.compileInc compiler) expressions ≠ .fail) :
    semantics ffi maxApp (initialSourceCode (ClosAnnotate.compile (chainExps start expressions)))
        (pureCo ClosAnnotate.compileInc ∘ oracle) compiler [.call .none 0 start []] =
      semantics ffi maxApp HolFiniteMapExact.empty oracle (pureCc ClosAnnotate.compileInc compiler) expressions := by
  have emptyCode : initialSourceCode [] = HolFiniteMapExact.empty := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    simp [initialSourceCode, HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL]
  have ordered : oracleMonotonic oracleCodeNames (· < ·)
      ({ key | start ≤ key ∧ key < start + expressions.length } ∪ codeDomain HolFiniteMapExact.empty) oracle := by
    constructor <;> intro i
    · intro j x y _ member _
      simp [oracleCodeNames, emptyAux i] at member
    · intro x y _ member
      simp [oracleCodeNames, emptyAux i] at member
  have chainEq := sourceChain_semantics_eq ffi maxApp start HolFiniteMapExact.empty oracle
    (pureCc ClosAnnotate.compileInc compiler) expressions nonempty
    (by intro key _ _; simp [HolFiniteMapExact.empty]) ordered nonfail
  have mapEq : initialSourceCode (chainExps start expressions) =
      sourceCodeWithChain start expressions HolFiniteMapExact.empty := by
    simpa [emptyCode] using initialSourceCode_chain_append start expressions []
  have chainNonfail : semantics ffi maxApp (initialSourceCode (chainExps start expressions)) oracle
      (pureCc ClosAnnotate.compileInc compiler) [.call .none 0 start []] ≠ .fail := by
    rw [mapEq, chainEq]
    exact nonfail
  have annotationEq := annotation_chain_call_semantics ffi maxApp start expressions oracle compiler safe oracleSafe chainNonfail
  rw [mapEq, chainEq] at annotationEq
  exact annotationEq.symm

/-- Multi-argument introduction and numbering followed by construction and
annotation of the installed chain preserve the current Lean observations.
This is the production ordering before closure-to-BVL lowering when the
known-function and direct-call optimizations are disabled; the proof is not a
reviewed HOL correspondence. -/
theorem mti_number_annotatedChain_semantics {C F : Type} (ffi : HolFfiState F)
    (fuel maxApp number start : Nat) (expressions : List ClosLang.Exp)
    (oracle : CompileOracle (Nat × C)) (compiler : Compiler C)
    (positive : 1 ≤ maxApp) (nonempty : expressions ≠ [])
    (unary : ∀ e ∈ expressions, noMti e)
    (oracleUnary : ∀ index, (oracle index).2.2 = [] ∧
      ∀ e ∈ (oracle index).2.1, noMti e)
    (nonfail : semantics ffi maxApp HolFiniteMapExact.empty oracle
      (pureCc (ClosMti.compileInc maxApp)
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc compiler)))
      expressions ≠ .fail) :
    ∃ transformed, ClosMti.compileFuel fuel true maxApp expressions = some transformed ∧
      semantics ffi maxApp
        (initialSourceCode (ClosAnnotate.compile (chainExps start (ClosNumber.renumberList number transformed).2)))
        (pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
          (pureCo (ClosMti.compileInc maxApp) ∘ oracle)) compiler [.call .none 0 start []] =
      semantics ffi maxApp HolFiniteMapExact.empty oracle
        (pureCc (ClosMti.compileInc maxApp)
          (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc ClosAnnotate.compileInc compiler)))
        expressions := by
  let transformed := ClosMti.introList maxApp expressions
  let transformedOracle : CompileOracle (Nat × C) := pureCo (ClosMti.compileInc maxApp) ∘ oracle
  let numbered := (ClosNumber.renumberList number transformed).2
  let numberedOracle := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) transformedOracle
  have numberedEq := ClosNumber.semantics_mti_then_number ffi maxApp number oracle
    (pureCc ClosAnnotate.compileInc compiler) expressions positive unary oracleUnary nonfail
  have transformedVars : everyFnVarsNone transformed :=
    (ClosMti.introList_varsNone maxApp expressions).mp (noMtiList_syntactic maxApp positive expressions unary).1
  have numberedVars : everyFnVarsNone numbered :=
    (ClosNumber.renumberList_varsNone transformed number).mpr transformedVars
  have numberedNonempty : numbered ≠ [] := by
    intro empty
    have len := ClosNumber.renumberList_length transformed number
    change numbered.length = transformed.length at len
    rw [empty] at len
    have originalLength : transformed.length = expressions.length := ClosMti.introList_length maxApp expressions
    exact nonempty (List.eq_nil_of_length_eq_zero (by simpa [← originalLength] using len.symm))
  have transformedOracleSafe : ∀ index, (transformedOracle index).2.2 = [] ∧
      everyFnVarsNone (transformedOracle index).2.1 := by
    intro index
    change (ClosMti.compileInc maxApp (oracle index).2).2 = [] ∧
      everyFnVarsNone (ClosMti.compileInc maxApp (oracle index).2).1
    exact ⟨rfl, (ClosMti.introList_varsNone maxApp _).mp
      (noMtiList_syntactic maxApp positive _ (oracleUnary index).2).1⟩
  have numberedOracleSafe : ∀ index, everyFnVarsNone (numberedOracle index).2.1 ∧
      everyFnVarsNone ((numberedOracle index).2.2.map (fun (_, _, body) => body)) := by
    intro index
    constructor
    · simpa [numberedOracle, stateCo, ClosNumber.ignoreTable, ClosNumber.compileInc_varsNone] using
        (transformedOracleSafe index).2
    · simp [numberedOracle, stateCo, ClosNumber.ignoreTable, (transformedOracleSafe index).1, everyFnVarsNone]
  have numberedAux : ∀ index, (numberedOracle index).2.2 = [] := by
    intro index
    simpa [numberedOracle, stateCo, ClosNumber.ignoreTable] using (transformedOracleSafe index).1
  have numberedNonfail : semantics ffi maxApp HolFiniteMapExact.empty numberedOracle
      (pureCc ClosAnnotate.compileInc compiler) numbered ≠ .fail := by
    simpa [numberedOracle, transformedOracle, numbered, transformed, ← numberedEq] using nonfail
  have chainEq := source_to_annotatedChain_semantics ffi maxApp start numbered numberedOracle compiler
    numberedNonempty numberedVars numberedOracleSafe numberedAux numberedNonfail
  refine ⟨transformed, ClosMti.compileFuel_introList fuel maxApp expressions, ?_⟩
  exact chainEq.trans numberedEq

/-- The no-optimization compiler preserves a nonempty source batch through
numbering, chain construction, annotation and BVL conversion, assuming a
consistent future oracle and a bound on its first numbering state. -/
theorem compileNoOpts_source_semantics_nonempty {C F : Type} (ffi : HolFfiState F)
    (config current output : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : ClosSem.CompileOracle (Nat × C)) (targetCompiler : BvlSem.Compiler C)
    (preprocess : compileCommonNoOpts? config expressions = some (current, program))
    (compile : compileNoOpts? config expressions = some (output, compiled, names))
    (nonempty : expressions ≠ [])
    (nonfail : semantics ffi config.maxApp HolFiniteMapExact.empty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc ClosAnnotate.compileInc (pureCc (compileInc config.maxApp) targetCompiler))) expressions ≠ .fail)
    (numberSafe : ¬ containsAppSome config.maxApp expressions) (varsSafe : everyFnVarsNone expressions)
    (oracleSafe : ∀ index, (oracle index).2.2 = [] ∧
      ¬ containsAppSome config.maxApp (oracle index).2.1 ∧ everyFnVarsNone (oracle index).2.1)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (initialBound : current.nextLoc ≤ (oracle 0).1.1) :
    BvlSem.semantics ffi (sptFromAList compiled)
      (pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
        stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) targetCompiler output.start =
      semantics ffi config.maxApp HolFiniteMapExact.empty oracle
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
          (pureCc ClosAnnotate.compileInc (pureCc (compileInc config.maxApp) targetCompiler))) expressions := by
  by_cases enabled : config.doMti || config.doCall
  · simp [compileCommonNoOpts?, enabled] at preprocess
  · cases known : config.knownConf with
    | some k => simp [compileCommonNoOpts?, enabled, known] at preprocess
    | none =>
      let next := config.nextLoc + max 1 expressions.length
      let aligned := if next % 2 = 0 then next else next + 1
      cases numbered : ClosNumber.renumberList aligned expressions with
      | mk nextLoc numberedExpressions =>
        have run : compileCommonNoOpts? config expressions =
            some ({ config with start := config.nextLoc, nextLoc := nextLoc, knownConf := none, callState := (.ln, []) },
              ClosAnnotate.compile (chainExps config.nextLoc numberedExpressions)) := by
          simp [compileCommonNoOpts?, enabled, known, next, aligned, numbered]
        have equal := Option.some.inj (preprocess.symm.trans run)
        cases equal
        let numberedOracle := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
        let compiler := pureCc (compileInc config.maxApp) targetCompiler
        have numberedEq := ClosNumber.semantics_number ffi config.maxApp aligned oracle
          (pureCc ClosAnnotate.compileInc compiler) expressions nonfail numberSafe
          (fun i => ⟨(oracleSafe i).1, (oracleSafe i).2.1⟩)
        simp only [numbered] at numberedEq
        have numberedNonempty : numberedExpressions ≠ [] := by
          intro empty
          have len := ClosNumber.renumberList_length expressions aligned
          rw [numbered, empty] at len
          exact nonempty (List.eq_nil_of_length_eq_zero (by simpa using len.symm))
        have numberedVars : everyFnVarsNone numberedExpressions := by
          have h := (ClosNumber.renumberList_varsNone expressions aligned).mpr varsSafe
          simpa [numbered] using h
        have numberedOracleSafe : ∀ index, everyFnVarsNone (numberedOracle index).2.1 ∧
            everyFnVarsNone ((numberedOracle index).2.2.map (fun (_, _, body) => body)) := by
          intro index
          constructor
          · simpa [numberedOracle, stateCo, ClosNumber.ignoreTable, ClosNumber.compileInc_varsNone] using (oracleSafe index).2.2
          · simp [numberedOracle, stateCo, ClosNumber.ignoreTable, (oracleSafe index).1, everyFnVarsNone]
        have numberedAux : ∀ index, (numberedOracle index).2.2 = [] := by
          intro index
          simpa [numberedOracle, stateCo, ClosNumber.ignoreTable] using (oracleSafe index).1
        have numberedNonfail : semantics ffi config.maxApp HolFiniteMapExact.empty numberedOracle
            (pureCc ClosAnnotate.compileInc compiler) numberedExpressions ≠ .fail := by
          rw [numberedEq]
          exact nonfail
        have chainEq := source_to_annotatedChain_semantics ffi config.maxApp config.nextLoc numberedExpressions
          numberedOracle compiler numberedNonempty numberedVars numberedOracleSafe numberedAux numberedNonfail
        have chainNonfail : semantics ffi config.maxApp
            (initialSourceCode (ClosAnnotate.compile (chainExps config.nextLoc numberedExpressions)))
            (pureCo ClosAnnotate.compileInc ∘ numberedOracle) compiler [.call .none 0 config.nextLoc []] ≠ .fail := by
          rw [chainEq, numberedEq]
          exact nonfail
        have compiledEq := compileNoOpts_numberedOracle_semantics ffi config _ output expressions _ compiled names
          oracle targetCompiler run compile chainNonfail oracleState initialBound
          (by intro i; simp [(oracleSafe i).1, ClosProps.codeLocations])
          (by intro i label member; simp [(oracleSafe i).1, ClosProps.codeLocations] at member)
          (by intro i label inMain inAux; simp [(oracleSafe i).1, ClosProps.codeLocations] at inAux)
          (by intro i entry member; simp [(oracleSafe i).1] at member)
          (by intro i entry member; simp [(oracleSafe i).1] at member)
        exact compiledEq.trans (chainEq.trans numberedEq)

/-- The generated entry for an empty batch returns a constant once its
entry-call clock has been paid. -/
theorem emptyAnnotatedChain_run {C F : Type} (ffi : HolFfiState F) (maxApp start clock : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C) :
    evaluate [.call .none 0 start []] []
      (initialState ffi maxApp (initialSourceCode (ClosAnnotate.compile (chainExps start []))) oracle compiler (clock + 1)) =
      (.val [.number 0], initialState ffi maxApp (initialSourceCode (ClosAnnotate.compile (chainExps start []))) oracle compiler clock) := by
  simp [ClosAnnotate.compile, chainExps, ClosAnnotate.annotateSing, ClosAnnotate.altFreeSing,
    ClosAnnotate.altFreeList, ClosAnnotate.shiftSing, ClosAnnotate.shiftList, evaluate, fixClock,
    initialState, findCode, initialSourceCode_cons_lookup, decClock, doApp, applyNumeric, doIntApp]

/-- A zero-clock call to the dummy entry times out without changing FFI state. -/
theorem emptyAnnotatedChain_zero {C F : Type} (ffi : HolFfiState F) (maxApp start : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C) :
    evaluate [.call .none 0 start []] []
      (initialState ffi maxApp (initialSourceCode (ClosAnnotate.compile (chainExps start []))) oracle compiler 0) =
      (.err (.abort .timeoutError), initialState ffi maxApp
        (initialSourceCode (ClosAnnotate.compile (chainExps start []))) oracle compiler 0) := by
  simp [ClosAnnotate.compile, chainExps, ClosAnnotate.annotateSing, ClosAnnotate.altFreeSing,
    ClosAnnotate.altFreeList, ClosAnnotate.shiftSing, ClosAnnotate.shiftList, evaluate, fixClock,
    initialState, findCode, initialSourceCode_cons_lookup]

/-- The empty expression list has the immediate successful observation. -/
theorem emptySource_semantics {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (oracle : CompileOracle C) (compiler : Compiler C) :
    semantics ffi maxApp code oracle compiler [] = .terminate .success ffi.ioEvents := by
  classical
  have noError : ¬ ∃ clock, (evaluate [] [] (initialState ffi maxApp code oracle compiler clock)).1 =
      .err (.abort .typeError) := by simp [evaluate]
  have observed : terminatingObservation ffi maxApp code oracle compiler [] (.terminate .success ffi.ioEvents) := by
    refine ⟨0, .val [], initialState ffi maxApp code oracle compiler 0, .success, ?_, ?_, ?_⟩
    · simp [evaluate]
    · rfl
    · rfl
  have unique : ∀ behavior, terminatingObservation ffi maxApp code oracle compiler [] behavior →
      behavior = .terminate .success ffi.ioEvents := by
    intro behavior ⟨clock, result, state, outcome, run, resultOutcome, behaviorEq⟩
    simp [evaluate] at run
    rcases run with ⟨rfl, rfl⟩
    subst outcome
    simpa [initialState] using behaviorEq
  unfold semantics
  rw [if_neg noError, HolLList.holOptionSome_eq_some observed unique]

/-- The generated dummy entry has the same successful observation as an
empty source batch. -/
theorem emptyAnnotatedChain_semantics {C F : Type} (ffi : HolFfiState F) (maxApp start : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C) :
    semantics ffi maxApp (initialSourceCode (ClosAnnotate.compile (chainExps start []))) oracle compiler
      [.call .none 0 start []] = .terminate .success ffi.ioEvents := by
  classical
  let code := initialSourceCode (ClosAnnotate.compile (chainExps start []))
  have noError : ¬ ∃ clock, (evaluate [.call .none 0 start []] []
      (initialState ffi maxApp code oracle compiler clock)).1 = .err (.abort .typeError) := by
    rintro ⟨clock, bad⟩
    cases clock with
    | zero => simp [code, emptyAnnotatedChain_zero] at bad
    | succ clock => simp [code, emptyAnnotatedChain_run] at bad
  have observed : terminatingObservation ffi maxApp code oracle compiler [.call .none 0 start []]
      (.terminate .success ffi.ioEvents) := by
    refine ⟨1, .val [.number 0], initialState ffi maxApp code oracle compiler 0, .success, ?_, ?_, ?_⟩
    · simpa [code] using emptyAnnotatedChain_run ffi maxApp start 0 oracle compiler
    · rfl
    · rfl
  have unique : ∀ behavior, terminatingObservation ffi maxApp code oracle compiler [.call .none 0 start []] behavior →
      behavior = .terminate .success ffi.ioEvents := by
    intro behavior ⟨clock, result, state, outcome, run, resultOutcome, behaviorEq⟩
    cases clock with
    | zero =>
      rw [show evaluate [.call .none 0 start []] [] (initialState ffi maxApp code oracle compiler 0) =
        (.err (.abort .timeoutError), initialState ffi maxApp code oracle compiler 0) from
          emptyAnnotatedChain_zero ffi maxApp start oracle compiler] at run
      cases run
      exact False.elim resultOutcome
    | succ clock =>
      rw [show evaluate [.call .none 0 start []] [] (initialState ffi maxApp code oracle compiler (clock + 1)) =
        (.val [.number 0], initialState ffi maxApp code oracle compiler clock) from
          emptyAnnotatedChain_run ffi maxApp start clock oracle compiler] at run
      cases run
      subst outcome
      simpa [initialState] using behaviorEq
  change semantics ffi maxApp code oracle compiler [.call .none 0 start []] = _
  unfold semantics
  rw [if_neg noError, HolLList.holOptionSome_eq_some observed unique]

/-- The no-optimization closure compiler preserves source behavior for both
empty and nonempty batches under the stated safety and oracle assumptions. -/
theorem compileNoOpts_source_semantics {C F : Type} (ffi : HolFfiState F)
    (config current output : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : ClosSem.CompileOracle (Nat × C)) (targetCompiler : BvlSem.Compiler C)
    (preprocess : compileCommonNoOpts? config expressions = some (current, program))
    (compile : compileNoOpts? config expressions = some (output, compiled, names))
    (nonfail : semantics ffi config.maxApp HolFiniteMapExact.empty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc ClosAnnotate.compileInc (pureCc (compileInc config.maxApp) targetCompiler))) expressions ≠ .fail)
    (numberSafe : ¬ containsAppSome config.maxApp expressions) (varsSafe : everyFnVarsNone expressions)
    (oracleSafe : ∀ index, (oracle index).2.2 = [] ∧
      ¬ containsAppSome config.maxApp (oracle index).2.1 ∧ everyFnVarsNone (oracle index).2.1)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (initialBound : current.nextLoc ≤ (oracle 0).1.1) :
    BvlSem.semantics ffi (sptFromAList compiled)
      (pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
        stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) targetCompiler output.start =
      semantics ffi config.maxApp HolFiniteMapExact.empty oracle
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
          (pureCc ClosAnnotate.compileInc (pureCc (compileInc config.maxApp) targetCompiler))) expressions := by
  by_cases nonempty : expressions ≠ []
  · exact compileNoOpts_source_semantics_nonempty ffi config current output expressions program compiled names
      oracle targetCompiler preprocess compile nonempty nonfail numberSafe varsSafe oracleSafe oracleState initialBound
  · have empty : expressions = [] := by simpa using nonempty
    subst expressions
    by_cases enabled : config.doMti || config.doCall
    · simp [compileCommonNoOpts?, enabled] at preprocess
    · cases known : config.knownConf with
      | some k => simp [compileCommonNoOpts?, enabled, known] at preprocess
      | none =>
        let next := config.nextLoc + max 1 ([] : List ClosLang.Exp).length
        let aligned := if next % 2 = 0 then next else next + 1
        have run : compileCommonNoOpts? config [] =
            some ({ config with start := config.nextLoc, nextLoc := aligned, knownConf := none, callState := (.ln, []) },
              ClosAnnotate.compile (chainExps config.nextLoc [])) := by
          simp [compileCommonNoOpts?, enabled, known, next, aligned, ClosNumber.renumberList]
        have equal := Option.some.inj (preprocess.symm.trans run)
        cases equal
        have chainNonfail : semantics ffi config.maxApp
            (initialSourceCode (ClosAnnotate.compile (chainExps config.nextLoc [])))
            (pureCo ClosAnnotate.compileInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
            (pureCc (compileInc config.maxApp) targetCompiler) [.call .none 0 config.nextLoc []] ≠ .fail := by
          rw [emptyAnnotatedChain_semantics]
          simp
        have compiledEq := compileNoOpts_numberedOracle_semantics ffi config _ output [] _ compiled names
          oracle targetCompiler run compile chainNonfail oracleState initialBound
          (by intro i; simp [(oracleSafe i).1, ClosProps.codeLocations])
          (by intro i label member; simp [(oracleSafe i).1, ClosProps.codeLocations] at member)
          (by intro i label inMain inAux; simp [(oracleSafe i).1, ClosProps.codeLocations] at inAux)
          (by intro i entry member; simp [(oracleSafe i).1] at member)
          (by intro i entry member; simp [(oracleSafe i).1] at member)
        rw [emptyAnnotatedChain_semantics] at compiledEq
        rw [emptySource_semantics]
        exact compiledEq

/-- With all optional closure optimizations disabled, the production driver
is exactly the no-optimization compiler for every traversal fuel. -/
theorem compileCallMtiFuel_noOpts (fuel : Nat) (config : Config) (expressions : List ClosLang.Exp)
    (mti : config.doMti = false) (calls : config.doCall = false) (known : config.knownConf = none) :
    compileCallMtiFuel? fuel config expressions = compileNoOpts? config expressions := by
  simp only [compileCallMtiFuel?, compileNoOpts?, compileCommonNoOpts?, ClosMti.compileFuel,
    ClosKnown.compileFuel, ClosCall.compileFuel, mti, calls, known, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte, Option.bind_eq_bind, Option.bind]
  cases h : ClosNumber.renumberList
      (if (config.nextLoc + max 1 expressions.length) % 2 = 0 then config.nextLoc + max 1 expressions.length
       else config.nextLoc + max 1 expressions.length + 1) expressions with
  | mk next transformed =>
    simp

/-- With known-function and direct-call conversion disabled, the full driver
executes the same preprocessing as the no-optimization driver on the actual
multi-argument output. The original expressions are retained for the name
table, as in the production driver. -/
theorem compileCallMtiFuel_mtiOnly (fuel : Nat) (config : Config) (expressions : List ClosLang.Exp)
    (calls : config.doCall = false) (known : config.knownConf = none) :
    compileCallMtiFuel? fuel config expressions = (do
      let transformed ← ClosMti.compileFuel fuel config.doMti config.maxApp expressions
      let (current, program) ← compileCommonNoOpts? { config with doMti := false } transformed
      compilePrepared? config { current with doMti := config.doMti } expressions program) := by
  simp only [compileCallMtiFuel?, compileCommonNoOpts?, calls, known, ClosKnown.compileFuel,
    ClosCall.compileFuel, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    Option.bind_eq_bind, Option.bind]
  cases mti : ClosMti.compileFuel fuel config.doMti config.maxApp expressions with
  | none => rfl
  | some transformed =>
    cases numbered : ClosNumber.renumberList
        (if (config.nextLoc + max 1 transformed.length) % 2 = 0 then config.nextLoc + max 1 transformed.length
         else config.nextLoc + max 1 transformed.length + 1) transformed with
    | mk next numberedExpressions => simp

/-- The production closure driver inherits the no-optimization source
behavior theorem when all optional closure optimizations are disabled. -/
theorem compileCallMtiFuel_noOpts_semantics {C F : Type} (ffi : HolFfiState F)
    (fuel : Nat) (config current output : Config) (expressions : List ClosLang.Exp)
    (program : List (Nat × Nat × ClosLang.Exp)) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : ClosSem.CompileOracle (Nat × C)) (targetCompiler : BvlSem.Compiler C)
    (mti : config.doMti = false) (calls : config.doCall = false) (known : config.knownConf = none)
    (preprocess : compileCommonNoOpts? config expressions = some (current, program))
    (compile : compileCallMtiFuel? fuel config expressions = some (output, compiled, names))
    (nonfail : semantics ffi config.maxApp HolFiniteMapExact.empty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc ClosAnnotate.compileInc (pureCc (compileInc config.maxApp) targetCompiler))) expressions ≠ .fail)
    (numberSafe : ¬ containsAppSome config.maxApp expressions) (varsSafe : everyFnVarsNone expressions)
    (oracleSafe : ∀ index, (oracle index).2.2 = [] ∧
      ¬ containsAppSome config.maxApp (oracle index).2.1 ∧ everyFnVarsNone (oracle index).2.1)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (initialBound : current.nextLoc ≤ (oracle 0).1.1) :
    BvlSem.semantics ffi (sptFromAList compiled)
      (pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
        stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) targetCompiler output.start =
      semantics ffi config.maxApp HolFiniteMapExact.empty oracle
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
          (pureCc ClosAnnotate.compileInc (pureCc (compileInc config.maxApp) targetCompiler))) expressions := by
  apply compileNoOpts_source_semantics ffi config current output expressions program compiled names oracle targetCompiler
    preprocess _ nonfail numberSafe varsSafe oracleSafe oracleState initialBound
  simpa [← compileCallMtiFuel_noOpts fuel config expressions mti calls known] using compile

end Flapjack.Compiler.Backend.ClosToBvl

module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Semantics

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.BvlSem.Evaluate
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Initialization of the closure-to-BVL simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- Once the target's reserved global table has been installed, empty source
and target stores satisfy the candidate state relation. The hypotheses are
the installed application stubs, compiler-oracle relation, and compiled source
code required by that relation. -/
theorem initial_stateRel {C F : Type} (ffi : HolFfiState F) (maxApp clock : Nat)
    (sourceCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (sourceOracle : ClosSem.CompileOracle C)
    (sourceCompiler : ClosSem.Compiler C) (targetCode : Spt (Nat × Bvl.Exp))
    (targetOracle : BvlSem.CompileOracle C) (targetCompiler : BvlSem.Compiler C)
    (generic : ∀ n, n < maxApp → sptLookup (genericAppFnLocation n) targetCode =
      some (n + 2, generateGenericApp maxApp n))
    (partialStubs : ∀ total n, total < maxApp ∧ n < total →
      sptLookup (partialAppFnLocation maxApp total n) targetCode =
        some (total - n + 1, generatePartialAppClosureFn total n))
    (force : sptLookup (numStubs maxApp - 2) targetCode = some (2, forceThunkCode))
    (oracle : compileOracleInv maxApp sourceCode sourceCompiler sourceOracle targetCode targetCompiler targetOracle)
    (compiledCode : ∀ name arity body, sourceCode.lookup name = some (arity, body) →
      ∃ aux targetBody finalAux, compileExpsHOL maxApp [body] aux = ([targetBody], finalAux) ∧
        sptLookup (name + numStubs maxApp) targetCode = some (arity, targetBody) ∧
        codeInstalled finalAux targetCode) :
    stateRel HolFiniteMapExact.empty
      (ClosSem.initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)
      { BvlSem.initialState ffi targetCode targetOracle targetCompiler clock with globals := [some (globalTable maxApp)] } := by
  simp [stateRel, ClosSem.initialState, BvlSem.initialState, numAddedGlobals, ClosSem.getGlobal,
    HolFiniteMapExact.empty, force, oracle]
  exact ⟨generic, fun total n h1 h2 => partialStubs total n ⟨h1, h2⟩, compiledCode⟩

/-- A list of installed code labels evaluates to its corresponding code
pointers without changing the target state. -/
theorem evaluate_installed_labels {C F : Type} (labels : List Nat) (env : List BvlSem.Value)
    (state : BvlSem.State C F)
    (installed : ∀ label ∈ labels, ∃ entry, sptLookup label state.code = some entry) :
    BvlSem.evaluate (labels.map mkLabel) env state = (.val (labels.map BvlSem.Value.codePtr), state) := by
  induction labels with
  | nil => simp [BvlSem.evaluate]
  | cons label rest ih =>
    obtain ⟨entry, lookup⟩ := installed label (by simp)
    have headRun : BvlSem.evaluate [mkLabel label] env state = (.val [.codePtr label], state) := by
      simp [mkLabel, BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, lookup]
    have tailRun := ih (fun name member => installed name (by simp [member]))
    have combined := BvlProps.evaluateAppend [mkLabel label] env state (rest.map mkLabel)
    simpa [BvlSem.evaluateTuple, headRun, tailRun] using combined

/-- The initialization wrapper creates the reserved partial-application
table before entering the compiled source entry. -/
theorem evaluate_initGlobals {C F : Type} (maxApp start : Nat) (state : BvlSem.State C F)
    (emptyGlobals : state.globals = [])
    (installed : ∀ total previous, total < maxApp → previous < total →
      ∃ entry, sptLookup (partialAppFnLocation maxApp total previous) state.code = some entry) :
    BvlSem.evaluate [initGlobals maxApp start] [] state =
      BvlSem.evaluate [.call 0 (some start) []] [] { state with globals := [some (globalTable maxApp)] } := by
  let labels := ((List.range maxApp).map fun total =>
    (List.range total).map fun previous => partialAppFnLocation maxApp total previous).flatten
  let allocated := { state with globals := [none] }
  have labelInstalled : ∀ label ∈ labels.reverse, ∃ entry, sptLookup label allocated.code = some entry := by
    intro label member
    simp only [List.mem_reverse, labels, List.mem_flatten, List.mem_map, List.mem_range] at member
    obtain ⟨inner, ⟨total, totalBound, innerEq⟩, labelMember⟩ := member
    subst inner
    obtain ⟨previous, previousBound, labelEq⟩ := List.mem_map.mp labelMember
    subst label
    exact installed total previous totalBound (List.mem_range.mp previousBound)
  have labelRun := evaluate_installed_labels labels.reverse [BvlSem.unitValue] allocated labelInstalled
  have allocRun : BvlSem.evaluate [.op (.globOp .allocGlobal) [.op (.intOp (.const 1)) []]] [] state =
      (.val [BvlSem.unitValue], allocated) := by
    simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyGlobal,
      BvlSem.applyNumeric, BvlSem.doIntApp, allocated, emptyGlobals]
  have labelRun' : BvlSem.evaluate
      (((List.range maxApp).map fun total =>
        (List.range total).map fun previous => mkLabel (partialAppFnLocation maxApp total previous)).flatten.reverse)
      [BvlSem.unitValue] allocated = (.val (labels.reverse.map BvlSem.Value.codePtr), allocated) := by
    simpa [labels, List.map_flatten, List.map_map, Function.comp_def] using labelRun
  have blockRun : BvlSem.evaluate
      [.op (.blockOp (.cons 0)) (((List.range maxApp).map fun total =>
        (List.range total).map fun previous => mkLabel (partialAppFnLocation maxApp total previous)).flatten.reverse)]
      [BvlSem.unitValue] allocated = (.val [globalTable maxApp], allocated) := by
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, labelRun']
    simp [BvlSem.doApp, BvlSem.applyBlock, globalTable, labels, List.map_flatten, List.map_map, Function.comp_def]
  have setRun : BvlSem.evaluate
      [.op (.globOp (.setGlobal 0)) [.op (.blockOp (.cons 0)) (((List.range maxApp).map fun total =>
        (List.range total).map fun previous => mkLabel (partialAppFnLocation maxApp total previous)).flatten.reverse)]]
      [BvlSem.unitValue] allocated =
      (.val [BvlSem.unitValue], { state with globals := [some (globalTable maxApp)] }) := by
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, blockRun]
    simp [BvlSem.doApp, BvlSem.applyGlobal, allocated]
  rw [initGlobals, BvlSem.evaluate, BvlSem.fixClock_evaluate, allocRun]
  simp only [List.append_nil, partialAppLabelTableLoc, BackendCommon.tupleTag]
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, setRun]
  simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.findCode]

/-- Entering the installed zero-argument initialization stub costs one clock
unit and then calls the compiled entry with the reserved table in place. -/
theorem evaluate_initial_entry {C F : Type} (ffi : HolFfiState F) (maxApp clock targetStart sourceStart : Nat)
    (code : Spt (Nat × Bvl.Exp)) (oracle : BvlSem.CompileOracle C) (compiler : BvlSem.Compiler C)
    (entry : sptLookup targetStart code = some (0, initGlobals maxApp sourceStart))
    (installed : ∀ total previous, total < maxApp → previous < total →
      ∃ stub, sptLookup (partialAppFnLocation maxApp total previous) code = some stub) :
    BvlSem.evaluate [.call 0 (some targetStart) []] [] (BvlSem.initialState ffi code oracle compiler (clock + 1)) =
      BvlSem.evaluate [.call 0 (some sourceStart) []] []
        { BvlSem.initialState ffi code oracle compiler clock with globals := [some (globalTable maxApp)] } := by
  have initialized := evaluate_initGlobals maxApp sourceStart (BvlSem.initialState ffi code oracle compiler clock)
    rfl installed
  simpa [BvlSem.evaluate, BvlSem.fixClock, BvlSem.findCode, BvlSem.initialState, BvlSem.decClock, entry] using initialized

/-- Forgetting related result payloads retains their observable result shape. -/
theorem observableResultRel_of_resultRel {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {source : Result (List ClosSem.Value) ClosSem.Value} {target : Result (List BvlSem.Value) BvlSem.Value}
    (related : resultRel (List.Forall₂ (vRel maxApp f refs code)) (vRel maxApp f refs code) source target) :
    observableResultRel source target := by
  cases source with
  | val values =>
    cases target with
    | val targets => simp [observableResultRel, resultRel]
    | err error => simp [resultRel] at related
  | err error =>
    cases target with
    | val targets => simp [resultRel] at related
    | err targetError =>
      exact excRel_mono _ _ (fun _ _ _ => True.intro) error targetError related

/-- Installed entry code and the initial oracle and state invariants imply
the forward initial-evaluation simulation for a source entry call. -/
theorem initialEvaluationSimulation_of_entry {C F : Type} (ffi : HolFfiState F) (maxApp sourceStart targetStart : Nat)
    (sourceCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (sourceOracle : ClosSem.CompileOracle C)
    (sourceCompiler : ClosSem.Compiler C) (targetCode : Spt (Nat × Bvl.Exp))
    (targetOracle : BvlSem.CompileOracle C) (targetCompiler : BvlSem.Compiler C)
    (generic : ∀ n, n < maxApp → sptLookup (genericAppFnLocation n) targetCode =
      some (n + 2, generateGenericApp maxApp n))
    (partialStubs : ∀ total n, total < maxApp ∧ n < total →
      sptLookup (partialAppFnLocation maxApp total n) targetCode =
        some (total - n + 1, generatePartialAppClosureFn total n))
    (force : sptLookup (numStubs maxApp - 2) targetCode = some (2, forceThunkCode))
    (oracle : compileOracleInv maxApp sourceCode sourceCompiler sourceOracle targetCode targetCompiler targetOracle)
    (compiledCode : ∀ name arity body, sourceCode.lookup name = some (arity, body) →
      ∃ aux targetBody finalAux, compileExpsHOL maxApp [body] aux = ([targetBody], finalAux) ∧
        sptLookup (name + numStubs maxApp) targetCode = some (arity, targetBody) ∧ codeInstalled finalAux targetCode)
    (annotations : codeAnnotations (ClosSem.initialState ffi maxApp sourceCode sourceOracle sourceCompiler 0))
    (entry : sptLookup targetStart targetCode = some (0, initGlobals maxApp (sourceStart + numStubs maxApp))) :
    initialEvaluationSimulation ffi maxApp sourceCode sourceOracle sourceCompiler [.call .none 0 sourceStart []]
      targetCode targetOracle targetCompiler targetStart := by
  intro clock result final run noType
  let source := ClosSem.initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock
  let target := { BvlSem.initialState ffi targetCode targetOracle targetCompiler clock with
    globals := [some (globalTable maxApp)] }
  have states : stateRel HolFiniteMapExact.empty source target :=
    initial_stateRel ffi maxApp clock sourceCode sourceOracle sourceCompiler targetCode targetOracle targetCompiler
      generic partialStubs force oracle compiledCode
  have codeAnnotations' : codeAnnotations source := by
    simpa [source, codeAnnotations, ClosSem.initialState] using annotations
  have compilation : compileExpsHOL maxApp [.call .none 0 sourceStart []] [] =
      ([.call 0 (some (sourceStart + numStubs maxApp)) []], []) := by
    rw [compileExps_eq_list]
    simp [compileExpListHOL, compileExpHOL]
  have post := expressionSimulation_all (C := C) (F := F) [.call .none 0 sourceStart []]
    source final target [] [] HolFiniteMapExact.empty [] [] [.call 0 (some (sourceStart + numStubs maxApp)) []]
    result run noType (by simpa [source, ClosSem.initialState] using compilation)
    (by simp [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp]) codeAnnotations'
    (by simp [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp]) (by simp [codeInstalled])
    (by simp [envRel]) states
  obtain ⟨extra, targetResult, targetFinal, fFinal, targetRun, related, finalStates, _, _, _, _⟩ := post
  refine ⟨extra + 1, targetResult, targetFinal, ?_, observableResultRel_of_resultRel related, finalStates.1⟩
  have entryRun := evaluate_initial_entry ffi maxApp (clock + extra) targetStart
    (sourceStart + numStubs maxApp) targetCode targetOracle targetCompiler entry
    (fun total previous h1 h2 => ⟨_, partialStubs total previous ⟨h1, h2⟩⟩)
  rw [show clock + (extra + 1) = (clock + extra) + 1 by omega, entryRun]
  simpa [source, target, ClosSem.initialState, BvlSem.initialState] using targetRun

/-- The installed entry code preserves the proof-side whole-program behavior
of a non-failing source entry call. This candidate remains untagged pending
review of the evaluator and state carriers against HOL. -/
theorem entry_semantics_eq {C F : Type} (ffi : HolFfiState F) (maxApp sourceStart targetStart : Nat)
    (sourceCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (sourceOracle : ClosSem.CompileOracle C)
    (sourceCompiler : ClosSem.Compiler C) (targetCode : Spt (Nat × Bvl.Exp))
    (targetOracle : BvlSem.CompileOracle C) (targetCompiler : BvlSem.Compiler C)
    (nonfail : ClosSem.semantics ffi maxApp sourceCode sourceOracle sourceCompiler [.call .none 0 sourceStart []] ≠ .fail)
    (generic : ∀ n, n < maxApp → sptLookup (genericAppFnLocation n) targetCode =
      some (n + 2, generateGenericApp maxApp n))
    (partialStubs : ∀ total n, total < maxApp ∧ n < total →
      sptLookup (partialAppFnLocation maxApp total n) targetCode =
        some (total - n + 1, generatePartialAppClosureFn total n))
    (force : sptLookup (numStubs maxApp - 2) targetCode = some (2, forceThunkCode))
    (oracle : compileOracleInv maxApp sourceCode sourceCompiler sourceOracle targetCode targetCompiler targetOracle)
    (compiledCode : ∀ name arity body, sourceCode.lookup name = some (arity, body) →
      ∃ aux targetBody finalAux, compileExpsHOL maxApp [body] aux = ([targetBody], finalAux) ∧
        sptLookup (name + numStubs maxApp) targetCode = some (arity, targetBody) ∧ codeInstalled finalAux targetCode)
    (annotations : codeAnnotations (ClosSem.initialState ffi maxApp sourceCode sourceOracle sourceCompiler 0))
    (entry : sptLookup targetStart targetCode = some (0, initGlobals maxApp (sourceStart + numStubs maxApp))) :
    BvlSem.semantics ffi targetCode targetOracle targetCompiler targetStart =
      ClosSem.semantics ffi maxApp sourceCode sourceOracle sourceCompiler [.call .none 0 sourceStart []] := by
  apply semantics_eq_of_initialSimulation ffi maxApp sourceCode sourceOracle sourceCompiler _
    targetCode targetOracle targetCompiler targetStart nonfail
  exact initialEvaluationSimulation_of_entry ffi maxApp sourceStart targetStart sourceCode sourceOracle sourceCompiler
    targetCode targetOracle targetCompiler generic partialStubs force oracle compiledCode annotations entry

private def toBroad (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) := code.lookup
private def ofBroad (lookup : Nat → Option (Nat × ClosLang.Exp))
    (finite : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat (Nat × ClosLang.Exp) := ⟨lookup, finite⟩

/-- The source-code finite map roundtrips through its lookup/support view. -/
theorem holFmapAsFiniteSupportParamWitness_initCodeRelation_code1
    (code1 : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code1) code1.finiteSupport).lookup key = code1.lookup key ∧
    (ofBroad (toBroad code1) code1.finiteSupport).finiteSupport = code1.finiteSupport ∧
    ofBroad (toBroad code1) code1.finiteSupport = code1 := by
  cases code1
  exact ⟨rfl, rfl, rfl⟩

/-- Installed generic and partial-application stubs and compiled source code. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "init_code_def"
  (fmap_as_finite_support_parameters := [code1])]
def initCodeRelation (code1 : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (code2 : Spt (Nat × Bvl.Exp)) (maxApp : Nat) : Prop :=
  (∀ n, n < maxApp → sptLookup (genericAppFnLocation n) code2 =
    some (n + 2, generateGenericApp maxApp n)) ∧
  (∀ total previous, total < maxApp ∧ previous < total →
    sptLookup (partialAppFnLocation maxApp total previous) code2 =
      some (total + 1 - previous, generatePartialAppClosureFn total previous)) ∧
  ∀ name arity body, code1.lookup name = some (arity, body) →
    ∃ aux1 body2 aux2, compileExpsHOL maxApp [body] aux1 = ([body2], aux2) ∧
      sptLookup (name + numStubs maxApp) code2 = some (arity, body2) ∧ codeInstalled aux2 code2

/-- The source-code map used by program semantics has the same codec. -/
theorem holFmapAsFiniteSupportParamWitness_compileProgSemantics_source_code1
    (code1 : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code1) code1.finiteSupport).lookup key = code1.lookup key ∧
    (ofBroad (toBroad code1) code1.finiteSupport).finiteSupport = code1.finiteSupport ∧
    ofBroad (toBroad code1) code1.finiteSupport = code1 :=
  holFmapAsFiniteSupportParamWitness_initCodeRelation_code1 code1 key

/-- Program-level observational preservation with the original installed-code,
annotation, oracle, and non-failure hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_prog_semantics"
  (fmap_as_finite_support_parameters := [code1])]
theorem compileProgSemantics_source {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code1 : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (co1 : ClosSem.CompileOracle C)
    (cc1 : ClosSem.Compiler C) (start : Nat) (code2 : Spt (Nat × Bvl.Exp))
    (prog1 : List (Nat × Nat × ClosLang.Exp)) (prog2 : List (Nat × Nat × Bvl.Exp))
    (nsm1 : Nat) (cc2 : BvlSem.Compiler C) (co2 : BvlSem.CompileOracle C)
    (hypotheses :
      ClosSem.semantics ffi maxApp code1 co1 cc1 [.call .none 0 start []] ≠ .fail ∧
      (∀ name arity body, code1.lookup name = some (arity, body) →
        ∃ aux1 body2 aux2, compileExpsHOL maxApp [body] aux1 = ([body2], aux2) ∧
          sptLookup (name + numStubs maxApp) code2 = some (arity, body2) ∧ codeInstalled aux2 code2) ∧
      compileProgExpsHOL maxApp prog1 = prog2 ∧ initCodeRelation code1 code2 maxApp ∧
      (∀ name arity body, code1.lookup name = some (arity, body) → ClosProps.everyFnLocationSome [body]) ∧
      (∀ name arity body, code1.lookup name = some (arity, body) → ClosProps.everyFnVarsSome [body]) ∧
      sptLookup nsm1 code2 = some (0, initGlobals maxApp (numStubs maxApp + start)) ∧
      sptLookup (numStubs maxApp - 2) code2 = some (2, forceThunkCode) ∧
      compileOracleInv maxApp code1 cc1 co1 code2 cc2 co2 ∧ codeInstalled prog2 code2) :
    BvlSem.semantics ffi code2 co2 cc2 nsm1 =
      ClosSem.semantics ffi maxApp code1 co1 cc1 [.call .none 0 start []] := by
  rcases hypotheses with ⟨nonfail, compiled, _, ⟨generic, partialStubs, _⟩, locations, vars, entry, force, oracle, _⟩
  apply entry_semantics_eq ffi maxApp start nsm1 code1 co1 cc1 code2 co2 cc2 nonfail generic
    ?_ force oracle compiled ?_ ?_
  · intro total previous bounds
    have arithmetic : total + 1 - previous = total - previous + 1 := by omega
    simpa [arithmetic] using partialStubs total previous bounds
  · simpa [codeAnnotations, ClosSem.initialState] using And.intro locations vars
  · simpa [Nat.add_comm] using entry

end Flapjack.Compiler.Backend.ClosToBvl

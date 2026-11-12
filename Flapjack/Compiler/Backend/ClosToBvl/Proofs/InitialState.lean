module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Semantics

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Initialization of the closure-to-BVL simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- Replicating a value once produces a singleton list. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "REPLICATE_1"]
theorem replicateOne {α : Type} (x : α) : List.replicate 1 x = [x] := rfl

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

namespace InitDomain

/-- The BVL reference store roundtrips through its finite-support view. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness

/-- Each installed partial-application label evaluates to its code pointer. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_init1"
  (fmap_as_finite_support := [refs])]
theorem evaluate_init1 {C F : Type} (mapp2 mapp1 total : Nat)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F)
    (installed : ∀ n, n < mapp2 → sptMem (partialAppFnLocation mapp1 total n) state.code) :
    BvlSem.evaluate ((List.range mapp2).map (fun n => mkLabel (partialAppFnLocation mapp1 total n))).reverse
      [BvlSem.unitValue] state =
    (.val ((List.range mapp2).map (fun n => BvlSem.Value.codePtr (partialAppFnLocation mapp1 total n))).reverse, state) := by
  induction mapp2 with
  | zero => simp [BvlSem.evaluate]
  | succ n ih =>
    obtain ⟨entry, lookup⟩ := (sptMem_iff_lookup _ _).mp (installed n (by omega))
    have headRun : BvlSem.evaluate [mkLabel (partialAppFnLocation mapp1 total n)]
        [BvlSem.unitValue] state = (.val [.codePtr (partialAppFnLocation mapp1 total n)], state) := by
      simp [mkLabel, BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, lookup]
    have tailRun := ih (fun k bound => installed k (by omega))
    have combined := BvlProps.evaluateAppend [mkLabel (partialAppFnLocation mapp1 total n)]
      [BvlSem.unitValue] state
      (((List.range n).map (fun k => mkLabel (partialAppFnLocation mapp1 total k))).reverse)
    simpa [List.range_succ, List.map_append, BvlSem.evaluateTuple, headRun, tailRun] using combined

/-- The generated partial-application labels evaluate to code pointers when
all of their locations occur in the target code domain. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_init"
  (fmap_as_finite_support := [refs])]
theorem evaluate_init {C F : Type} (mapp2 mapp1 : Nat)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F)
    (installed : ∀ m n, m < mapp2 ∧ n < m →
      sptMem (partialAppFnLocation mapp1 m n) state.code) :
    BvlSem.evaluate (((List.range mapp2).map fun total =>
      (List.range total).map fun previous => mkLabel (partialAppFnLocation mapp1 total previous)).flatten.reverse)
      [BvlSem.unitValue] state =
    (.val (((List.range mapp2).map fun total =>
      (List.range total).map fun previous => BvlSem.Value.codePtr
        (partialAppFnLocation mapp1 total previous)).flatten.reverse), state) := by
  induction mapp2 with
  | zero => simp [BvlSem.evaluate]
  | succ n ih =>
    have headRun := evaluate_init1 n mapp1 n state (fun k bound => installed n k ⟨by omega, bound⟩)
    have tailRun := ih (fun m k bounds => installed m k ⟨by omega, bounds.2⟩)
    have combined := BvlProps.evaluateAppend
      (((List.range n).map fun k => mkLabel (partialAppFnLocation mapp1 n k)).reverse)
      [BvlSem.unitValue] state
      (((List.range n).map fun total =>
        (List.range total).map fun k => mkLabel (partialAppFnLocation mapp1 total k)).flatten.reverse)
    simpa [List.range_succ, List.map_append, BvlSem.evaluateTuple, headRun, tailRun] using combined

end InitDomain

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
  have labelRun := InitDomain.evaluate_init maxApp maxApp allocated (by
    intro total previous bounds
    exact (sptMem_iff_lookup _ _).2 (installed total previous bounds.1 bounds.2))
  have allocRun : BvlSem.evaluate [.op (.globOp .allocGlobal) [.op (.intOp (.const 1)) []]] [] state =
      (.val [BvlSem.unitValue], allocated) := by
    simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyGlobal,
      BvlSem.applyNumeric, BvlSem.doIntApp, allocated, emptyGlobals]
  have labelRun' : BvlSem.evaluate
      (((List.range maxApp).map fun total =>
        (List.range total).map fun previous => mkLabel (partialAppFnLocation maxApp total previous)).flatten.reverse)
      [BvlSem.unitValue] allocated = (.val (labels.reverse.map BvlSem.Value.codePtr), allocated) := by
    simpa [labels, List.map_reverse, List.map_flatten, List.map_map, Function.comp_def] using labelRun
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
  apply semantics_eq_of_initialSimulation ffi maxApp code1 co1 cc1 _
    code2 co2 cc2 nsm1 nonfail
  apply initialEvaluationSimulation_of_entry ffi maxApp start nsm1 code1 co1 cc1 code2 co2 cc2
    generic ?_ force oracle compiled ?_ ?_
  · intro total previous bounds
    have arithmetic : total + 1 - previous = total - previous + 1 := by omega
    simpa [arithmetic] using partialStubs total previous bounds
  · simpa [codeAnnotations, ClosSem.initialState] using And.intro locations vars
  · simpa [Nat.add_comm] using entry

end Flapjack.Compiler.Backend.ClosToBvl

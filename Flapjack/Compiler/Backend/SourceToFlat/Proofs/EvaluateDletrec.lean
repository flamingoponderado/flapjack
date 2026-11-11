module

import Flapjack.Compiler.Backend.FlatProps.ValueBasics

public import Flapjack.FiniteMap.AlistExact.Lookup
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateDlet
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateEmptyDeclarations
public import Flapjack.SemanticPrimitivesProps.RecursiveFunctions

@[expose] public section

/-! Recursive declaration simulation over the preliminary factored value and
state relations. These helpers are not yet a port of `compile_correct`. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendCommon
open OracleInvariant

/-- A non-type-error recursive declaration has distinct names and passes the
source constructor checks. -/
theorem dletrec_conditions_of_safe {F : Type} (source : State F) (sourceEnv : SemEnv Value)
    (location : Flapjack.Misc.Location.Locs) (funs : List (VarN × VarN × AstHOL.Exp))
    (safe : ∀ next, EvaluateHOL.evaluateDecs source sourceEnv [.dletrec location funs] ≠
      (next, .err (.abort .typeError))) :
    (funs.map Prod.fst).Nodup ∧
      funs.all (fun (_, _, expr) => everyExp (oneConCheck sourceEnv.c) expr) = true := by
  by_cases distinct : (funs.map Prod.fst).Nodup
  · cases wellformed : funs.all (fun (_, _, expr) => everyExp (oneConCheck sourceEnv.c) expr) with
    | true => exact ⟨distinct, rfl⟩
    | false =>
      have bad : EvaluateHOL.evaluateDecs source sourceEnv [.dletrec location funs] =
          (source, .err (.abort .typeError)) := by
        simp [EvaluateHOL.evaluateDecs, distinct, wellformed, EvaluateHOL.typeError]
      exact False.elim (safe source bad)
  · have bad : EvaluateHOL.evaluateDecs source sourceEnv [.dletrec location funs] =
        (source, .err (.abort .typeError)) := by
      simp [EvaluateHOL.evaluateDecs, distinct, EvaluateHOL.typeError]
    exact False.elim (safe source bad)

/-- Compiling recursive functions preserves their ordered names. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_funs_dom2"]
theorem compileFuns_names (trace : List VarN) (env : Environment)
    (funs : List (VarN × VarN × AstHOL.Exp)) :
    (compileFuns trace env funs).map Prod.fst = funs.map Prod.fst := by
  simp [compileFuns_map, List.map_map, Function.comp_def]

/-- A safe recursive declaration preserves the factored compiler invariant
after filling its reserved globals. Its relations and evaluator carriers
still need review against HOL's full `compile_correct` statement. -/
theorem evaluateDletrec_factored {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (env : Environment) (sourceEnv : SemEnv Value) (trace : List VarN)
    (funs : List (VarN × VarN × AstHOL.Exp))
    (sourceState : State F) (flatState : FlatSem.State C F)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (n : Nat) (gen : EnvironmentGenerationStore) (location : Flapjack.Misc.Location.Locs)
    (safe : ∀ next, EvaluateHOL.evaluateDecs sourceState sourceEnv [.dletrec location funs] ≠
      (next, .err (.abort .typeError)))
    (envInv : GlobalEnvInv genv env (fun _ => False) sourceEnv)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) sourceState flatState)
    (generation : envGenRel gen sourceState.evalState)
    (bounded : idxPrev (compileDecs trace n start env gen [.dletrec location funs]).2.1 finish) :
    EvaluateHOL.evaluateDecs sourceState sourceEnv [.dletrec location funs] =
      (sourceState, .val ⟨SemanticPrimitivesHOL.buildRecEnv funs sourceEnv nsEmpty, nsEmpty⟩) ∧
    ∃ finalGenv finalState,
      FlatSem.evaluateDecs flatState (compileDecs trace n start env gen [.dletrec location funs]).2.2.2.2 =
        (finalState, none) ∧
      GlobalGrowth genv finalGenv ∧ StateRel finalGenv sourceState finalState ∧
      EnvDomainEq (compileDecs trace n start env gen [.dletrec location funs]).2.2.1
        ⟨SemanticPrimitivesHOL.buildRecEnv funs sourceEnv nsEmpty, nsEmpty⟩ ∧
      GlobalEnvInv finalGenv (compileDecs trace n start env gen [.dletrec location funs]).2.2.1
        (fun _ => False) ⟨SemanticPrimitivesHOL.buildRecEnv funs sourceEnv nsEmpty, nsEmpty⟩ ∧
      factoredInvariant interp transform (compileDecs trace n start env gen [.dletrec location funs]).2.2.2.1
        finalGenv ((compileDecs trace n start env gen [.dletrec location funs]).2.1, finish, other)
        sourceState finalState ∧
      envGenRel (compileDecs trace n start env gen [.dletrec location funs]).2.2.2.1 sourceState.evalState ∧
      oracForwardRel interp sourceState.evalState sourceState.evalState := by
  obtain ⟨distinct, wellformed⟩ := dletrec_conditions_of_safe sourceState sourceEnv location funs safe
  have fits : funs.length + start.vidx ≤ finish.vidx := by
    have h := bounded.1
    simp only [compileDecs] at h
    omega
  let compiled := compileFuns trace
    { env with v := nsBindList ((funs.map Prod.fst).map
      (fun f => (f, VarName.localName .none f))) env.v } funs
  let sourceBindings := (funs.map Prod.fst).map (fun name => (name, Value.recclosure sourceEnv funs name))
  let flatBindings := (funs.map Prod.fst).map (fun name => (name, FlatSem.Value.recclosure ⟨[]⟩ compiled name))
  have names : flatBindings.map Prod.fst = funs.map Prod.fst := by
    simp [flatBindings, List.map_map, Function.comp_def]
  have flatDistinct : (flatBindings.map Prod.fst).Nodup := by simpa [names] using distinct
  have related : EnvRel genv (alistToNs sourceBindings) flatBindings := by
    rw [envRel_alist_iff]
    simp only [sourceBindings, flatBindings, List.forall₂_map_left_iff, List.forall₂_map_right_iff,
      List.forall₂_same]
    intro fn _
    refine ⟨trivial, ?_⟩
    have inv : GlobalEnvInv genv env (fun n => n ∈ ([] : List VarN)) sourceEnv := by
      simpa using envInv
    have closure := ValueRel.recclosure genv env sourceEnv nsEmpty funs fn.1 ⟨[]⟩ trace
      (List.replicate funs.length .none) (.empty genv) inv (by simp)
    have bindEq : bindLocals (List.replicate funs.length .none) (funs.map Prod.fst) env.v =
        nsBindList ((funs.map Prod.fst).map (fun f => (f, VarName.localName .none f))) env.v := by
      have empty : bindLocals [] [] env.v = env.v := rfl
      simpa only [List.append_nil, empty, nsAppend_to_nsBindList] using
        (nsAppend_bindLocals funs .none [] [] env.v).symm
    dsimp only at closure
    simpa only [List.map_nil, List.append_nil, bindEq, (nsAppend_nsEmpty sourceEnv.v).2, compiled] using closure
  obtain ⟨finalGenv, finalState, run, finalInv, constructors, types, slots, envResult⟩ :=
    invariantMakeVarls interp transform gen genv start finish other sourceState flatState start.vidx
      (flatBindings.map Prod.fst).reverse ⟨flatBindings⟩ 0 .none
      ⟨invariant, rfl, by simpa [names, Nat.add_comm] using fits, rfl, flatDistinct⟩
  have growth : GlobalGrowth genv finalGenv := by
    apply GlobalGrowth.ofSubglobals genv finalGenv slots
    · rw [constructors]; exact fun _ _ h => h
    · rw [types]; exact fun _ _ h => h
  have related' := envRel_growth genv finalGenv growth _ _ related
  have envResult' := envResult sourceBindings 0 related'
  have stateResult : StateRel finalGenv sourceState finalState := finalInv.2.2.1
  have nameShape : flatBindings.reverse.map Prod.fst = (funs.map Prod.fst).reverse := by
    simpa [List.map_reverse] using congrArg List.reverse names
  have flatEnv : FlatSem.buildRecEnv compiled ⟨[]⟩ [] = flatBindings := by
    rw [FlatProps.buildRecEnv_merge compiled (), List.append_nil]
    simpa only [flatBindings, List.map_map, Function.comp_def] using
      congrArg (List.map (fun name => (name, FlatSem.Value.recclosure ⟨[]⟩ compiled name)))
        (compileFuns_names trace _ funs)
  have bodyRun : FlatSem.evaluate ⟨FlatSem.buildRecEnv compiled ⟨[]⟩ []⟩ flatState
      [makeVarls 0 .none start.vidx (funs.map Prod.fst).reverse] =
        (finalState, .val [FlatSem.unitValue]) := by
    simpa [flatEnv, names] using run
  constructor
  · simp [EvaluateHOL.evaluateDecs, distinct, wellformed]
  refine ⟨finalGenv, finalState, ?_, growth, stateResult,
    ?_, ?_, ?_, ?_, oracForwardRel_refl interp _⟩
  · have beforeClock := ((stateRel_iff genv sourceState flatState).mp invariant.2.2.1).2.2.1
    have afterClock := ((stateRel_iff finalGenv sourceState finalState).mp stateResult).2.2.1
    have clock : finalState.clock = flatState.clock := afterClock.symm.trans beforeClock
    simp only [compileDecs, FlatSem.evaluateDecs, FlatSem.evaluate, compileFuns_names, distinct, if_true]
    rw [bodyRun]
    simp [FlatSem.fixClock, ← clock, FlatSem.unitValue]
  · simp only [compileDecs, Flapjack.SemanticPrimitivesProps.buildRecEnv_merge funs (),
      (nsAppend_nsEmpty _).1]
    obtain ⟨values, valueModules⟩ := alistToNs_domains_eq (M := ModN)
      (allocDefs (n + 1) start.vidx (funs.map Prod.fst).reverse)
      (funs.map (fun fn => (fn.1, Value.recclosure sourceEnv funs fn.1))) (by
        intro key
        simp [fst_allocDefs, List.map_map, Function.comp_def])
    exact ⟨values, valueModules, envDomainEq_empty.2.2⟩
  · simpa only [compileDecs, Flapjack.SemanticPrimitivesProps.buildRecEnv_merge funs (),
      (nsAppend_nsEmpty _).1, List.map_map, Function.comp_def, ← nameShape, List.map_reverse, emptyEnv,
      sourceBindings, allocDefs_ignoreCounter _ (n + 1) 0 start.vidx] using envResult'
  · simpa [compileDecs, names] using finalInv
  · simpa [compileDecs] using generation

/-- Recursive declaration case in the shape of the declaration conjunct of
the original compiler theorem, using Flapjack's preliminary factored
relations. The relations and evaluator carriers still require HOL review. -/
theorem evaluateDletrec_case_factored {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (env nextEnv : Environment) (sourceEnv : SemEnv Value) (trace : List VarN)
    (funs : List (VarN × VarN × AstHOL.Exp)) (source sourceLast : State F)
    (flat : FlatSem.State C F) (start finish next : NextIndices) (other : Set (Nat × IndexKind))
    (n n' : Nat) (gen nextGen : EnvironmentGenerationStore) (location : Flapjack.Misc.Location.Locs)
    (flatDecs : List FlatLang.Exp) (result : Result (SemEnv Value) Value)
    (sourceRun : EvaluateHOL.evaluateDecs source sourceEnv [.dletrec location funs] = (sourceLast, result))
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (compiled : compileDecs trace n start env gen [.dletrec location funs] =
      (n', next, nextEnv, nextGen, flatDecs))
    (envInv : GlobalEnvInv genv env (fun _ => False) sourceEnv)
    (notTypeError : result ≠ .err (.abort .typeError))
    (generation : envGenRel gen source.evalState)
    (_future : envGenFutureRel interp nextGen source.evalState)
    (bounded : idxPrev next finish) :
    FactoredDecCase interp transform genv source sourceLast flat finish next other nextGen nextEnv flatDecs result := by
  have safe : ∀ last, EvaluateHOL.evaluateDecs source sourceEnv [.dletrec location funs] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply notTypeError
    exact congrArg Prod.snd (sourceRun.symm.trans bad)
  have bound : idxPrev (compileDecs trace n start env gen [.dletrec location funs]).2.1 finish := by
    simpa [compiled] using bounded
  obtain ⟨sourceEq, finalGenv, finalState, flatRun, growth, states, domain, finalEnv,
    finalInvariant, finalGeneration, forward⟩ :=
    evaluateDletrec_factored interp transform genv env sourceEnv trace funs source flat start finish other
      n gen location safe envInv invariant generation bound
  have pairEq := sourceRun.symm.trans sourceEq
  have lastEq : sourceLast = source := congrArg Prod.fst pairEq
  have resultEq : result = .val ⟨SemanticPrimitivesHOL.buildRecEnv funs sourceEnv nsEmpty, nsEmpty⟩ :=
    congrArg Prod.snd pairEq
  subst sourceLast
  subst result
  simp only [compiled] at flatRun domain finalEnv finalInvariant finalGeneration
  refine ⟨finalState, finalGenv, none, flatRun, states, ?_, ?_, ?_⟩
  · intro _
    exact ⟨finalInvariant, forward, growth⟩
  · intro resultEnv same
    cases same
    exact ⟨rfl, domain, finalGeneration, finalEnv⟩
  · intro error impossible
    cases impossible

end Flapjack.Compiler.Backend.SourceToFlat

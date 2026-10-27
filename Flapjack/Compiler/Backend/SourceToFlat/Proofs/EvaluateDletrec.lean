import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateDlet

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
theorem compileFuns_names (trace : List VarN) (env : Environment)
    (funs : List (VarN × VarN × AstHOL.Exp)) :
    (compileFuns trace env funs).map Prod.fst = funs.map Prod.fst := by
  induction funs with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨name, arg, body⟩
    simp [compileFuns, ih]

/-- Replicated empty traces bind exactly the recursive local function names. -/
theorem bindLocals_recNames (env : Environment) (names : List VarN) :
    bindLocals (List.replicate names.length .none) names env.v =
      nsBindList (names.map fun name => (name, VarName.localName .none name)) env.v := by
  unfold bindLocals
  congr 1
  induction names with
  | nil => rfl
  | cons name names ih => simp [List.replicate_succ, ih]

/-- Each source recursive closure corresponds to the flat recursive closure
formed by compiling the entire mutually recursive group. This uses the
preliminary factored value relation and is not a reviewed HOL theorem. -/
theorem dletrec_closure_rel (genv : GlobalEnv) (env : Environment) (sourceEnv : SemEnv Value)
    (trace : List VarN) (funs : List (VarN × VarN × AstHOL.Exp)) (name : VarN)
    (envInv : GlobalEnvInv genv env (fun _ => False) sourceEnv) :
    ValueRel genv (.recclosure sourceEnv funs name)
      (.recclosure ⟨[]⟩ (compileFuns trace
        { env with v := nsBindList ((funs.map Prod.fst).map
          (fun f => (f, VarName.localName .none f))) env.v } funs) name) := by
  have inv : GlobalEnvInv genv env (fun n => n ∈ ([] : List VarN)) sourceEnv := by
    simpa using envInv
  have related := ValueRel.recclosure genv env sourceEnv nsEmpty funs name ⟨[]⟩ trace
    (List.replicate funs.length .none) (.empty genv) inv (by simp)
  have appendEmpty : nsAppend (nsEmpty : Namespace ModN VarN Value) sourceEnv.v = sourceEnv.v := by
    cases sourceEnv.v
    simp [nsEmpty, nsAppend]
  have bindEq := bindLocals_recNames env (funs.map Prod.fst)
  simp only [List.length_map] at bindEq
  dsimp only at related
  simp only [List.map_nil, List.append_nil, bindEq, appendEmpty] at related
  cases sourceEnv
  simpa using related

/-- Any ordered list of names from a recursive group gives related source and
flat closure bindings. Repeated names remain in their original order. -/
theorem dletrec_bindings_rel (genv : GlobalEnv) (env : Environment) (sourceEnv : SemEnv Value)
    (trace : List VarN) (funs : List (VarN × VarN × AstHOL.Exp)) (names : List VarN)
    (envInv : GlobalEnvInv genv env (fun _ => False) sourceEnv) :
    let compiled := compileFuns trace
      { env with v := nsBindList ((funs.map Prod.fst).map
        (fun f => (f, VarName.localName .none f))) env.v } funs
    EnvRel genv (alistToNs (names.map (fun name => (name, Value.recclosure sourceEnv funs name))))
      (names.map (fun name => (name, FlatSem.Value.recclosure ⟨[]⟩ compiled name))) := by
  induction names with
  | nil => simpa [alistToNs, nsEmpty] using EnvRel.empty genv
  | cons name names ih =>
    have head := dletrec_closure_rel genv env sourceEnv trace funs name envInv
    simpa [alistToNs, nsBind] using EnvRel.bind genv name _ _ _ _ ih head

/-- The source and flat recursive-environment builders produce related
bindings for the complete group. This is a factored simulation helper. -/
theorem dletrec_buildEnv_rel (genv : GlobalEnv) (env : Environment) (sourceEnv : SemEnv Value)
    (trace : List VarN) (funs : List (VarN × VarN × AstHOL.Exp))
    (envInv : GlobalEnvInv genv env (fun _ => False) sourceEnv) :
    let compiled := compileFuns trace
      { env with v := nsBindList ((funs.map Prod.fst).map
        (fun f => (f, VarName.localName .none f))) env.v } funs
    EnvRel genv (SemanticPrimitivesHOL.buildRecEnv funs sourceEnv nsEmpty)
      (FlatSem.buildRecEnv compiled ⟨[]⟩ []) := by
  let compiled := compileFuns trace
    { env with v := nsBindList ((funs.map Prod.fst).map
      (fun f => (f, VarName.localName .none f))) env.v } funs
  have sourceShape (xs : List (VarN × VarN × AstHOL.Exp)) :
      xs.foldr (fun (name, _, _) rest => nsBind name (.recclosure sourceEnv funs name) rest)
        (nsEmpty : Namespace ModN VarN Value) =
        alistToNs ((xs.map Prod.fst).map (fun name => (name, Value.recclosure sourceEnv funs name))) := by
    induction xs with
    | nil => rfl
    | cons pair rest ih =>
      rcases pair with ⟨name, arg, body⟩
      simp only [List.foldr_cons, List.map_cons]
      rw [ih]
      rfl
  have flatShape (xs : List (VarN × VarN × FlatLang.Exp)) :
      xs.foldr (fun (name, _, _) rest => (name, FlatSem.Value.recclosure ⟨[]⟩ compiled name) :: rest) [] =
        (xs.map Prod.fst).map (fun name => (name, FlatSem.Value.recclosure ⟨[]⟩ compiled name)) := by
    induction xs with
    | nil => rfl
    | cons pair rest ih =>
      rcases pair with ⟨name, arg, body⟩
      simp [ih]
  change EnvRel genv (SemanticPrimitivesHOL.buildRecEnv funs sourceEnv nsEmpty)
    (FlatSem.buildRecEnv compiled ⟨[]⟩ [])
  rw [SemanticPrimitivesHOL.buildRecEnv, sourceShape, FlatSem.buildRecEnv, flatShape]
  have names : compiled.map Prod.fst = funs.map Prod.fst := by
    exact compileFuns_names trace _ funs
  rw [names]
  exact dletrec_bindings_rel genv env sourceEnv trace funs (funs.map Prod.fst) envInv

/-- The flat recursive environment contains closures in source-name order. -/
theorem dletrec_flatEnv (env : Environment) (trace : List VarN)
    (funs : List (VarN × VarN × AstHOL.Exp)) :
    let compiled := compileFuns trace
      { env with v := nsBindList ((funs.map Prod.fst).map
        (fun f => (f, VarName.localName .none f))) env.v } funs
    FlatSem.buildRecEnv compiled ⟨[]⟩ [] =
      (funs.map Prod.fst).map (fun name => (name, FlatSem.Value.recclosure ⟨[]⟩ compiled name)) := by
  let compiled := compileFuns trace
    { env with v := nsBindList ((funs.map Prod.fst).map
      (fun f => (f, VarName.localName .none f))) env.v } funs
  have shape (xs : List (VarN × VarN × FlatLang.Exp)) :
      xs.foldr (fun (name, _, _) rest => (name, FlatSem.Value.recclosure ⟨[]⟩ compiled name) :: rest) [] =
        (xs.map Prod.fst).map (fun name => (name, FlatSem.Value.recclosure ⟨[]⟩ compiled name)) := by
    induction xs with
    | nil => rfl
    | cons pair rest ih =>
      rcases pair with ⟨name, arg, body⟩
      simp [ih]
  change FlatSem.buildRecEnv compiled ⟨[]⟩ [] = _
  rw [FlatSem.buildRecEnv, shape]
  rw [show compiled.map Prod.fst = funs.map Prod.fst from compileFuns_names trace _ funs]

/-- The source recursive environment contains closures in source-name order. -/
theorem dletrec_sourceEnv (sourceEnv : SemEnv Value) (funs : List (VarN × VarN × AstHOL.Exp)) :
    SemanticPrimitivesHOL.buildRecEnv funs sourceEnv nsEmpty =
      alistToNs ((funs.map Prod.fst).map (fun name => (name, Value.recclosure sourceEnv funs name))) := by
  have shape (xs : List (VarN × VarN × AstHOL.Exp)) :
      xs.foldr (fun (name, _, _) rest => nsBind name (.recclosure sourceEnv funs name) rest)
        (nsEmpty : Namespace ModN VarN Value) =
        alistToNs ((xs.map Prod.fst).map (fun name => (name, Value.recclosure sourceEnv funs name))) := by
    induction xs with
    | nil => rfl
    | cons pair rest ih =>
      rcases pair with ⟨name, arg, body⟩
      simp only [List.foldr_cons, List.map_cons]
      rw [ih]
      rfl
  exact shape funs

private theorem lookup_exists_iff_key_mem {α : Type} (entries : List (VarN × α)) (name : VarN) :
    (∃ value, entries.lookup name = some value) ↔ name ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
    obtain ⟨key, value⟩ := entry
    by_cases equal : name = key
    · subst key
      simp
    · simp [List.lookup_cons, BEq.beq, equal, ih]

private theorem allocDefs_keys (names : List VarN) (n base : Nat) :
    (allocDefs n base names).map Prod.fst = names := by
  induction names generalizing n base with
  | nil => rfl
  | cons name names ih => simp [allocDefs, ih]

/-- The compiled recursive group and source recursive environment have the
same value and module domains. -/
theorem dletrec_envDomainEq (env : Environment) (sourceEnv : SemEnv Value) (trace : List VarN)
    (n : Nat) (start : NextIndices) (gen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (funs : List (VarN × VarN × AstHOL.Exp)) :
    EnvDomainEq (compileDecs trace n start env gen [.dletrec location funs]).2.2.1
      ⟨SemanticPrimitivesHOL.buildRecEnv funs sourceEnv nsEmpty, nsEmpty⟩ := by
  simp only [compileDecs, dletrec_sourceEnv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext id
    apply propext
    cases id with
    | short name =>
      simp only [nsDom, alistToNs, nsLookup]
      rw [lookup_exists_iff_key_mem, lookup_exists_iff_key_mem, allocDefs_keys]
      simp [List.map_map, Function.comp_def]
    | long moduleName id => simp [nsDom, alistToNs, nsLookup]
  · funext path
    apply propext
    cases path <;> simp [nsDomMod, alistToNs, nsLookupMod]
  · funext id
    apply propext
    cases id <;> simp [nsDom, nsLookup, nsEmpty]
  · funext path
    apply propext
    cases path <;> simp [nsDomMod, nsLookupMod, nsEmpty]

/-- Recursive closures initialize their reserved globals and produce a
related compiler environment. The complete declaration invariant and flat
`letrec` execution remain separate obligations. -/
theorem dletrec_initialize {C F R : Type}
    (interp : Option (Value → Option (Config × R))) (genv : GlobalEnv)
    (env : Environment) (sourceEnv : SemEnv Value) (trace : List VarN)
    (funs : List (VarN × VarN × AstHOL.Exp))
    (envInv : GlobalEnvInv genv env (fun _ => False) sourceEnv)
    (distinct : (funs.map Prod.fst).Nodup)
    (sourceState : State F) (flatState : FlatSem.State C F)
    (stateRel : StateRel genv sourceState flatState) (globals : flatState.globals = genv.v)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (range : idxRangeRel interp genv sourceState.nextTypeStamp sourceState.nextExnStamp
      sourceState.evalState (start, finish, other))
    (lengthMatch : finIdxMatch genv.v.length finish (srcOracNextCfg interp sourceState.evalState))
    (fits : funs.length + start.vidx ≤ finish.vidx) :
    let compiled := compileFuns trace
      { env with v := nsBindList ((funs.map Prod.fst).map
        (fun f => (f, VarName.localName .none f))) env.v } funs
    let sourceBindings := (funs.map Prod.fst).map (fun name => (name, Value.recclosure sourceEnv funs name))
    let flatBindings := (funs.map Prod.fst).map (fun name => (name, FlatSem.Value.recclosure ⟨[]⟩ compiled name))
    ∃ pre post, pre.length = start.vidx ∧
      flatState.globals = pre ++ (List.replicate flatBindings.length none ++ post) ∧
      let finalSlots := pre ++ (flatBindings.reverse.map Prod.snd |>.map some) ++ post
      let finalEnv := { genv with v := finalSlots }
      let finalState := { flatState with globals := finalSlots }
      FlatSem.evaluate ⟨flatBindings⟩ flatState
        [makeVarls 0 .none start.vidx (flatBindings.reverse.map Prod.fst)] =
          (finalState, .val [FlatSem.unitValue]) ∧
      GlobalGrowth genv finalEnv ∧ StateRel finalEnv sourceState finalState ∧
      GlobalEnvInv finalEnv
        { emptyEnv with v := alistToNs (allocDefs 0 start.vidx (flatBindings.reverse.map Prod.fst)) }
        (fun _ => False) ⟨alistToNs sourceBindings, nsEmpty⟩ := by
  let sourceBindings := (funs.map Prod.fst).map (fun name => (name, Value.recclosure sourceEnv funs name))
  let compiled := compileFuns trace
    { env with v := nsBindList ((funs.map Prod.fst).map
      (fun f => (f, VarName.localName .none f))) env.v } funs
  let flatBindings := (funs.map Prod.fst).map (fun name => (name, FlatSem.Value.recclosure ⟨[]⟩ compiled name))
  have related : EnvRel genv (alistToNs sourceBindings) flatBindings :=
    dletrec_bindings_rel genv env sourceEnv trace funs (funs.map Prod.fst) envInv
  have nodup : (sourceBindings.map Prod.fst).Nodup := by
    simpa [sourceBindings, List.map_map, Function.comp_def] using distinct
  have bound : flatBindings.length + start.vidx ≤ finish.vidx := by simpa [flatBindings] using fits
  simpa [sourceBindings, flatBindings, compiled, List.append_assoc] using
    evaluate_makeVarls_idxRange interp genv sourceBindings flatBindings related nodup sourceState flatState
      stateRel globals start finish other range lengthMatch bound 0 .none

/-- The compiled recursive declaration executes its generated initializer
in the environment of all compiled recursive closures. -/
theorem evaluateDletrec_flat {C F : Type} (flat final : FlatSem.State C F)
    (trace : List VarN) (n : Nat) (start : NextIndices) (env : Environment)
    (gen : EnvironmentGenerationStore) (location : Flapjack.Misc.Location.Locs)
    (funs : List (VarN × VarN × AstHOL.Exp))
    (distinct : (funs.map Prod.fst).Nodup)
    (run : let compiled := (compileFuns trace
          { env with v := nsBindList ((funs.map Prod.fst).map
            (fun f => (f, VarName.localName .none f))) env.v } funs)
      FlatSem.evaluate ⟨FlatSem.buildRecEnv compiled ⟨[]⟩ []⟩ flat
        [makeVarls 0 .none start.vidx (funs.map Prod.fst).reverse] =
        (final, .val [FlatSem.unitValue]))
    (clock : final.clock = flat.clock) :
    FlatSem.evaluateDecs flat (compileDecs trace n start env gen [.dletrec location funs]).2.2.2.2 =
      (final, none) := by
  simp only [compileDecs, FlatSem.evaluateDecs, FlatSem.evaluate, compileFuns_names, distinct, if_true]
  rw [run]
  cases final
  simp_all [FlatSem.fixClock, FlatSem.unitValue]

/-- Executing the compiled recursive declaration fills its reserved slots
with related recursive closures. This does not yet establish the full
factored invariant after initialization. -/
theorem evaluateDletrec_initialized {C F R : Type}
    (interp : Option (Value → Option (Config × R))) (genv : GlobalEnv)
    (env : Environment) (sourceEnv : SemEnv Value) (trace : List VarN)
    (funs : List (VarN × VarN × AstHOL.Exp))
    (envInv : GlobalEnvInv genv env (fun _ => False) sourceEnv)
    (distinct : (funs.map Prod.fst).Nodup)
    (wellformed : funs.all (fun (_, _, expr) => everyExp (oneConCheck sourceEnv.c) expr) = true)
    (sourceState : State F) (flatState : FlatSem.State C F)
    (stateRel : StateRel genv sourceState flatState) (globals : flatState.globals = genv.v)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (range : idxRangeRel interp genv sourceState.nextTypeStamp sourceState.nextExnStamp
      sourceState.evalState (start, finish, other))
    (lengthMatch : finIdxMatch genv.v.length finish (srcOracNextCfg interp sourceState.evalState))
    (fits : funs.length + start.vidx ≤ finish.vidx)
    (n : Nat) (gen : EnvironmentGenerationStore) (location : Flapjack.Misc.Location.Locs) :
    EvaluateHOL.evaluateDecs sourceState sourceEnv [.dletrec location funs] =
      (sourceState, .val ⟨SemanticPrimitivesHOL.buildRecEnv funs sourceEnv nsEmpty, nsEmpty⟩) ∧
    ∃ finalGenv finalState,
      FlatSem.evaluateDecs flatState (compileDecs trace n start env gen [.dletrec location funs]).2.2.2.2 =
        (finalState, none) ∧
      GlobalGrowth genv finalGenv ∧ StateRel finalGenv sourceState finalState ∧
      GlobalEnvInv finalGenv (compileDecs trace n start env gen [.dletrec location funs]).2.2.1
        (fun _ => False) ⟨SemanticPrimitivesHOL.buildRecEnv funs sourceEnv nsEmpty, nsEmpty⟩ := by
  constructor
  · simp [EvaluateHOL.evaluateDecs, distinct, wellformed]
  let compiled := compileFuns trace
    { env with v := nsBindList ((funs.map Prod.fst).map
      (fun f => (f, VarName.localName .none f))) env.v } funs
  let flatBindings := (funs.map Prod.fst).map (fun name => (name, FlatSem.Value.recclosure ⟨[]⟩ compiled name))
  obtain ⟨pre, post, _, _, run, growth, states, envResult⟩ :=
    dletrec_initialize interp genv env sourceEnv trace funs envInv distinct sourceState flatState
      stateRel globals start finish other range lengthMatch fits
  let slots := pre ++ (flatBindings.reverse.map Prod.snd).map some ++ post
  let finalState := { flatState with globals := slots }
  let finalGenv := { genv with v := slots }
  have nameShape : flatBindings.reverse.map Prod.fst = (funs.map Prod.fst).reverse := by
    simp [flatBindings, List.map_reverse, List.map_map, Function.comp_def]
  have flatEnv : FlatSem.buildRecEnv compiled ⟨[]⟩ [] = flatBindings :=
    dletrec_flatEnv env trace funs
  have bodyRun : FlatSem.evaluate ⟨FlatSem.buildRecEnv compiled ⟨[]⟩ []⟩ flatState
      [makeVarls 0 .none start.vidx (funs.map Prod.fst).reverse] =
        (finalState, .val [FlatSem.unitValue]) := by
    simpa only [flatEnv, ← nameShape] using run
  refine ⟨finalGenv, finalState, ?_, growth, states, ?_⟩
  · exact evaluateDletrec_flat flatState finalState trace n start env gen location funs distinct bodyRun rfl
  · simpa only [compileDecs, dletrec_sourceEnv, ← nameShape, emptyEnv, finalGenv, slots,
      flatBindings, compiled, allocDefs_ignoreCounter _ (n + 1) 0 start.vidx] using envResult

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
  have invariantCopy := invariant
  obtain ⟨_, _, states, range, _, _, globals, _, _, fin⟩ := invariantCopy
  let compiled := compileFuns trace
    { env with v := nsBindList ((funs.map Prod.fst).map
      (fun f => (f, VarName.localName .none f))) env.v } funs
  let flatBindings := (funs.map Prod.fst).map (fun name => (name, FlatSem.Value.recclosure ⟨[]⟩ compiled name))
  obtain ⟨pre, post, prefixLength, slots, run, growth, stateResult, envResult⟩ :=
    dletrec_initialize interp genv env sourceEnv trace funs envInv distinct sourceState flatState
      states globals.symm start finish other range (by simpa [globals] using fin) fits
  let finalSlots := pre ++ (flatBindings.reverse.map Prod.snd).map some ++ post
  let finalState := { flatState with globals := finalSlots }
  let finalGenv := { genv with v := finalSlots }
  have nameShape : flatBindings.reverse.map Prod.fst = (funs.map Prod.fst).reverse := by
    simp [flatBindings, List.map_reverse, List.map_map, Function.comp_def]
  have flatEnv : FlatSem.buildRecEnv compiled ⟨[]⟩ [] = flatBindings := dletrec_flatEnv env trace funs
  have bodyRun : FlatSem.evaluate ⟨FlatSem.buildRecEnv compiled ⟨[]⟩ []⟩ flatState
      [makeVarls 0 .none start.vidx (funs.map Prod.fst).reverse] =
        (finalState, .val [FlatSem.unitValue]) := by
    simpa only [flatEnv, ← nameShape] using run
  have finalInv := factoredInvariant_fillBlock interp transform gen genv start finish other sourceState flatState
    (flatBindings.reverse.map Prod.snd) pre post invariant (by simpa [flatBindings] using slots) prefixLength
    (by simpa [flatBindings, Nat.add_comm] using fits)
  constructor
  · simp [EvaluateHOL.evaluateDecs, distinct, wellformed]
  refine ⟨finalGenv, finalState, ?_, growth, stateResult,
    dletrec_envDomainEq env sourceEnv trace n start gen location funs, ?_, ?_, ?_, oracForwardRel_refl interp _⟩
  · exact evaluateDletrec_flat flatState finalState trace n start env gen location funs distinct bodyRun rfl
  · simpa only [compileDecs, dletrec_sourceEnv, ← nameShape, emptyEnv, finalGenv, finalSlots,
      flatBindings, compiled, allocDefs_ignoreCounter _ (n + 1) 0 start.vidx] using envResult
  · simpa [compileDecs, finalGenv, finalState, finalSlots, flatBindings, compiled, List.append_assoc] using finalInv
  · simpa [compileDecs] using generation

end Flapjack.Compiler.Backend.SourceToFlat

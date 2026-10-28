import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalEnvironment
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRelCases

/-! Function-call prerequisites over the factored source-to-flat relations.
These lemmas remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Decrementing both evaluator clocks preserves the factored invariant.
This is used before entering a function body. -/
theorem factoredInvariant_decClock {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F)
    (invariant : factoredInvariant interp transform gen genv idxs source flat) :
    factoredInvariant interp transform gen genv idxs (EvaluateHOL.decClock source) (FlatSem.decClock flat) := by
  obtain ⟨cOk, tysOk, states, range, invs, orac, globals, reserved, genInv, fin⟩ := invariant
  have decStates : StateRel genv (EvaluateHOL.decClock source) (FlatSem.decClock flat) := by
    cases states with
    | intro nonempty refs clock ffi =>
      exact .intro _ _ nonempty refs (by simp [EvaluateHOL.decClock, FlatSem.decClock, clock]) ffi
  exact ⟨cOk, tysOk, decStates, range, invs, orac, globals, reserved, genInv, fin⟩

/-- Looking up a compiled recursive function preserves its name and argument
and compiles its body under the same recursive environment. -/
theorem findRecFun_compileFuns (name : VarN) (trace : List VarN) (env : Environment)
    (funs : List (VarN × VarN × AstHOL.Exp)) :
    findRecFun name (compileFuns trace env funs) =
      (findRecFun name funs).map (fun (arg, body) =>
        (arg, compileExp (name :: trace) { env with v := nsBind arg (.localName .none arg) env.v } body)) := by
  induction funs with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨fn, arg, body⟩ := head
    by_cases eq : fn = name
    · subst fn
      simp [compileFuns, findRecFun]
    · simp [compileFuns, findRecFun, eq, ih]

/-- Calling related non-recursive closures creates related argument
bindings and compiles the function body under the extended local traces. -/
theorem doOpApp_closure_local (genv : GlobalEnv)
    (sourceEnv : SemEnv Value) (name : VarN) (body : AstHOL.Exp) (flatClosure : FlatSem.Value)
    (argument : Value) (flatArgument : FlatSem.Value)
    (closureRel : ValueRel genv (.closure sourceEnv name body) flatClosure)
    (argumentRel : ValueRel genv argument flatArgument) :
    ∃ (baseMap : Environment) (baseEnv : SemEnv Value) (sourceLocal : Namespace ModN VarN Value)
      (flatEnv : FlatSem.Environment FlatSem.Value) (trace : List VarN) (traces : List BackendCommon.Tra),
      doOpApp [.closure sourceEnv name body, argument] =
        some ({ baseEnv with v := nsAppend sourceLocal baseEnv.v }, body) ∧
      FlatSem.doOpApp [flatClosure, flatArgument] =
        some (flatEnv, compileExp trace { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v } body) ∧
      EnvRel genv sourceLocal flatEnv.v ∧
      GlobalEnvInv genv baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv ∧
      traces.length = flatEnv.v.length := by
  obtain ⟨baseMap, baseEnv, captured, flatCaptured, trace, traces, sourceEq, flatEq, locals, globals, len⟩ :=
    (valueRel_closure_iff genv sourceEnv name body flatClosure).mp closureRel
  cases traces with
  | nil => simp at len
  | cons head rest =>
    have extendedRel := EnvRel.bind genv name argument captured flatCaptured.v flatArgument locals argumentRel
    have extendedInv : GlobalEnvInv genv baseMap
        (fun n => n ∈ ((name, flatArgument) :: flatCaptured.v).map Prod.fst) baseEnv := by
      cases globals with
      | intro _ _ _ values constructors =>
        apply GlobalEnvInv.intro
        · intro id value fresh lookup
          apply values id value _ lookup
          intro ⟨n, mem, eq⟩
          apply fresh
          exact ⟨n, by simp [mem], eq⟩
        · exact constructors
    refine ⟨baseMap, baseEnv, nsBind name argument captured,
      { flatCaptured with v := (name, flatArgument) :: flatCaptured.v }, trace, head :: rest, ?_, ?_, extendedRel, extendedInv, ?_⟩
    · rw [sourceEq]
      cases captured
      cases baseEnv.v
      rfl
    · rw [flatEq]
      rfl
    · simpa using len
/-- Calling a related local recursive closure reinstalls the related
recursive group and its argument. This covers the local recursive-closure
case; the separate top-level recursive representation remains open. -/
theorem doOpApp_recclosure_local (genv : GlobalEnv) (baseMap : Environment) (baseEnv : SemEnv Value)
    (captured : Namespace ModN VarN Value) (flatCaptured : FlatSem.Environment FlatSem.Value)
    (funs : List (VarN × VarN × AstHOL.Exp)) (name arg : VarN) (body : AstHOL.Exp)
    (trace : List VarN) (traces : List BackendCommon.Tra)
    (locals : EnvRel genv captured flatCaptured.v)
    (globals : GlobalEnvInv genv baseMap (fun n => n ∈ flatCaptured.v.map Prod.fst) baseEnv)
    (len : traces.length = funs.length + flatCaptured.v.length)
    (distinct : (funs.map Prod.fst).Nodup) (found : findRecFun name funs = some (arg, body))
    (argument : Value) (flatArgument : FlatSem.Value) (argumentRel : ValueRel genv argument flatArgument) :
    let sourceEnv := { baseEnv with v := nsAppend captured baseEnv.v }
    let recMap := { baseMap with v := bindLocals traces (funs.map Prod.fst ++ flatCaptured.v.map Prod.fst) baseMap.v }
    let compiled := compileFuns trace recMap funs
    let sourceLocal := nsBind arg argument (buildRecEnv funs sourceEnv captured)
    let flatLocal := (arg, flatArgument) :: FlatSem.buildRecEnv compiled flatCaptured flatCaptured.v
    doOpApp [.recclosure sourceEnv funs name, argument] =
      some ({ baseEnv with v := nsAppend sourceLocal baseEnv.v }, body) ∧
    FlatSem.doOpApp [.recclosure flatCaptured compiled name, flatArgument] =
      some ({ flatCaptured with v := flatLocal },
        compileExp (name :: trace) { baseMap with v := bindLocals (.none :: traces) (flatLocal.map Prod.fst) baseMap.v } body) ∧
    EnvRel genv sourceLocal flatLocal ∧
    GlobalEnvInv genv baseMap (fun n => n ∈ flatLocal.map Prod.fst) baseEnv ∧
    (.none :: traces).length = flatLocal.length := by
  dsimp only
  let sourceEnv := { baseEnv with v := nsAppend captured baseEnv.v }
  let recMap := { baseMap with v := bindLocals traces (funs.map Prod.fst ++ flatCaptured.v.map Prod.fst) baseMap.v }
  let compiled := compileFuns trace recMap funs
  let recursiveLocal := buildRecEnv funs sourceEnv captured
  let recursiveFlat := FlatSem.buildRecEnv compiled flatCaptured flatCaptured.v
  have names : recursiveFlat.map Prod.fst = funs.map Prod.fst ++ flatCaptured.v.map Prod.fst := by
    simp [recursiveFlat, compiled, flatBuildRecEnv_names, compileFuns_local_names]
  have recursiveRel : EnvRel genv recursiveLocal recursiveFlat := by
    exact localRecEnv_related genv baseMap baseEnv captured flatCaptured funs trace traces locals globals len
  have newInv : GlobalEnvInv genv baseMap (fun n => n ∈ ((arg, flatArgument) :: recursiveFlat).map Prod.fst) baseEnv := by
    cases globals with
    | intro _ _ _ values constructors =>
      apply GlobalEnvInv.intro
      · intro id value fresh lookup
        apply values id value _ lookup
        intro ⟨n, mem, eq⟩
        apply fresh
        exact ⟨n, by simp [names, mem], eq⟩
      · exact constructors
  have sourceBind : nsAppend (nsBind arg argument recursiveLocal) baseEnv.v =
      nsBind arg argument (buildRecEnv funs sourceEnv sourceEnv.v) := by
    have recBind : buildRecEnv funs sourceEnv sourceEnv.v = nsAppend recursiveLocal baseEnv.v := by
      simpa [sourceEnv, recursiveLocal] using buildRecEnv_nsAppend funs sourceEnv captured baseEnv.v
    rw [recBind]
    cases recursiveLocal
    cases baseEnv.v
    rfl
  have compiledFound : findRecFun name compiled = some (arg,
      compileExp (name :: trace) { recMap with v := nsBind arg (.localName .none arg) recMap.v } body) := by
    simp [compiled, findRecFun_compileFuns, found]
  have flatDistinct : (compiled.map Prod.fst).Nodup := by simpa [compiled, compileFuns_local_names] using distinct
  have mapBind : bindLocals (.none :: traces) (((arg, flatArgument) :: recursiveFlat).map Prod.fst) baseMap.v =
      nsBind arg (.localName .none arg) recMap.v := by
    simp [names, recMap, bindLocals, nsBindList]
  refine ⟨?_, ?_, EnvRel.bind genv arg argument recursiveLocal recursiveFlat flatArgument recursiveRel argumentRel, newInv, ?_⟩
  · simp [doOpApp, distinct, found, ← sourceBind, sourceEnv, recursiveLocal]
  · simp [FlatSem.doOpApp, flatDistinct, compiledFound, ← mapBind, recursiveFlat, compiled, recMap]
  · have flatLength : recursiveFlat.length = funs.length + flatCaptured.v.length := by
      have h := congrArg List.length names
      simpa using h
    change Nat.succ traces.length = Nat.succ recursiveFlat.length
    simp [flatLength, len]

/-- A recursive binding lookup depends only on membership in the group. -/
theorem lookup_recursive_bindings (sourceEnv : SemEnv Value)
    (funs : List (VarN × VarN × AstHOL.Exp)) (names : List VarN) (name : VarN) :
    (names.map (fun x => (x, Value.recclosure sourceEnv funs x))).lookup name =
      if name ∈ names then some (.recclosure sourceEnv funs name) else none := by
  induction names with
  | nil => simp
  | cons head tail ih =>
    by_cases eq : name = head
    · subst head
      simp
    · simp [List.lookup_cons, BEq.beq, eq, ih]

/-- An association list has a value at exactly its listed keys. -/
theorem lookup_key_exists {α : Type} (entries : List (VarN × α)) (name : VarN) :
    (∃ value, entries.lookup name = some value) ↔ name ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp
  | cons entry tail ih =>
    obtain ⟨key, value⟩ := entry
    by_cases eq : name = key
    · subst key
      simp
    · simp [List.lookup_cons, BEq.beq, eq, ih]

/-- Installing a binding list is namespace append with its association list. -/
theorem nsBindList_eq_nsAppend {α : Type} (entries : List (VarN × α)) (env : Namespace ModN VarN α) :
    nsBindList entries env = nsAppend (alistToNs entries) env := by
  cases env with
  | bind values modules =>
    induction entries with
    | nil => rfl
    | cons entry tail ih =>
      obtain ⟨name, value⟩ := entry
      simp only [nsBindList, List.foldr_cons] at ih ⊢
      rw [ih]
      rfl

/-- Every global slot in a top-level recursive group contains a closure
related to the corresponding source recursive closure. -/
theorem topRec_group_slot_related (genv : GlobalEnv) (baseMap : Environment) (sourceEnv : SemEnv Value)
    (funs : List (VarN × VarN × AstHOL.Exp)) (flatEnv : FlatSem.Environment FlatSem.Value)
    (newVars : List (VarN × VarName))
    (names : newVars.map Prod.fst = funs.reverse.map Prod.fst)
    (globals : GlobalEnvInv genv baseMap (fun _ => False) sourceEnv) (empty : flatEnv.v = [])
    (closures : ∀ x, x ∈ funs.map Prod.fst → ∃ n y e storedTrace bodyTrace localTrace,
      newVars.lookup x = some (.glob storedTrace n) ∧ n < genv.v.length ∧
      findRecFun x funs = some (y, e) ∧
      genv.v[n]?.getD none = some (.closure flatEnv y
        (compileExp bodyTrace { baseMap with v := nsBindList ((y, .localName localTrace y) :: newVars) baseMap.v } e)))
    (name : VarN) (member : name ∈ funs.map Prod.fst) :
    ∃ n storedTrace flatValue, newVars.lookup name = some (.glob storedTrace n) ∧
      n < genv.v.length ∧ genv.v[n]?.getD none = some flatValue ∧
      ValueRel genv (.recclosure sourceEnv funs name) flatValue := by
  obtain ⟨n, arg, body, storedTrace, bodyTrace, argTrace, lookup, bound, found, slot⟩ := closures name member
  refine ⟨n, storedTrace, _, lookup, bound, slot, ?_⟩
  exact .topRecclosure genv baseMap sourceEnv funs flatEnv name arg body newVars bodyTrace argTrace
    names globals empty found closures

/-- The global slots of a top-level recursive group establish the global
invariant for the rebuilt source environment and the extended compiler map. -/
theorem topRec_rebuilt_globalInv (genv : GlobalEnv) (baseMap : Environment) (sourceEnv : SemEnv Value)
    (funs : List (VarN × VarN × AstHOL.Exp)) (flatEnv : FlatSem.Environment FlatSem.Value)
    (newVars : List (VarN × VarName))
    (names : newVars.map Prod.fst = funs.reverse.map Prod.fst)
    (globals : GlobalEnvInv genv baseMap (fun _ => False) sourceEnv) (empty : flatEnv.v = [])
    (closures : ∀ x, x ∈ funs.map Prod.fst → ∃ n y e storedTrace bodyTrace localTrace,
      newVars.lookup x = some (.glob storedTrace n) ∧ n < genv.v.length ∧
      findRecFun x funs = some (y, e) ∧
      genv.v[n]?.getD none = some (.closure flatEnv y
        (compileExp bodyTrace { baseMap with v := nsBindList ((y, .localName localTrace y) :: newVars) baseMap.v } e))) :
    GlobalEnvInv genv { baseMap with v := nsBindList newVars baseMap.v } (fun _ => False)
      { sourceEnv with v := buildRecEnv funs sourceEnv sourceEnv.v } := by
  have sourceShape : buildRecEnv funs sourceEnv sourceEnv.v =
      nsAppend (alistToNs ((funs.map Prod.fst).map (fun x => (x, Value.recclosure sourceEnv funs x)))) sourceEnv.v := by
    have h := buildRecEnv_nsAppend funs sourceEnv nsEmpty sourceEnv.v
    have emptyAppend : nsAppend (nsEmpty : Namespace ModN VarN Value) sourceEnv.v = sourceEnv.v := by
      cases sourceEnv.v
      rfl
    rw [emptyAppend, dletrec_sourceEnv] at h
    exact h
  cases globals with
  | intro _ _ _ values constructors =>
    apply GlobalEnvInv.intro
    · intro id value _ lookup
      cases id with
      | short name =>
        by_cases member : name ∈ funs.map Prod.fst
        · have sourceFound : nsLookup (buildRecEnv funs sourceEnv sourceEnv.v) (.short name) =
              some (.recclosure sourceEnv funs name) := by
            rw [sourceShape, nsLookup_append_short]
            change (((funs.map Prod.fst).map (fun x => (x, Value.recclosure sourceEnv funs x))).lookup name).orElse (fun _ => nsLookup sourceEnv.v (.short name)) = some (.recclosure sourceEnv funs name)
            rw [lookup_recursive_bindings]
            simp [member]
          change nsLookup (buildRecEnv funs sourceEnv sourceEnv.v) (.short name) = some value at lookup
          rw [sourceFound] at lookup
          cases lookup
          have originalInv : GlobalEnvInv genv baseMap (fun _ => False) sourceEnv := .intro genv baseMap _ sourceEnv values constructors
          obtain ⟨n, storedTrace, flatValue, found, bound, slot, related⟩ :=
            topRec_group_slot_related genv baseMap sourceEnv funs flatEnv newVars names originalInv empty closures name member
          apply GlobalLookupRel.intro genv _ (.short name) _ n flatValue storedTrace _ bound slot related
          rw [nsBindList_eq_nsAppend, nsLookup_append_short]
          simp [alistToNs, nsLookup, found]
        · have absent : newVars.lookup name = none := by
            cases found : newVars.lookup name with
            | none => rfl
            | some item =>
              have key := (lookup_key_exists newVars name).mp ⟨item, found⟩
              rw [names] at key
              simp only [List.map_reverse, List.mem_reverse] at key
              exact (member key).elim
          have baseLookup : nsLookup sourceEnv.v (.short name) = some value := by
            change nsLookup (buildRecEnv funs sourceEnv sourceEnv.v) (.short name) = some value at lookup
            rw [sourceShape, nsLookup_append_short] at lookup
            change (((funs.map Prod.fst).map (fun x => (x, Value.recclosure sourceEnv funs x))).lookup name).orElse (fun _ => nsLookup sourceEnv.v (.short name)) = some value at lookup
            rw [lookup_recursive_bindings] at lookup
            simpa [member] using lookup
          have rel := values (.short name) value (by simp) baseLookup
          cases rel with
          | intro _ _ _ n flatValue trace found bound slot related =>
            apply GlobalLookupRel.intro genv _ (.short name) value n flatValue trace _ bound slot related
            rw [nsBindList_eq_nsAppend, nsLookup_append_short]
            simpa [alistToNs, nsLookup, absent] using found
      | long moduleName rest =>
        have baseLookup : nsLookup sourceEnv.v (.long moduleName rest) = some value := by
          change nsLookup (buildRecEnv funs sourceEnv sourceEnv.v) (.long moduleName rest) = some value at lookup
          simpa [sourceShape, nsLookup_append_long, alistToNs, nsLookupMod] using lookup
        have rel := values (.long moduleName rest) value (by simp) baseLookup
        cases rel with
        | intro _ _ _ n flatValue trace found bound slot related =>
          apply GlobalLookupRel.intro genv _ (.long moduleName rest) value n flatValue trace _ bound slot related
          rw [nsBindList_eq_nsAppend, nsLookup_append_long]
          simpa [alistToNs, nsLookupMod] using found
    · exact constructors

/-- A source top-level recursive closure related to a flat ordinary closure
selects the same function body and argument. The retained global-slot
hypothesis is needed to relate the rebuilt recursive environment before
simulating the body. -/
theorem doOpApp_topRecclosure_setup (genv : GlobalEnv) (sourceEnv : SemEnv Value)
    (funs : List (VarN × VarN × AstHOL.Exp)) (name : VarN)
    (flatEnv : FlatSem.Environment FlatSem.Value) (arg : VarN) (flatBody : FlatLang.Exp)
    (argument : Value) (flatArgument : FlatSem.Value)
    (closureRel : ValueRel genv (.recclosure sourceEnv funs name) (.closure flatEnv arg flatBody))
    (distinct : (funs.map Prod.fst).Nodup) :
    ∃ (baseMap : Environment) (body : AstHOL.Exp) (newVars : List (VarN × VarName))
      (trace : List VarN) (argTrace : BackendCommon.Tra),
      newVars.map Prod.fst = funs.reverse.map Prod.fst ∧
      GlobalEnvInv genv baseMap (fun _ => False) sourceEnv ∧ flatEnv.v = [] ∧
      findRecFun name funs = some (arg, body) ∧
      (∀ x, x ∈ funs.map Prod.fst → ∃ n y e storedTrace bodyTrace localTrace,
        newVars.lookup x = some (.glob storedTrace n) ∧ n < genv.v.length ∧
        findRecFun x funs = some (y, e) ∧
        genv.v[n]?.getD none = some (.closure flatEnv y
          (compileExp bodyTrace { baseMap with v := nsBindList ((y, .localName localTrace y) :: newVars) baseMap.v } e))) ∧
      doOpApp [.recclosure sourceEnv funs name, argument] =
        some ({ sourceEnv with v := nsBind arg argument (buildRecEnv funs sourceEnv sourceEnv.v) }, body) ∧
      FlatSem.doOpApp [.closure flatEnv arg flatBody, flatArgument] =
        some ({ flatEnv with v := [(arg, flatArgument)] },
          compileExp trace { baseMap with v := nsBindList ((arg, .localName argTrace arg) :: newVars) baseMap.v } body) := by
  cases closureRel with
  | topRecclosure =>
    rename_i baseMap body newVars trace argTrace globals names empty closures found
    refine ⟨baseMap, body, newVars, trace, argTrace, names, globals, empty, found, closures, ?_, ?_⟩
    · simp [doOpApp, distinct, found]
    · simp [FlatSem.doOpApp, empty]

/-- Calling a top-level recursive closure establishes the same local and
global invariants as an ordinary closure call. -/
theorem doOpApp_topRecclosure_local (genv : GlobalEnv) (sourceEnv : SemEnv Value)
    (funs : List (VarN × VarN × AstHOL.Exp)) (name : VarN)
    (flatEnv : FlatSem.Environment FlatSem.Value) (arg : VarN) (flatBody : FlatLang.Exp)
    (argument : Value) (flatArgument : FlatSem.Value)
    (closureRel : ValueRel genv (.recclosure sourceEnv funs name) (.closure flatEnv arg flatBody))
    (argumentRel : ValueRel genv argument flatArgument) (distinct : (funs.map Prod.fst).Nodup) :
    ∃ (baseMap : Environment) (baseEnv : SemEnv Value) (sourceLocal : Namespace ModN VarN Value)
      (flatLocal : FlatSem.Environment FlatSem.Value) (trace : List VarN) (traces : List BackendCommon.Tra)
      (body : AstHOL.Exp),
      doOpApp [.recclosure sourceEnv funs name, argument] =
        some ({ baseEnv with v := nsAppend sourceLocal baseEnv.v }, body) ∧
      FlatSem.doOpApp [.closure flatEnv arg flatBody, flatArgument] =
        some (flatLocal, compileExp trace { baseMap with v := bindLocals traces (flatLocal.v.map Prod.fst) baseMap.v } body) ∧
      EnvRel genv sourceLocal flatLocal.v ∧
      GlobalEnvInv genv baseMap (fun n => n ∈ flatLocal.v.map Prod.fst) baseEnv ∧
      traces.length = flatLocal.v.length := by
  obtain ⟨baseMap, body, newVars, trace, argTrace, names, globals, empty, found, closures, sourceApp, flatApp⟩ :=
    doOpApp_topRecclosure_setup genv sourceEnv funs name flatEnv arg flatBody argument flatArgument closureRel distinct
  let extendedMap := { baseMap with v := nsBindList newVars baseMap.v }
  let extendedEnv := { sourceEnv with v := buildRecEnv funs sourceEnv sourceEnv.v }
  let localEnv := nsBind arg argument (nsEmpty : Namespace ModN VarN Value)
  let flatLocal := { flatEnv with v := [(arg, flatArgument)] }
  have localRel : EnvRel genv localEnv flatLocal.v := by
    exact .bind genv arg argument nsEmpty [] flatArgument (.empty genv) argumentRel
  have rebuilt := topRec_rebuilt_globalInv genv baseMap sourceEnv funs flatEnv newVars names globals empty closures
  have extendedInv : GlobalEnvInv genv extendedMap (fun n => n ∈ flatLocal.v.map Prod.fst) extendedEnv := by
    cases rebuilt with
    | intro _ _ _ values constructors =>
      apply GlobalEnvInv.intro
      · intro id value _ lookup
        exact values id value (by simp) lookup
      · exact constructors
  refine ⟨extendedMap, extendedEnv, localEnv, flatLocal, trace, [argTrace], body, ?_, ?_, localRel, extendedInv, rfl⟩
  · rw [sourceApp]
    cases h : buildRecEnv funs sourceEnv sourceEnv.v
    simp [extendedEnv, localEnv, nsAppend, nsBind, nsEmpty, h]
  · rw [flatApp]
    simp [extendedMap, flatLocal, bindLocals, nsBindList]

/-- Every successful source function application to a related argument has a
flat call with related local environments and a compiled source body. This
unifies ordinary, local-recursive, and top-level-recursive closure cases. -/
theorem doOpApp_related (genv : GlobalEnv) (sourceFunction : Value) (flatFunction : FlatSem.Value)
    (argument : Value) (flatArgument : FlatSem.Value)
    (functionRel : ValueRel genv sourceFunction flatFunction) (argumentRel : ValueRel genv argument flatArgument)
    (successful : doOpApp [sourceFunction, argument] ≠ none) :
    ∃ (baseMap : Environment) (baseEnv : SemEnv Value) (sourceLocal : Namespace ModN VarN Value)
      (flatLocal : FlatSem.Environment FlatSem.Value) (trace : List VarN) (traces : List BackendCommon.Tra)
      (body : AstHOL.Exp),
      doOpApp [sourceFunction, argument] = some ({ baseEnv with v := nsAppend sourceLocal baseEnv.v }, body) ∧
      FlatSem.doOpApp [flatFunction, flatArgument] =
        some (flatLocal, compileExp trace { baseMap with v := bindLocals traces (flatLocal.v.map Prod.fst) baseMap.v } body) ∧
      EnvRel genv sourceLocal flatLocal.v ∧
      GlobalEnvInv genv baseMap (fun n => n ∈ flatLocal.v.map Prod.fst) baseEnv ∧
      traces.length = flatLocal.v.length := by
  cases sourceFunction with
  | litv lit => simp [doOpApp] at successful
  | conv stamp values => simp [doOpApp] at successful
  | loc flag address => simp [doOpApp] at successful
  | vectorv values => simp [doOpApp] at successful
  | env env id => simp [doOpApp] at successful
  | closure env name body =>
    obtain ⟨baseMap, baseEnv, sourceLocal, flatLocal, trace, traces, src, dst, locals, globals, len⟩ :=
      doOpApp_closure_local genv env name body flatFunction argument flatArgument functionRel argumentRel
    exact ⟨baseMap, baseEnv, sourceLocal, flatLocal, trace, traces, body, src, dst, locals, globals, len⟩
  | recclosure env funs name =>
    have distinct : (funs.map Prod.fst).Nodup := by
      by_contra no
      simp [doOpApp, no] at successful
    cases found : findRecFun name funs with
    | none => simp [doOpApp, distinct, found] at successful
    | some pair =>
      obtain ⟨arg, body⟩ := pair
      rcases (valueRel_recclosure_iff genv env funs name flatFunction).mp functionRel with
        ⟨baseMap, baseEnv, captured, flatCaptured, trace, traces, rfl, rfl, locals, globals, len⟩ |
        ⟨baseMap, flatEnv, flatArg, flatBody, newVars, trace, argTrace, names, globals, empty, findFlat, closures, flatEq⟩
      · have setup := doOpApp_recclosure_local genv baseMap baseEnv captured flatCaptured funs name arg body
          trace traces locals globals len distinct found argument flatArgument argumentRel
        dsimp only at setup
        exact ⟨baseMap, baseEnv, _, _, name :: trace, .none :: traces, body, setup⟩
      · rw [flatEq] at functionRel ⊢
        exact doOpApp_topRecclosure_local genv env funs name flatEnv flatArg _ argument flatArgument functionRel argumentRel distinct


end Flapjack.Compiler.Backend.SourceToFlat

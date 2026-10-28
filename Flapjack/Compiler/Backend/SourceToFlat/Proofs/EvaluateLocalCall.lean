import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalEnvironment
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRelCases

/-! Function-call prerequisites over the factored source-to-flat relations.
These lemmas remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

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


end Flapjack.Compiler.Backend.SourceToFlat

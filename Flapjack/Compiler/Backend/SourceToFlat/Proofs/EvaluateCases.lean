import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalLookup
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.StateRel
import Flapjack.Compiler.Backend.Semantics.FlatSem.Evaluate
import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact
import Flapjack.EvaluateHOL.Definition

/-! Initial source-to-flat expression simulations. These are Flapjack-specific
infrastructure over the factored relations and the fuel-bounded flat
evaluator, not cases of the unbounded HOL `compile_correct` theorem. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendCommon

/-- A local lookup in related environments produces a related flat value. -/
theorem envRel_lookup (genv : GlobalEnv) (source : Namespace ModN VarN SemanticPrimitivesHOL.Value)
    (flat : List (VarN × FlatSem.Value)) (related : EnvRel genv source flat)
    (name : VarN) (value : SemanticPrimitivesHOL.Value)
    (lookup : nsLookup source (.short name) = some value) :
    ∃ flatValue, flat.lookup name = some flatValue ∧ ValueRel genv value flatValue := by
  cases related with
  | empty => simp [nsEmpty, nsLookup] at lookup
  | bind key sourceValue sourceEnv flatEnv flatValue envRel valueRel =>
    cases sourceEnv with
    | bind sourceValues sourceModules =>
      by_cases same : key = name
      · subst name
        simp [nsBind, nsLookup] at lookup
        subst value
        exact ⟨flatValue, by simp, valueRel⟩
      · have neq : (name == key) = false := by
          change decide (name = key) = false
          simp [Ne.symm same]
        simp [nsBind, nsLookup, List.lookup_cons, neq] at lookup
        obtain ⟨found, hfound, hrel⟩ := envRel_lookup genv _ flatEnv envRel name value lookup
        exact ⟨found, by simpa [List.lookup_cons, neq] using hfound, hrel⟩
termination_by flat.length

/-- A literal has the same value and preserves related states on both sides. -/
theorem evaluate_literal_related {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (trace : List VarN) (lit : Lit) (fuel : Nat) :
    EvaluateHOL.evaluate sourceState sourceEnv [.lit lit] = (sourceState, .val [.litv lit]) ∧
    FlatSem.evaluateFuel (fuel + 1) flatEnv flatState [compileExp trace compMap (.lit lit)] =
      some (flatState, .val [.litv lit]) ∧
    ValueRel genv (.litv lit) (.litv lit) ∧ StateRel genv sourceState flatState := by
  exact ⟨by simp [EvaluateHOL.evaluate], rfl, .literal genv lit, statesRel⟩

/-- A source local and the compiled flat local return related values. The
compiler-map premise identifies the local chosen by the pass. -/
theorem evaluate_local_related {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (envRel : EnvRel genv sourceEnv.v flatEnv.v)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (trace : List VarN) (name : VarN) (t : Tra)
    (compiled : nsLookup compMap.v (.short name) = some (.localName t name))
    (source : SemanticPrimitivesHOL.Value) (lookup : nsLookup sourceEnv.v (.short name) = some source)
    (fuel : Nat) :
    ∃ flat, EvaluateHOL.evaluate sourceState sourceEnv [.var (.short name)] = (sourceState, .val [source]) ∧
      FlatSem.evaluateFuel (fuel + 1) flatEnv flatState [compileExp trace compMap (.var (.short name))] =
        some (flatState, .val [flat]) ∧ ValueRel genv source flat ∧ StateRel genv sourceState flatState := by
  obtain ⟨flat, flatLookup, valueRel⟩ := envRel_lookup genv sourceEnv.v flatEnv.v envRel name source lookup
  refine ⟨flat, ?_, ?_, valueRel, statesRel⟩
  · simp [EvaluateHOL.evaluate, lookup]
  · simp [compileExp, compiled, compileVar, FlatSem.evaluateFuel, flatLookup]

/-- A source global and the compiled global-lookup expression return related
values. This connects the actual source evaluator to bounded flat evaluation. -/
theorem evaluate_global_related {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (globalsEq : flatState.globals = genv.v)
    (trace : List VarN) (id : Ident ModN VarN) (source : SemanticPrimitivesHOL.Value)
    (lookup : nsLookup sourceEnv.v id = some source) (related : GlobalLookupRel genv compMap id source)
    (fuel : Nat) :
    ∃ flat, EvaluateHOL.evaluate sourceState sourceEnv [.var id] = (sourceState, .val [source]) ∧
      FlatSem.evaluateFuel (fuel + 2) flatEnv flatState [compileExp trace compMap (.var id)] =
        some (flatState, .val [flat]) ∧ ValueRel genv source flat ∧ StateRel genv sourceState flatState := by
  obtain ⟨n, flat, t, compiled, valueRel, flatDo⟩ :=
    globalLookupRel_doApp genv compMap id source flatState globalsEq related
  refine ⟨flat, ?_, ?_, valueRel, statesRel⟩
  · simp [EvaluateHOL.evaluate, lookup]
  · simp [compileExp, compiled, compileVar, FlatSem.evaluateFuel, FlatSem.fixClock, FlatSem.doApp, flatDo]

/-- A function formed in a global environment and an empty flat local
environment produces related closures. -/
theorem evaluate_global_function_related {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value)
    (globalInv : GlobalEnvInv genv compMap (fun _ => False) sourceEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (trace : List VarN)
    (name : VarN) (body : AstHOL.Exp) (fuel : Nat) :
    let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[]⟩
    let compiledBody := compileExp trace
      { compMap with v := nsBind name (.localName .none name) compMap.v } body
    EvaluateHOL.evaluate sourceState sourceEnv [.fn name body] =
      (sourceState, .val [.closure sourceEnv name body]) ∧
    FlatSem.evaluateFuel (fuel + 1) flatEnv flatState [compileExp trace compMap (.fn name body)] =
      some (flatState, .val [.closure flatEnv name compiledBody]) ∧
    ValueRel genv (.closure sourceEnv name body) (.closure flatEnv name compiledBody) ∧
    StateRel genv sourceState flatState := by
  have inv : GlobalEnvInv genv compMap (fun n => n ∈ ([] : List VarN)) sourceEnv := by
    simpa using globalInv
  have related := ValueRel.closure genv compMap sourceEnv nsEmpty name body ⟨[]⟩ trace [.none]
    (.empty genv) inv rfl
  have appendEmpty : nsAppend (nsEmpty : Namespace ModN VarN SemanticPrimitivesHOL.Value) sourceEnv.v = sourceEnv.v := by
    cases h : sourceEnv.v with
    | bind values modules => simp [nsEmpty, nsAppend]
  have closureRel : ValueRel genv (.closure sourceEnv name body)
      (.closure ⟨[]⟩ name (compileExp trace
        { compMap with v := nsBind name (.localName .none name) compMap.v } body)) := by
    simpa [appendEmpty, bindLocals, nsBindList] using related
  exact ⟨by simp [EvaluateHOL.evaluate], rfl, closureRel, statesRel⟩

/-- A function captures related locals and preserves the global environment
invariant. The trace list has the same length as the flat local environment. -/
theorem evaluate_function_related {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (globalEnv : SemEnv SemanticPrimitivesHOL.Value)
    (sourceLocal : Namespace ModN VarN SemanticPrimitivesHOL.Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (localRel : EnvRel genv sourceLocal flatEnv.v)
    (globalInv : GlobalEnvInv genv compMap (fun n => n ∈ flatEnv.v.map Prod.fst) globalEnv)
    (traces : List Tra) (length : traces.length = flatEnv.v.length)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (trace : List VarN)
    (name : VarN) (body : AstHOL.Exp) (fuel : Nat) :
    let sourceEnv := { globalEnv with v := nsAppend sourceLocal globalEnv.v }
    let currentMap := { compMap with v := bindLocals traces (flatEnv.v.map Prod.fst) compMap.v }
    let compiledBody := compileExp trace
      { currentMap with v := nsBind name (.localName .none name) currentMap.v } body
    EvaluateHOL.evaluate sourceState sourceEnv [.fn name body] =
      (sourceState, .val [.closure sourceEnv name body]) ∧
    FlatSem.evaluateFuel (fuel + 1) flatEnv flatState [compileExp trace currentMap (.fn name body)] =
      some (flatState, .val [.closure flatEnv name compiledBody]) ∧
    ValueRel genv (.closure sourceEnv name body) (.closure flatEnv name compiledBody) ∧
    StateRel genv sourceState flatState := by
  have related := ValueRel.closure genv compMap globalEnv sourceLocal name body flatEnv trace (.none :: traces)
    localRel globalInv (by simpa using length)
  have closureRel : ValueRel genv (.closure { globalEnv with v := nsAppend sourceLocal globalEnv.v } name body)
      (.closure flatEnv name (compileExp trace
        { compMap with v := (nsBind name (VarName.localName .none name)
          (bindLocals traces (flatEnv.v.map Prod.fst) compMap.v)) } body)) := by
    simpa [bindLocals, nsBindList] using related
  exact ⟨by simp [EvaluateHOL.evaluate], rfl, closureRel, statesRel⟩

/-- Literal simulation using both clocked evaluators without extra fuel. This
is infrastructure over the factored value and state relations. -/
theorem evaluate_literal_unbounded {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (trace : List VarN) (lit : Lit) :
    EvaluateHOL.evaluate sourceState sourceEnv [.lit lit] = (sourceState, .val [.litv lit]) ∧
    FlatSem.evaluate flatEnv flatState [compileExp trace compMap (.lit lit)] =
      (flatState, .val [.litv lit]) ∧
    ValueRel genv (.litv lit) (.litv lit) ∧ StateRel genv sourceState flatState := by
  exact ⟨by simp [EvaluateHOL.evaluate], by simp [compileExp, FlatSem.evaluate], .literal genv lit, statesRel⟩

/-- Local-variable simulation using both clocked evaluators without extra fuel. -/
theorem evaluate_local_unbounded {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (envRel : EnvRel genv sourceEnv.v flatEnv.v)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (trace : List VarN) (name : VarN) (t : Tra)
    (compiled : nsLookup compMap.v (.short name) = some (.localName t name))
    (source : SemanticPrimitivesHOL.Value) (lookup : nsLookup sourceEnv.v (.short name) = some source) :
    ∃ flat, EvaluateHOL.evaluate sourceState sourceEnv [.var (.short name)] = (sourceState, .val [source]) ∧
      FlatSem.evaluate flatEnv flatState [compileExp trace compMap (.var (.short name))] =
        (flatState, .val [flat]) ∧ ValueRel genv source flat ∧ StateRel genv sourceState flatState := by
  obtain ⟨flat, flatLookup, valueRel⟩ := envRel_lookup genv sourceEnv.v flatEnv.v envRel name source lookup
  refine ⟨flat, ?_, ?_, valueRel, statesRel⟩
  · simp [EvaluateHOL.evaluate, lookup]
  · simp [compileExp, compiled, compileVar, FlatSem.evaluate, flatLookup]

/-- Global-variable simulation using both clocked evaluators without extra fuel. -/
theorem evaluate_global_unbounded {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (globalsEq : flatState.globals = genv.v)
    (trace : List VarN) (id : Ident ModN VarN) (source : SemanticPrimitivesHOL.Value)
    (lookup : nsLookup sourceEnv.v id = some source) (related : GlobalLookupRel genv compMap id source) :
    ∃ flat, EvaluateHOL.evaluate sourceState sourceEnv [.var id] = (sourceState, .val [source]) ∧
      FlatSem.evaluate flatEnv flatState [compileExp trace compMap (.var id)] =
        (flatState, .val [flat]) ∧ ValueRel genv source flat ∧ StateRel genv sourceState flatState := by
  obtain ⟨n, flat, t, compiled, valueRel, flatDo⟩ :=
    globalLookupRel_doApp genv compMap id source flatState globalsEq related
  refine ⟨flat, ?_, ?_, valueRel, statesRel⟩
  · simp [EvaluateHOL.evaluate, lookup]
  · simp [compileExp, compiled, compileVar, FlatSem.evaluate, FlatSem.fixClock, FlatSem.doApp, flatDo]

/-- Closure capture simulation using both clocked evaluators without extra fuel. -/
theorem evaluate_function_unbounded {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (globalEnv : SemEnv SemanticPrimitivesHOL.Value)
    (sourceLocal : Namespace ModN VarN SemanticPrimitivesHOL.Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (localRel : EnvRel genv sourceLocal flatEnv.v)
    (globalInv : GlobalEnvInv genv compMap (fun n => n ∈ flatEnv.v.map Prod.fst) globalEnv)
    (traces : List Tra) (length : traces.length = flatEnv.v.length)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (trace : List VarN)
    (name : VarN) (body : AstHOL.Exp) :
    let sourceEnv := { globalEnv with v := nsAppend sourceLocal globalEnv.v }
    let currentMap := { compMap with v := bindLocals traces (flatEnv.v.map Prod.fst) compMap.v }
    let compiledBody := compileExp trace
      { currentMap with v := nsBind name (.localName .none name) currentMap.v } body
    EvaluateHOL.evaluate sourceState sourceEnv [.fn name body] =
      (sourceState, .val [.closure sourceEnv name body]) ∧
    FlatSem.evaluate flatEnv flatState [compileExp trace currentMap (.fn name body)] =
      (flatState, .val [.closure flatEnv name compiledBody]) ∧
    ValueRel genv (.closure sourceEnv name body) (.closure flatEnv name compiledBody) ∧
    StateRel genv sourceState flatState := by
  have bounded := evaluate_function_related genv compMap globalEnv sourceLocal flatEnv localRel globalInv
    traces length sourceState flatState statesRel trace name body 0
  exact ⟨by simp [EvaluateHOL.evaluate], by simp [compileExp, FlatSem.evaluate], bounded.2.2.1, statesRel⟩

end Flapjack.Compiler.Backend.SourceToFlat

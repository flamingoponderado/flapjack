module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateBoundConstructor
public import Flapjack.NamespaceProps
public import Flapjack.Compiler.Backend.FlatProps.ValueBasics
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRelCases
public import Flapjack.SemanticPrimitivesProps.RecursiveFunctions

@[expose] public section

/-! Growing expression simulation infrastructure for related local environments. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

namespace DoAppRecHelpPort
/-- Roundtrip for the finite maps of the global environment. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end DoAppRecHelpPort

/-- Recursive closures generated from a function list preserve the local
environment relation when they capture the same related environments. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_app_rec_help"
  (fmap_as_finite_support := [c, tys])]
theorem doApp_rec_help {α : Type} {baseEnv : SemEnv Value} {traces : List BackendCommon.Tra}
    {capturedFuns : List (VarN × VarN × AstHOL.Exp)} :
    ∀ (genv : GlobalEnv) (compMap : Environment) (sourceLocal : Namespace ModN VarN Value)
      (flatLocal : FlatSem.Environment FlatSem.Value) (_envVTop : α)
      (funs : List (VarN × VarN × AstHOL.Exp)) (trace : List VarN),
      EnvRel genv sourceLocal flatLocal.v ∧
      GlobalEnvInv genv compMap (fun n => n ∈ flatLocal.v.map Prod.fst) baseEnv ∧
      traces.length = capturedFuns.length + flatLocal.v.length →
      EnvRel genv
        (alistToNs (funs.map (fun (f, _, _) =>
          (f, Value.recclosure { baseEnv with v := nsAppend sourceLocal baseEnv.v } capturedFuns f))))
        ((compileFuns trace { compMap with v := (List.foldr (fun (x, v) e => nsBind x v e) compMap.v
          (List.zipWith (fun t x => (x, VarName.localName t x)) traces
            (capturedFuns.map Prod.fst ++ flatLocal.v.map Prod.fst))) } funs).map
          (fun (f, _, _) => (f, FlatSem.Value.recclosure flatLocal
            (compileFuns trace { compMap with v := (List.foldr (fun (x, v) e => nsBind x v e) compMap.v
              (List.zipWith (fun t x => (x, VarName.localName t x)) traces
                (capturedFuns.map Prod.fst ++ flatLocal.v.map Prod.fst))) } capturedFuns) f))) := by
  intro genv compMap sourceLocal flatLocal _ funs trace ⟨localRel, globalInv, length⟩
  have recRel : ∀ name, ValueRel genv
      (.recclosure { baseEnv with v := nsAppend sourceLocal baseEnv.v } capturedFuns name)
      (.recclosure flatLocal (compileFuns trace { compMap with v := bindLocals traces (capturedFuns.map Prod.fst ++ flatLocal.v.map Prod.fst) compMap.v } capturedFuns) name) := by
    intro name
    exact .recclosure genv compMap baseEnv sourceLocal capturedFuns name flatLocal trace traces
      localRel globalInv length
  induction funs with
  | nil => simpa [compileFuns, alistToNs, nsEmpty] using EnvRel.empty genv
  | cons head rest ih =>
    obtain ⟨name, arg, body⟩ := head
    simpa [compileFuns, alistToNs, nsBind, bindLocals, nsBindList] using
      EnvRel.bind genv name _ _ _ _ ih (recRel name)

/-- An expression simulation restricted to states at or below a clock bound. -/
def LocalEnvBoundedIH {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (expr : AstHOL.Exp) : Prop :=
  ∀ (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (baseEnv : SemEnv Value)
    (sourceLocal : Namespace ModN VarN Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (traces : List BackendCommon.Tra) (trace : List VarN) (baseMap : Environment) (gen : EnvironmentGenerationStore),
    source.clock ≤ limit → EnvRel genv sourceLocal flatEnv.v →
    GlobalEnvInv genv baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv →
    traces.length = flatEnv.v.length → factoredInvariant interp transform gen genv (start, finish, other) source flat →
    envGenRel gen source.evalState →
    (∀ last, EvaluateHOL.evaluate source { baseEnv with v := nsAppend sourceLocal baseEnv.v } [expr] ≠
      (last, .err (.abort .typeError))) →
    LocalExpressionStep interp transform genv start finish other source flat
      { baseEnv with v := nsAppend sourceLocal baseEnv.v } flatEnv trace
      { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v } gen expr

/-- Constructing a local recursive environment preserves the factored
source-to-flat value relation for every mutually recursive closure. -/
theorem localRecEnv_related (genv : GlobalEnv) (baseMap : Environment)
    (baseEnv : SemEnv Value) (sourceLocal : Namespace ModN VarN Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (funs : List (VarN × VarN × AstHOL.Exp))
    (trace : List VarN) (traces : List BackendCommon.Tra)
    (localRel : EnvRel genv sourceLocal flatEnv.v)
    (envInv : GlobalEnvInv genv baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv)
    (length : traces.length = funs.length + flatEnv.v.length) :
    let compMap := { baseMap with v := bindLocals traces (funs.map Prod.fst ++ flatEnv.v.map Prod.fst) baseMap.v }
    let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
    let compiled := compileFuns trace compMap funs
    EnvRel genv (buildRecEnv funs sourceEnv sourceLocal) (FlatSem.buildRecEnv compiled flatEnv flatEnv.v) := by
  dsimp only
  rw [Flapjack.SemanticPrimitivesProps.buildRecEnv_merge funs (),
    FlatProps.buildRecEnv_merge _ ()]
  apply envRel_nsAppend genv _ _ _ _ ⟨?_, localRel⟩
  simpa only [bindLocals, nsBindList] using
    (doApp_rec_help (α := Unit) (baseEnv := baseEnv) (traces := traces) (capturedFuns := funs)
      genv baseMap sourceLocal flatEnv () funs trace ⟨localRel, envInv, length⟩)

/-- Variable lookup respects local shadowing and falls back to the related
global environment for names absent from the local stack. -/
theorem localEnvBounded_variable {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (id : Ident ModN VarN) : LocalEnvBoundedIH (F := F) interp transform limit (.var id) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen _ localRel envInv tracesLen
    invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  change LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen
    (.var id)
  let tracedNames := traces.zip (flatEnv.v.map Prod.fst)
  let bindings := tracedNames.map (fun (tr, name) => (name, VarName.localName tr name))
  have bindingKeys : bindings.map Prod.fst = flatEnv.v.map Prod.fst := by
    change (tracedNames.map _).map Prod.fst = _
    rw [List.map_map]
    exact List.map_snd_zip (by simpa using tracesLen.symm.le)
  have compiledShape : compMap.v = nsAppend (alistToNs bindings) baseMap.v := by
    simp only [compMap, bindLocals, ← nsAppend_to_nsBindList, bindings, tracedNames,
      List.zip_eq_zipWith, List.map_zipWith]
  have globalCase : ∀ id, (∀ name, name ∈ flatEnv.v.map Prod.fst → id ≠ .short name) →
      nsLookup sourceEnv.v id = nsLookup baseEnv.v id →
      (∀ last, EvaluateHOL.evaluate source sourceEnv [.var id] ≠ (last, .err (.abort .typeError))) →
      LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen (.var id) := by
    intro id fresh sourceLookupEq safeId
    cases lookup : nsLookup baseEnv.v id with
    | none =>
      have bad : EvaluateHOL.evaluate source sourceEnv [.var id] = (source, .err (.abort .typeError)) := by
        simp [EvaluateHOL.evaluate, sourceLookupEq, lookup, EvaluateHOL.typeError]
      exact False.elim (safeId source bad)
    | some sourceValue =>
      have oldRel : GlobalLookupRel genv baseMap id sourceValue := by
        cases envInv with
        | intro _ _ _ values _ =>
          apply values id sourceValue _ lookup
          intro ⟨n, mem, eq⟩
          exact fresh n mem eq
      have newRel : GlobalLookupRel genv compMap id sourceValue := by
        cases oldRel with
        | intro _ _ _ index stored tr compiled bound slot valueRel =>
          apply GlobalLookupRel.intro genv compMap id sourceValue index stored tr _ bound slot valueRel
          rw [compiledShape]
          cases id with
          | long moduleName rest =>
            rw [nsLookup_append_long]
            exact compiled
          | short name =>
            have missing : bindings.lookup name = none := by
              by_contra found
              have member := (Flapjack.lookup_exists_iff_mem_keys bindings name).mp
                (Option.ne_none_iff_exists'.mp found)
              rw [bindingKeys] at member
              exact fresh name member rfl
            rw [nsLookup_append_short]
            change (bindings.lookup name).orElse _ = _
            simpa [missing] using compiled
      have sourceLookup : nsLookup sourceEnv.v id = some sourceValue := by rw [sourceLookupEq, lookup]
      obtain ⟨flatValue, sourceRun, flatRun, valueRel, states⟩ :=
        evaluate_global_unbounded genv compMap sourceEnv flatEnv source flat invariant.2.2.1
          invariant.2.2.2.2.2.2.1.symm trace id sourceValue sourceLookup newRel
      refine ⟨genv, ?_, ?_⟩
      · unfold ExprSim
        rw [sourceRun, flatRun]
        exact ⟨.value (.cons valueRel .nil), states⟩
      · rw [sourceRun, flatRun]
        exact ⟨GlobalGrowth.refl genv, invariant, generation, oracForwardRel_refl interp source.evalState⟩
  obtain ⟨entries, sourceShape, names⟩ := envRel_dom genv sourceLocal flatEnv.v localRel
  have lookupNone (name : VarN) : nsLookup sourceLocal (.short name) = none ↔ flatEnv.v.lookup name = none := by
    rw [sourceShape]
    change entries.lookup name = none ↔ flatEnv.v.lookup name = none
    apply not_iff_not.mp
    change entries.lookup name ≠ none ↔ flatEnv.v.lookup name ≠ none
    rw [Option.ne_none_iff_exists', Option.ne_none_iff_exists',
      Flapjack.lookup_exists_iff_mem_keys, Flapjack.lookup_exists_iff_mem_keys, names]
  cases id with
  | long moduleName rest =>
    apply globalCase (.long moduleName rest)
    · intro n _ neq
      cases neq
    · change nsLookup (nsAppend sourceLocal baseEnv.v) (.long moduleName rest) = _
      rw [nsLookup_append_long, sourceShape]
      rfl
    · exact safe
  | short name =>
    cases flatLookup : flatEnv.v.lookup name with
    | none =>
      have absent : name ∉ flatEnv.v.map Prod.fst := by
        intro member
        obtain ⟨v, found⟩ := (Flapjack.lookup_exists_iff_mem_keys flatEnv.v name).mpr member
        rw [flatLookup] at found
        contradiction
      apply globalCase (.short name)
      · intro n mem eq
        cases eq
        exact absent mem
      · change nsLookup (nsAppend sourceLocal baseEnv.v) (.short name) = _
        rw [nsLookup_append_short, (lookupNone name).mpr flatLookup]
        rfl
      · exact safe
    | some flatValue =>
      cases localLookup : nsLookup sourceLocal (.short name) with
      | none =>
        have missing := (lookupNone name).mp localLookup
        rw [flatLookup] at missing
        contradiction
      | some sourceValue =>
        obtain ⟨foundFlat, foundLookup, valueRel⟩ := envRel_lookup genv sourceLocal flatEnv.v localRel name sourceValue localLookup
        rw [flatLookup] at foundLookup
        cases foundLookup
        have localKey : name ∈ bindings.map Prod.fst := by
          rw [bindingKeys]
          exact (Flapjack.lookup_exists_iff_mem_keys flatEnv.v name).mp ⟨flatValue, flatLookup⟩
        obtain ⟨varName, found⟩ := (Flapjack.lookup_exists_iff_mem_keys bindings name).mpr localKey
        obtain ⟨pre, post, split, _⟩ := List.lookup_eq_some_iff.mp found
        have member : (name, varName) ∈ bindings := by rw [split]; simp
        obtain ⟨⟨tr, key⟩, _, equal⟩ := List.mem_map.mp member
        have keyEq : key = name := congrArg Prod.fst equal
        subst key
        have valueEq : VarName.localName tr name = varName := congrArg Prod.snd equal
        subst varName
        have compiled : nsLookup (bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v)
            (.short name) = some (.localName tr name) := by
          change nsLookup compMap.v (.short name) = _
          rw [compiledShape, nsLookup_append_short]
          change (bindings.lookup name).orElse _ = _
          rw [found]
          rfl
        have sourceLookup : nsLookup sourceEnv.v (.short name) = some sourceValue := by
          change nsLookup (nsAppend sourceLocal baseEnv.v) (.short name) = _
          simp [nsLookup_append_short, localLookup]
        have sourceRun : EvaluateHOL.evaluate source sourceEnv [.var (.short name)] = (source, .val [sourceValue]) := by
          simp [EvaluateHOL.evaluate, sourceLookup]
        have flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap (.var (.short name))] =
            (flat, .val [flatValue]) := by
          simp [compileExp, compMap, compiled, compileVar, FlatSem.evaluate, flatLookup]
        refine ⟨genv, ?_, ?_⟩
        · unfold ExprSim
          rw [sourceRun, flatRun]
          exact ⟨.value (.cons valueRel .nil), invariant.2.2.1⟩
        · rw [sourceRun, flatRun]
          exact ⟨GlobalGrowth.refl genv, invariant, generation, oracForwardRel_refl interp source.evalState⟩

end Flapjack.Compiler.Backend.SourceToFlat

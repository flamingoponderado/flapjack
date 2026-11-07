import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateBoundControl
import Flapjack.NamespaceProps

/-! Growing expression simulation for arbitrary related local environments.
These factored relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

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

/-- Literals preserve arbitrary related local environments and both states. -/
theorem localEnvBounded_literal {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat) (lit : Lit) :
    LocalEnvBoundedIH (F := F) interp transform limit (.lit lit) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen _ _ _ _ invariant generation _
  refine ⟨genv, exprSim_literal genv _ trace _ flatEnv source flat invariant.2.2.1 lit, ?_⟩
  simpa only [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate] using
    And.intro (GlobalGrowth.refl genv) (And.intro invariant
      (And.intro generation (oracForwardRel_refl interp source.evalState)))

/-- Functions capture any related local environment. -/
theorem localEnvBounded_function {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (name : VarN) (body : AstHOL.Exp) : LocalEnvBoundedIH (F := F) interp transform limit (.fn name body) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen _ localRel envInv length
    invariant generation _
  refine ⟨genv, exprSim_function genv baseMap baseEnv sourceLocal flatEnv localRel envInv traces length
    source flat invariant.2.2.1 trace name body, ?_⟩
  simpa only [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate] using
    And.intro (GlobalGrowth.refl genv) (And.intro invariant
      (And.intro generation (oracForwardRel_refl interp source.evalState)))

/-- Recursive source bindings commute with appending a surrounding namespace. -/
theorem buildRecEnv_nsAppend (funs : List (VarN × VarN × AstHOL.Exp)) (closureEnv : SemEnv Value)
    (localEnv globalEnv : Namespace ModN VarN Value) :
    buildRecEnv funs closureEnv (nsAppend localEnv globalEnv) =
      nsAppend (buildRecEnv funs closureEnv localEnv) globalEnv := by
  have aux : ∀ remaining : List (VarN × VarN × AstHOL.Exp),
      remaining.foldr (fun (name, _, _) rest => nsBind name (.recclosure closureEnv funs name) rest)
          (nsAppend localEnv globalEnv) =
        nsAppend (remaining.foldr (fun (name, _, _) rest => nsBind name (.recclosure closureEnv funs name) rest)
          localEnv) globalEnv := by
    intro remaining
    induction remaining with
    | nil => rfl
    | cons head tail ih =>
      obtain ⟨name, arg, body⟩ := head
      simp only [List.foldr_cons, ih]
      cases tailEnv : tail.foldr (fun (name, _, _) rest => nsBind name (.recclosure closureEnv funs name) rest) localEnv
      cases globalEnv
      rfl
  exact aux funs

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
  let compMap := { baseMap with v := bindLocals traces (funs.map Prod.fst ++ flatEnv.v.map Prod.fst) baseMap.v }
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compiled := compileFuns trace compMap funs
  have recRel : ∀ name, ValueRel genv (.recclosure sourceEnv funs name) (.recclosure flatEnv compiled name) := by
    intro name
    exact .recclosure genv baseMap baseEnv sourceLocal funs name flatEnv trace traces localRel envInv length
  have helper : ∀ remaining : List (VarN × VarN × AstHOL.Exp),
      EnvRel genv
        (remaining.foldr (fun (name, _, _) rest => nsBind name (.recclosure sourceEnv funs name) rest) sourceLocal)
        ((compileFuns trace compMap remaining).foldr
          (fun (name, _, _) rest => (name, .recclosure flatEnv compiled name) :: rest) flatEnv.v) := by
    intro remaining
    induction remaining with
    | nil => exact localRel
    | cons head rest ih =>
      obtain ⟨name, arg, body⟩ := head
      simp only [List.foldr_cons, compileFuns]
      exact .bind genv name _ _ _ _ ih (recRel name)
  exact helper funs


/-- A compiled local lookup selects a trace for the first matching local name. -/
theorem bindLocals_lookup_hit (locals : List (VarN × FlatSem.Value)) (traces : List BackendCommon.Tra)
    (base : Namespace ModN VarN VarName) (name : VarN) (value : FlatSem.Value)
    (length : traces.length = locals.length) (lookup : locals.lookup name = some value) :
    ∃ tr, nsLookup (bindLocals traces (locals.map Prod.fst) base) (.short name) = some (.localName tr name) := by
  induction locals generalizing traces with
  | nil => simp at lookup
  | cons entry rest ih =>
    obtain ⟨key, stored⟩ := entry
    cases traces with
    | nil => simp at length
    | cons tr traces =>
      have len : traces.length = rest.length := by simpa using length
      by_cases same : name = key
      · subst key
        refine ⟨tr, ?_⟩
        change nsLookup (nsBind name (.localName tr name) (bindLocals traces (rest.map Prod.fst) base))
          (.short name) = _
        exact nsLookup_nsBind.1 name _ _
      · have neq : (name == key) = false := by
          change decide (name = key) = false
          simp [same]
        have restLookup : rest.lookup name = some value := by simpa [List.lookup_cons, neq] using lookup
        obtain ⟨foundTrace, found⟩ := ih traces len restLookup
        refine ⟨foundTrace, ?_⟩
        change nsLookup (nsBind key (.localName tr key) (bindLocals traces (rest.map Prod.fst) base)) (.short name) = _
        rw [nsLookup_bind_other _ key (VarName.localName tr key) (.short name) (by simpa using same)]
        exact found

/-- Names absent from the local stack retain their original compiler lookup. -/
theorem bindLocals_lookup_other (locals : List (VarN × FlatSem.Value)) (traces : List BackendCommon.Tra)
    (base : Namespace ModN VarN VarName) (id : Ident ModN VarN)
    (length : traces.length = locals.length)
    (fresh : ∀ name, name ∈ locals.map Prod.fst → id ≠ .short name) :
    nsLookup (bindLocals traces (locals.map Prod.fst) base) id = nsLookup base id := by
  induction locals generalizing traces with
  | nil =>
    cases traces with
    | nil => simp [bindLocals, nsBindList]
    | cons tr traces => simp at length
  | cons entry rest ih =>
    obtain ⟨key, stored⟩ := entry
    cases traces with
    | nil => simp at length
    | cons tr traces =>
      have len : traces.length = rest.length := by simpa using length
      have different : id ≠ .short key := fresh key (by simp)
      have restFresh : ∀ n, n ∈ rest.map Prod.fst → id ≠ .short n := by
        intro n mem
        exact fresh n (by simp [mem])
      change nsLookup (nsBind key (.localName tr key) (bindLocals traces (rest.map Prod.fst) base)) id = _
      rw [nsLookup_bind_other _ key (VarName.localName tr key) id different]
      exact ih traces len restFresh

/-- A missing flat local lookup is also absent from the related source locals. -/
theorem envRel_missing (genv : GlobalEnv) (source : Namespace ModN VarN Value)
    (flat : List (VarN × FlatSem.Value)) (related : EnvRel genv source flat) (name : VarN)
    (missing : flat.lookup name = none) : nsLookup source (.short name) = none := by
  cases related with
  | empty => rfl
  | bind key sourceValue sourceEnv flatEnv flatValue envRel valueRel =>
    by_cases same : name = key
    · subst key
      simp at missing
    · have neq : (name == key) = false := by
        change decide (name = key) = false
        simp [same]
      have restMissing : flatEnv.lookup name = none := by simpa [List.lookup_cons, neq] using missing
      rw [nsLookup_bind_other _ key sourceValue (.short name) (by simpa using same)]
      exact envRel_missing genv sourceEnv flatEnv envRel name restMissing
termination_by flat.length

/-- A missing source local lookup is also absent from the related flat locals. -/
theorem envRel_source_missing (genv : GlobalEnv) (source : Namespace ModN VarN Value)
    (flat : List (VarN × FlatSem.Value)) (related : EnvRel genv source flat) (name : VarN)
    (missing : nsLookup source (.short name) = none) : flat.lookup name = none := by
  cases related with
  | empty => rfl
  | bind key sourceValue sourceEnv flatEnv flatValue envRel valueRel =>
    by_cases same : name = key
    · subst key
      rw [nsLookup_nsBind.1] at missing
      contradiction
    · have neq : (name == key) = false := by
        change decide (name = key) = false
        simp [same]
      have restMissing : nsLookup sourceEnv (.short name) = none := by
        simpa [nsLookup_bind_other _ key sourceValue (.short name) (by simpa using same)] using missing
      simpa [List.lookup_cons, neq] using envRel_source_missing genv sourceEnv flatEnv envRel name restMissing
termination_by flat.length

/-- Related local environments contain no module namespaces. -/
theorem envRel_no_modules (genv : GlobalEnv) (source : Namespace ModN VarN Value)
    (flat : List (VarN × FlatSem.Value)) (related : EnvRel genv source flat) (moduleName : ModN) :
    nsLookupMod source [moduleName] = none := by
  cases related with
  | empty => rfl
  | bind key value sourceEnv flatEnv flatValue envRel valueRel =>
    have ih := envRel_no_modules genv sourceEnv flatEnv envRel moduleName
    cases sourceEnv with
    | bind values modules => simpa [nsBind, nsLookupMod] using ih
termination_by flat.length

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
          simpa [compMap, bindLocals_lookup_other flatEnv.v traces baseMap.v id tracesLen fresh] using compiled
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
  cases id with
  | long moduleName rest =>
    apply globalCase (.long moduleName rest)
    · intro n _ neq
      cases neq
    · change nsLookup (nsAppend sourceLocal baseEnv.v) (.long moduleName rest) = _
      rw [nsLookup_append_long, envRel_no_modules genv sourceLocal flatEnv.v localRel moduleName]
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
        rw [nsLookup_append_short, envRel_missing genv sourceLocal flatEnv.v localRel name flatLookup]
        rfl
      · exact safe
    | some flatValue =>
      cases localLookup : nsLookup sourceLocal (.short name) with
      | none =>
        have missing := envRel_source_missing genv sourceLocal flatEnv.v localRel name localLookup
        rw [flatLookup] at missing
        contradiction
      | some sourceValue =>
        obtain ⟨foundFlat, foundLookup, valueRel⟩ := envRel_lookup genv sourceLocal flatEnv.v localRel name sourceValue localLookup
        rw [flatLookup] at foundLookup
        cases foundLookup
        obtain ⟨tr, compiled⟩ := bindLocals_lookup_hit flatEnv.v traces baseMap.v name flatValue tracesLen flatLookup
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

/-- Leaf expressions using arbitrary related local environments. -/
inductive LocalEnvExpression : AstHOL.Exp → Prop where
  | literal (lit : Lit) : LocalEnvExpression (.lit lit)
  | variable_ (id : Ident ModN VarN) : LocalEnvExpression (.var id)
  | function_ (name : VarN) (body : AstHOL.Exp) : LocalEnvExpression (.fn name body)

end Flapjack.Compiler.Backend.SourceToFlat

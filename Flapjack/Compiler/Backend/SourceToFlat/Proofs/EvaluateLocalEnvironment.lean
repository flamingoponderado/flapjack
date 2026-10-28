import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateBoundControl

/-! Growing expression simulation for arbitrary related local environments.
These factored relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Induction hypothesis for arbitrary related local environments and their
compiler traces. -/
def LocalEnvIH {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expr : AstHOL.Exp) : Prop :=
  ∀ (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (baseEnv : SemEnv Value)
    (sourceLocal : Namespace ModN VarN Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (traces : List BackendCommon.Tra) (trace : List VarN) (baseMap : Environment) (gen : EnvironmentGenerationStore),
    EnvRel genv sourceLocal flatEnv.v →
    GlobalEnvInv genv baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv →
    traces.length = flatEnv.v.length →
    factoredInvariant interp transform gen genv (start, finish, other) source flat →
    envGenRel gen source.evalState →
    (∀ last, EvaluateHOL.evaluate source { baseEnv with v := nsAppend sourceLocal baseEnv.v } [expr] ≠
      (last, .err (.abort .typeError))) →
    LocalExpressionStep interp transform genv start finish other source flat
      { baseEnv with v := nsAppend sourceLocal baseEnv.v } flatEnv trace
      { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v } gen expr

/-- Named local bindings extend the related environments and compose the
initializer and body simulations, including shadowing and early errors. -/
theorem localEnvIH_let_named {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (first body : AstHOL.Exp)
    (firstIH : LocalEnvIH (F := F) interp transform first)
    (bodyIH : LocalEnvIH (F := F) interp transform body) :
    LocalEnvIH (F := F) interp transform (.let_ (some name) first body) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have firstSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [first] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, bad]
  obtain ⟨middleGenv, firstSim, firstPost⟩ := firstIH genv start finish other source flat baseEnv sourceLocal flatEnv traces
    (name :: trace) baseMap gen localRel envInv tracesLen invariant generation firstSafe
  unfold ExprSim at firstSim
  generalize sourceFirst : EvaluateHOL.evaluate source sourceEnv [first] = sourceResult at firstSim firstPost
  obtain ⟨middleSource, sourceResult⟩ := sourceResult
  generalize flatFirst : FlatSem.evaluate flatEnv flat [compileExp (name :: trace) compMap first] = flatResult at firstSim firstPost
  obtain ⟨middleFlat, flatResult⟩ := flatResult
  obtain ⟨firstRelated, firstStates⟩ := firstSim
  cases firstRelated with
  | abort error =>
    refine ⟨middleGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        [compileExp (name :: trace) compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatFirst]
      exact ⟨.abort error, firstStates⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
      trivial
  | raise valueRel =>
    refine ⟨middleGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        [compileExp (name :: trace) compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatFirst]
      exact ⟨.raise valueRel, firstStates⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        [compileExp (name :: trace) compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatFirst]
      exact firstPost
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨value, sourceEq⟩ := EvaluateProps.evaluateSingFull source middleSource sourceEnv first sourceValues sourceFirst
    subst sourceValues
    cases valuesRel with
    | cons related tail =>
      cases tail with
      | nil =>
        rename_i flatValue
        obtain ⟨firstGrowth, middleInvariant, middleGeneration, firstForward⟩ := firstPost
        have middleEnv := globalEnvInv_growth genv middleGenv firstGrowth baseMap
          (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv envInv
        have extendedInv : GlobalEnvInv middleGenv baseMap
            (fun n => n ∈ ((name, flatValue) :: flatEnv.v).map Prod.fst) baseEnv := by
          cases middleEnv with
          | intro _ _ _ values constructors =>
            apply GlobalEnvInv.intro
            · intro id v fresh lookup
              apply values id v _ lookup
              intro ⟨n, mem, eq⟩
              apply fresh
              exact ⟨n, by simp [mem], eq⟩
            · exact constructors
        have extendedRel := EnvRel.bind middleGenv name value sourceLocal flatEnv.v flatValue
          (envRel_growth genv middleGenv firstGrowth sourceLocal flatEnv.v localRel) related
        have sourceBind : nsAppend (nsBind name value sourceLocal) baseEnv.v = nsBind name value sourceEnv.v := by
          cases sourceLocal
          cases envEq : baseEnv.v
          simp [sourceEnv, envEq, nsAppend, nsBind]
        have mapBind : bindLocals (.none :: traces) (((name, flatValue) :: flatEnv.v).map Prod.fst) baseMap.v =
            nsBind name (.localName .none name) compMap.v := by
          simp [bindLocals, nsBindList, compMap]
        simp only [List.map_cons] at mapBind
        have bodySafe : ∀ last, EvaluateHOL.evaluate middleSource
            { sourceEnv with v := nsBind name value sourceEnv.v } [body] ≠ (last, .err (.abort .typeError)) := by
          intro last bad
          apply safe last
          rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
          simpa [nsOptBind, EvaluateHOL.headValue, Flapjack.holHd] using bad
        obtain ⟨finalGenv, bodySim, bodyPost⟩ := bodyIH middleGenv start finish other middleSource middleFlat
          baseEnv (nsBind name value sourceLocal) { flatEnv with v := (name, flatValue) :: flatEnv.v }
          (.none :: traces) trace baseMap gen extendedRel extendedInv (by simpa using tracesLen)
          middleInvariant middleGeneration (by simpa [sourceBind] using bodySafe)
        have bodySim : ExprSim finalGenv { compMap with v := nsBind name (.localName .none name) compMap.v }
            trace { sourceEnv with v := nsBind name value sourceEnv.v }
            { flatEnv with v := (name, flatValue) :: flatEnv.v } middleSource middleFlat body := by
          simpa [sourceBind, mapBind] using bodySim
        have bodyPost := bodyPost
        simp only [sourceBind] at bodyPost
        have sourceOuter : EvaluateHOL.evaluate source sourceEnv [.let_ (some name) first body] =
            EvaluateHOL.evaluate middleSource { sourceEnv with v := nsBind name value sourceEnv.v } [body] := by
          rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
          simp [nsOptBind, EvaluateHOL.headValue, Flapjack.holHd]
        have flatOuter : FlatSem.evaluate flatEnv flat [compileExp trace compMap (.let_ (some name) first body)] =
            FlatSem.evaluate { flatEnv with v := (name, flatValue) :: flatEnv.v } middleFlat
              [compileExp trace { compMap with v := nsBind name (.localName .none name) compMap.v } body] := by
          rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
            [compileExp (name :: trace) compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatFirst]
          rfl
        refine ⟨finalGenv, ?_, ?_⟩
        · unfold ExprSim at bodySim ⊢
          rw [sourceOuter, flatOuter]
          exact bodySim
        · rw [sourceOuter, flatOuter]
          cases result : (EvaluateHOL.evaluate middleSource
              { sourceEnv with v := nsBind name value sourceEnv.v } [body]).2 with
          | err error =>
            cases error with
            | abort error => simp
            | raise value =>
              rw [result] at bodyPost
              obtain ⟨growth, finalInvariant, finalGeneration, bodyForward⟩ := bodyPost
              exact ⟨firstGrowth.trans growth, finalInvariant, finalGeneration,
                oracForwardRel_trans interp _ _ _ ⟨firstForward, bodyForward⟩⟩
          | val values =>
            rw [result] at bodyPost
            obtain ⟨growth, finalInvariant, finalGeneration, bodyForward⟩ := bodyPost
            exact ⟨firstGrowth.trans growth, finalInvariant, finalGeneration,
              oracForwardRel_trans interp _ _ _ ⟨firstForward, bodyForward⟩⟩


/-- Literals preserve arbitrary related local environments and both states. -/
theorem localEnvIH_literal {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (lit : Lit) :
    LocalEnvIH (F := F) interp transform (.lit lit) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen _ _ _ invariant generation _
  refine ⟨genv, exprSim_literal genv _ trace _ flatEnv source flat invariant.2.2.1 lit, ?_⟩
  simpa only [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate] using
    And.intro (GlobalGrowth.refl genv) (And.intro invariant
      (And.intro generation (oracForwardRel_refl interp source.evalState)))

/-- Functions capture any related local environment. -/
theorem localEnvIH_function {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (body : AstHOL.Exp) : LocalEnvIH (F := F) interp transform (.fn name body) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv length
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

/-- Compilation preserves the names and order of a recursive function group. -/
theorem compileFuns_local_names (trace : List VarN) (env : Environment)
    (funs : List (VarN × VarN × AstHOL.Exp)) :
    (compileFuns trace env funs).map Prod.fst = funs.map Prod.fst := by
  induction funs with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨name, arg, body⟩ := head
    simp [compileFuns, ih]

/-- The flat recursive environment prepends the compiled function names. -/
theorem flatBuildRecEnv_names (funs : List (VarN × VarN × FlatLang.Exp))
    (closureEnv : FlatSem.Environment FlatSem.Value) (initial : List (VarN × FlatSem.Value)) :
    (FlatSem.buildRecEnv funs closureEnv initial).map Prod.fst = funs.map Prod.fst ++ initial.map Prod.fst := by
  have aux : ∀ remaining : List (VarN × VarN × FlatLang.Exp),
      (remaining.foldr (fun (name, _, _) rest => (name, FlatSem.Value.recclosure closureEnv funs name) :: rest) initial).map Prod.fst =
        remaining.map Prod.fst ++ initial.map Prod.fst := by
    intro remaining
    induction remaining with
    | nil => rfl
    | cons head tail _ =>
      obtain ⟨name, arg, body⟩ := head
      simp
  exact aux funs

/-- The compiler's recursive-name bindings agree with the extended local
trace list used by the arbitrary-environment induction hypothesis. -/
theorem bindRecNames_bindLocals (names : List VarN) (traces : List BackendCommon.Tra)
    (locals : List VarN) (compMap : Namespace ModN VarN VarName) :
    nsBindList (names.map (fun name => (name, VarName.localName .none name)))
        (bindLocals traces locals compMap) =
      bindLocals (List.replicate names.length .none ++ traces) (names ++ locals) compMap := by
  induction names with
  | nil => rfl
  | cons name tail ih =>
    simp only [List.map_cons, List.length_cons, List.replicate_succ, List.cons_append]
    simp only [nsBindList, List.foldr_cons]
    unfold nsBindList at ih
    rw [ih]
    simp [bindLocals, nsBindList]

/-- Appending related local environments preserves their value relation. -/
theorem envRel_nsAppend (genv : GlobalEnv)
    (left right : Namespace ModN VarN Value) (flatLeft flatRight : List (VarN × FlatSem.Value))
    (leftRel : EnvRel genv left flatLeft) (rightRel : EnvRel genv right flatRight) :
    EnvRel genv (nsAppend left right) (flatLeft ++ flatRight) := by
  induction flatLeft generalizing left with
  | nil =>
    cases leftRel
    cases right
    simpa [nsAppend, nsEmpty] using rightRel
  | cons head tail ih =>
    cases leftRel with
    | bind name value env flatEnv flat hEnv hValue =>
      have extended := EnvRel.bind genv name value (nsAppend env right) (tail ++ flatRight) flat (ih env hEnv) hValue
      cases env
      cases right
      simpa [nsAppend, nsBind] using extended

/-- Namespace concatenation is associative. -/
theorem local_nsAppend_assoc (a b c : Namespace ModN VarN Value) :
    nsAppend (nsAppend a b) c = nsAppend a (nsAppend b c) := by
  cases a
  cases b
  cases c
  simp [nsAppend, List.append_assoc]

/-- A selected pattern body can use the arbitrary-local induction hypothesis
with its related pattern bindings and compiler-generated traces. -/
theorem localEnvIH_patternBody {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (pattern : Pat) (body : AstHOL.Exp) (bodyIH : LocalEnvIH (F := F) interp transform body)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (baseEnv : SemEnv Value)
    (sourceLocal : Namespace ModN VarN Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (traces : List BackendCommon.Tra) (trace : List VarN) (baseMap : Environment) (gen : EnvironmentGenerationStore)
    (localRel : EnvRel genv sourceLocal flatEnv.v)
    (envInv : GlobalEnvInv genv baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv)
    (tracesLen : traces.length = flatEnv.v.length)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (bindings : List (VarN × Value)) (flatBindings : List (VarN × FlatSem.Value))
    (bindingRel : EnvRel genv (alistToNs bindings) flatBindings)
    (bindingNames : flatBindings.map Prod.fst = patBindings pattern)
    (safe : ∀ last, EvaluateHOL.evaluate source
      { baseEnv with v := nsAppend (alistToNs bindings) (nsAppend sourceLocal baseEnv.v) } [body] ≠
      (last, .err (.abort .typeError))) :
    LocalExpressionStep interp transform genv start finish other source flat
      { baseEnv with v := nsAppend (alistToNs bindings) (nsAppend sourceLocal baseEnv.v) }
      { flatEnv with v := flatBindings ++ flatEnv.v } trace
      { baseMap with v := nsBindList (patTups .none (patBindings pattern)) (bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v) } gen body := by
  obtain ⟨patternTraces, mapBind, patternLength⟩ := nsBindList_patTups_bindLocals
    (patBindings pattern) .none traces (flatEnv.v.map Prod.fst) baseMap.v
  have extendedRel := envRel_nsAppend genv (alistToNs bindings) sourceLocal flatBindings flatEnv.v bindingRel localRel
  have extendedInv : GlobalEnvInv genv baseMap (fun n => n ∈ (flatBindings ++ flatEnv.v).map Prod.fst) baseEnv := by
    cases envInv with
    | intro _ _ _ values constructors =>
      apply GlobalEnvInv.intro
      · intro id v fresh lookup
        apply values id v _ lookup
        intro ⟨n, mem, eq⟩
        apply fresh
        exact ⟨n, by simp [mem], eq⟩
      · exact constructors
  have bindingLength : flatBindings.length = (patBindings pattern).length := by
    have h := congrArg List.length bindingNames
    simpa using h
  obtain result := bodyIH genv start finish other source flat baseEnv
    (nsAppend (alistToNs bindings) sourceLocal) { flatEnv with v := flatBindings ++ flatEnv.v }
    (patternTraces ++ traces) trace baseMap gen extendedRel extendedInv
    (by simp [patternLength, bindingLength, tracesLen]) invariant generation
    (by simpa [local_nsAppend_assoc] using safe)
  simpa [local_nsAppend_assoc, List.map_append, bindingNames, ← mapBind] using result

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

/-- Local mutually recursive bindings preserve the arbitrary-environment
simulation when the body does. -/
theorem localEnvIH_letrec {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (funs : List (VarN × VarN × AstHOL.Exp)) (body : AstHOL.Exp)
    (bodyIH : LocalEnvIH (F := F) interp transform body) :
    LocalEnvIH (F := F) interp transform (.letrec funs body) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  let newTraces := List.replicate funs.length BackendCommon.Tra.none ++ traces
  let newMap := { compMap with v := nsBindList (funs.map Prod.fst |>.map (fun name => (name, VarName.localName .none name))) compMap.v }
  let compiled := compileFuns trace newMap funs
  let sourceLocal' := buildRecEnv funs sourceEnv sourceLocal
  let flatLocal' := FlatSem.buildRecEnv compiled flatEnv flatEnv.v
  have distinct : (funs.map Prod.fst).Nodup := by
    by_contra invalid
    apply safe source
    simp [EvaluateHOL.evaluate, invalid, EvaluateHOL.typeError]
  have names : flatLocal'.map Prod.fst = funs.map Prod.fst ++ flatEnv.v.map Prod.fst := by
    simp only [flatLocal', flatBuildRecEnv_names, compiled, compileFuns_local_names]
  have mapBind : bindLocals newTraces (funs.map Prod.fst ++ flatEnv.v.map Prod.fst) baseMap.v = newMap.v := by
    simpa [newTraces, newMap, compMap] using (bindRecNames_bindLocals (funs.map Prod.fst) traces (flatEnv.v.map Prod.fst) baseMap.v).symm
  have extendedRel : EnvRel genv sourceLocal' flatLocal' := by
    have related := localRecEnv_related genv baseMap baseEnv sourceLocal flatEnv funs trace newTraces
      localRel envInv (by simp [newTraces, tracesLen])
    simpa only [sourceLocal', sourceEnv, flatLocal', compiled, newMap, compMap, mapBind] using related
  have extendedInv : GlobalEnvInv genv baseMap (fun n => n ∈ flatLocal'.map Prod.fst) baseEnv := by
    cases envInv with
    | intro _ _ _ values constructors =>
      apply GlobalEnvInv.intro
      · intro id v fresh lookup
        apply values id v _ lookup
        intro ⟨n, mem, eq⟩
        apply fresh
        exact ⟨n, by rw [names]; simp [mem], eq⟩
      · exact constructors
  have sourceBind : nsAppend sourceLocal' baseEnv.v = buildRecEnv funs sourceEnv sourceEnv.v := by
    simpa [sourceLocal'] using (buildRecEnv_nsAppend funs sourceEnv sourceLocal baseEnv.v).symm
  have bodySafe : ∀ last, EvaluateHOL.evaluate source { sourceEnv with v := buildRecEnv funs sourceEnv sourceEnv.v }
      [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    simpa [EvaluateHOL.evaluate, distinct] using bad
  have localLength : flatLocal'.length = funs.length + flatEnv.v.length := by
    have h := congrArg List.length names
    simpa using h
  obtain ⟨nextGenv, bodySim, bodyPost⟩ := bodyIH genv start finish other source flat baseEnv sourceLocal'
    { flatEnv with v := flatLocal' } newTraces trace baseMap gen extendedRel extendedInv
    (by simp [newTraces, tracesLen, localLength]) invariant generation (by simpa [sourceBind] using bodySafe)
  have bodySim : ExprSim nextGenv newMap trace
      { sourceEnv with v := buildRecEnv funs sourceEnv sourceEnv.v } { flatEnv with v := flatLocal' }
      source flat body := by
    simpa [sourceBind, names, mapBind] using bodySim
  simp only [sourceBind, names, mapBind] at bodyPost
  have sourceOuter : EvaluateHOL.evaluate source sourceEnv [.letrec funs body] =
      EvaluateHOL.evaluate source { sourceEnv with v := buildRecEnv funs sourceEnv sourceEnv.v } [body] := by
    simp [EvaluateHOL.evaluate, distinct]
  have flatOuter : FlatSem.evaluate flatEnv flat [compileExp trace compMap (.letrec funs body)] =
      FlatSem.evaluate { flatEnv with v := flatLocal' } flat [compileExp trace newMap body] := by
    simp [compileExp, FlatSem.evaluate, compiled, flatLocal', newMap, compileFuns_local_names, distinct]
  refine ⟨nextGenv, ?_, ?_⟩
  · unfold ExprSim at bodySim ⊢
    rw [sourceOuter, flatOuter]
    exact bodySim
  · rw [sourceOuter, flatOuter]
    exact bodyPost

/-- An arbitrary-environment induction hypothesis specializes to the empty
local environment used by declaration expressions. -/
theorem localEnvIH_to_factored {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expr : AstHOL.Exp) (ih : LocalEnvIH (F := F) interp transform expr) :
    FactoredExpressionIH (F := F) interp transform expr := by
  intro genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation safe
  have emptyAppend : nsAppend nsEmpty sourceEnv.v = sourceEnv.v := by
    cases sourceEnv.v
    rfl
  have sourceEq : { sourceEnv with v := nsAppend nsEmpty sourceEnv.v } = sourceEnv := by
    simp only [emptyAppend]
  have mapEq : { compMap with v := bindLocals [] [] compMap.v } = compMap := by
    simp [bindLocals, nsBindList]
  have step := ih genv start finish other source flat sourceEnv nsEmpty ⟨[]⟩ [] trace compMap gen
    (.empty genv) (by simpa using envInv) rfl invariant generation (by simpa only [sourceEq] using safe)
  apply (localExpressionStep_empty interp transform genv start finish other source flat sourceEnv trace compMap gen expr).mp
  simpa only [List.map_nil, sourceEq, mapEq] using step

private theorem nsLookup_bind_same {α : Type} (env : Namespace ModN VarN α) (name : VarN) (value : α) :
    nsLookup (nsBind name value env) (.short name) = some value := by
  cases env
  simp [nsBind, nsLookup]

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
        exact nsLookup_bind_same _ name _
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
      rw [nsLookup_bind_same] at missing
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

private theorem localLookup_exists_iff_mem (entries : List (VarN × FlatSem.Value)) (name : VarN) :
    (∃ value, entries.lookup name = some value) ↔ name ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
    obtain ⟨key, value⟩ := entry
    by_cases equal : name = key
    · subst key
      simp
    · simp [List.lookup_cons, BEq.beq, equal, ih]

/-- Variable lookup respects local shadowing and falls back to the related
global environment for names absent from the local stack. -/
theorem localEnvIH_variable {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (id : Ident ModN VarN) : LocalEnvIH (F := F) interp transform (.var id) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen
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
        obtain ⟨v, found⟩ := (localLookup_exists_iff_mem flatEnv.v name).mpr member
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

/-- A first set of recursively nested named bindings, literals, and closure
creation, using arbitrary related local environments. -/
inductive LocalEnvExpression : AstHOL.Exp → Prop where
  | literal (lit : Lit) : LocalEnvExpression (.lit lit)
  | variable_ (id : Ident ModN VarN) : LocalEnvExpression (.var id)
  | function_ (name : VarN) (body : AstHOL.Exp) : LocalEnvExpression (.fn name body)
  | letNamed (name : VarN) (first body : AstHOL.Exp) : LocalEnvExpression first → LocalEnvExpression body →
      LocalEnvExpression (.let_ (some name) first body)

/-- Covered expressions satisfy the preliminary arbitrary-local induction
hypothesis, whose relations remain pending HOL review. -/
theorem localEnvIH_covered {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expr : AstHOL.Exp) (covered : LocalEnvExpression expr) : LocalEnvIH (F := F) interp transform expr := by
  induction covered with
  | literal lit => exact localEnvIH_literal interp transform lit
  | variable_ id => exact localEnvIH_variable interp transform id
  | function_ name body => exact localEnvIH_function interp transform name body
  | letNamed name first body _ _ firstIH bodyIH =>
    exact localEnvIH_let_named interp transform name first body firstIH bodyIH

end Flapjack.Compiler.Backend.SourceToFlat

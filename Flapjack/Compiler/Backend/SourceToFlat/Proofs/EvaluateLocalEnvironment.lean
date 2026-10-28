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

/-- A first set of recursively nested named bindings, literals, and closure
creation, using arbitrary related local environments. -/
inductive LocalEnvExpression : AstHOL.Exp → Prop where
  | literal (lit : Lit) : LocalEnvExpression (.lit lit)
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
  | function_ name body => exact localEnvIH_function interp transform name body
  | letNamed name first body _ _ firstIH bodyIH =>
    exact localEnvIH_let_named interp transform name first body firstIH bodyIH

end Flapjack.Compiler.Backend.SourceToFlat

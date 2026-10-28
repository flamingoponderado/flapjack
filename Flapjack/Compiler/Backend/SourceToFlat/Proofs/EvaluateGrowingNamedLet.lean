import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateGrowingEquality

/-! Growing expression simulation in a local environment. These factored
relations and this composition lemma are not yet reviewed HOL ports. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- A growing expression step with an explicit flat local environment. -/
def LocalExpressionStep {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (trace : List VarN)
    (compMap : Environment) (gen : EnvironmentGenerationStore) (expr : AstHOL.Exp) : Prop :=
  let result := EvaluateHOL.evaluate source sourceEnv [expr]
  let flatResult := FlatSem.evaluate flatEnv flat [compileExp trace compMap expr]
  ∃ nextGenv, ExprSim nextGenv compMap trace sourceEnv flatEnv source flat expr ∧
    match result.2 with
    | .err (.abort _) => True
    | _ => GlobalGrowth genv nextGenv ∧
        factoredInvariant interp transform gen nextGenv (start, finish, other) result.1 flatResult.1 ∧
        envGenRel gen result.1.evalState ∧ oracForwardRel interp source.evalState result.1.evalState

/-- A declaration expression step is the empty-local instance of the more
general step. -/
theorem localExpressionStep_empty {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore) (expr : AstHOL.Exp) :
    LocalExpressionStep interp transform genv start finish other source flat sourceEnv ⟨[]⟩ trace compMap gen expr ↔
      DletExpressionStep interp transform genv start finish other source flat sourceEnv trace compMap gen expr := by
  rfl

/-- Compose a growing initializer with a growing body simulation in the
extended environments. The body premise is the remaining local induction
hypothesis; it is not derived by this lemma. -/
theorem factoredExpressionIH_let_named_of_local {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (first body : AstHOL.Exp)
    (firstIH : FactoredExpressionIH (F := F) interp transform first)
    (bodyIH : ∀ (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
      (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
      (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore)
      (value : Value) (flatValue : FlatSem.Value),
      ValueRel genv value flatValue →
      factoredInvariant interp transform gen genv (start, finish, other) source flat →
      envGenRel gen source.evalState →
      (∀ last, EvaluateHOL.evaluate source { sourceEnv with v := nsBind name value sourceEnv.v } [body] ≠
        (last, .err (.abort .typeError))) →
      LocalExpressionStep interp transform genv start finish other source flat
        { sourceEnv with v := nsBind name value sourceEnv.v } ⟨[(name, flatValue)]⟩ trace
        { compMap with v := nsBind name (.localName .none name) compMap.v } gen body) :
    FactoredExpressionIH (F := F) interp transform (.let_ (some name) first body) := by
  intro genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation safe
  have firstSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [first] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, bad]
  obtain ⟨middleGenv, firstSim, firstPost⟩ := firstIH genv start finish other source flat sourceEnv
    (name :: trace) compMap gen envInv invariant generation firstSafe
  unfold ExprSim at firstSim
  generalize sourceFirst : EvaluateHOL.evaluate source sourceEnv [first] = sourceResult at firstSim firstPost
  obtain ⟨middleSource, sourceResult⟩ := sourceResult
  generalize flatFirst : FlatSem.evaluate ⟨[]⟩ flat [compileExp (name :: trace) compMap first] = flatResult at firstSim firstPost
  obtain ⟨middleFlat, flatResult⟩ := flatResult
  obtain ⟨firstRelated, firstStates⟩ := firstSim
  cases firstRelated with
  | abort error =>
    refine ⟨middleGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations ⟨[]⟩ flat
        [compileExp (name :: trace) compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatFirst]
      exact ⟨.abort error, firstStates⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
      trivial
  | raise valueRel =>
    refine ⟨middleGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations ⟨[]⟩ flat
        [compileExp (name :: trace) compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatFirst]
      exact ⟨.raise valueRel, firstStates⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations ⟨[]⟩ flat
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
        have bodySafe : ∀ last, EvaluateHOL.evaluate middleSource
            { sourceEnv with v := nsBind name value sourceEnv.v } [body] ≠ (last, .err (.abort .typeError)) := by
          intro last bad
          apply safe last
          rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
          simpa [nsOptBind, EvaluateHOL.headValue, Flapjack.holHd] using bad
        obtain ⟨finalGenv, bodySim, bodyPost⟩ := bodyIH middleGenv start finish other middleSource middleFlat
          sourceEnv trace compMap gen value flatValue related middleInvariant middleGeneration bodySafe
        have sourceOuter : EvaluateHOL.evaluate source sourceEnv [.let_ (some name) first body] =
            EvaluateHOL.evaluate middleSource { sourceEnv with v := nsBind name value sourceEnv.v } [body] := by
          rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
          simp [nsOptBind, EvaluateHOL.headValue, Flapjack.holHd]
        have flatOuter : FlatSem.evaluate ⟨[]⟩ flat [compileExp trace compMap (.let_ (some name) first body)] =
            FlatSem.evaluate ⟨[(name, flatValue)]⟩ middleFlat
              [compileExp trace { compMap with v := nsBind name (.localName .none name) compMap.v } body] := by
          rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations ⟨[]⟩ flat
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

/-- Looking up the newly bound variable preserves the growing step, even
when it shadows a source or compilation environment binding. -/
theorem localExpressionStep_boundVariable {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (name : VarN) (value : Value) (flatValue : FlatSem.Value)
    (related : ValueRel genv value flatValue)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState) :
    LocalExpressionStep interp transform genv start finish other source flat
      { sourceEnv with v := nsBind name value sourceEnv.v } ⟨[(name, flatValue)]⟩ trace
      { compMap with v := nsBind name (.localName .none name) compMap.v } gen (.var (.short name)) := by
  have sourceRun : EvaluateHOL.evaluate source { sourceEnv with v := nsBind name value sourceEnv.v }
      [.var (.short name)] = (source, .val [value]) := by
    cases sourceEnv.v with
    | bind values modules => simp [EvaluateHOL.evaluate, nsLookup, nsBind]
  have flatRun : FlatSem.evaluate ⟨[(name, flatValue)]⟩ flat
      [compileExp trace { compMap with v := nsBind name (.localName .none name) compMap.v }
        (.var (.short name))] = (flat, .val [flatValue]) := by
    cases compMap.v with
    | bind values modules =>
      simp [compileExp, nsLookup, nsBind, compileVar, FlatSem.evaluate]
  refine ⟨genv, ?_, ?_⟩
  · unfold ExprSim
    rw [sourceRun, flatRun]
    exact ⟨.value (.cons related .nil), invariant.2.2.1⟩
  · rw [sourceRun, flatRun]
    exact ⟨GlobalGrowth.refl genv, invariant, generation, oracForwardRel_refl interp source.evalState⟩

/-- A named binding whose body returns the bound value satisfies the growing
declaration-expression induction hypothesis. -/
theorem factoredExpressionIH_let_named_self {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (first : AstHOL.Exp)
    (firstIH : FactoredExpressionIH (F := F) interp transform first) :
    FactoredExpressionIH (F := F) interp transform (.let_ (some name) first (.var (.short name))) := by
  apply factoredExpressionIH_let_named_of_local interp transform name first (.var (.short name)) firstIH
  intro genv start finish other source flat sourceEnv trace compMap gen value flatValue related invariant generation _
  exact localExpressionStep_boundVariable interp transform genv start finish other source flat sourceEnv trace
    compMap gen name value flatValue related invariant generation

end Flapjack.Compiler.Backend.SourceToFlat

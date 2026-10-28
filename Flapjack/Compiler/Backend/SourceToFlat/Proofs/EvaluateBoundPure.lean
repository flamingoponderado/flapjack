import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateGrowingNamedLet

/-! State-preserving local expression simulation for named bindings. The
factored relations are preliminary and have not completed HOL review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Local expressions built from the bound variable, literals, tuples and
annotations. Tuple arguments may themselves contain tuples. -/
inductive BoundPureExpression (name : VarN) : AstHOL.Exp → Prop where
  | boundVar : BoundPureExpression name (.var (.short name))
  | literal (lit : Lit) : BoundPureExpression name (.lit lit)
  | tuple (args : List AstHOL.Exp) :
      (∀ expr, expr ∈ args → BoundPureExpression name expr) → BoundPureExpression name (.con none args)
  | tannot (expr : AstHOL.Exp) (typ : AstT) :
      BoundPureExpression name expr → BoundPureExpression name (.tannot expr typ)
  | lannot (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) :
      BoundPureExpression name expr → BoundPureExpression name (.lannot expr loc)

/-- The covered local expressions simulate each other and preserve both
states, including when the bound name shadows an older binding. -/
theorem boundPure_simulation {C F : Type} (genv : GlobalEnv) (name : VarN)
    (value : Value) (flatValue : FlatSem.Value) (related : ValueRel genv value flatValue)
    (sourceEnv : SemEnv Value) (trace : List VarN) (compMap : Environment)
    (expr : AstHOL.Exp) (covered : BoundPureExpression name expr) :
    ∀ (source : State F) (flat : FlatSem.State C F), StateRel genv source flat →
      ExprSim genv { compMap with v := nsBind name (.localName .none name) compMap.v } trace
        { sourceEnv with v := nsBind name value sourceEnv.v } ⟨[(name, flatValue)]⟩ source flat expr ∧
      (EvaluateHOL.evaluate source { sourceEnv with v := nsBind name value sourceEnv.v } [expr]).1 = source ∧
      (FlatSem.evaluate ⟨[(name, flatValue)]⟩ flat
        [compileExp trace { compMap with v := nsBind name (.localName .none name) compMap.v } expr]).1 = flat := by
  induction covered with
  | boundVar =>
    intro source flat states
    have sourceRun : EvaluateHOL.evaluate source { sourceEnv with v := nsBind name value sourceEnv.v }
        [.var (.short name)] = (source, .val [value]) := by
      cases sourceEnv.v with
      | bind values modules => simp [EvaluateHOL.evaluate, nsLookup, nsBind]
    have flatRun : FlatSem.evaluate ⟨[(name, flatValue)]⟩ flat
        [compileExp trace { compMap with v := nsBind name (.localName .none name) compMap.v }
          (.var (.short name))] = (flat, .val [flatValue]) := by
      cases compMap.v with
      | bind values modules => simp [compileExp, nsLookup, nsBind, compileVar, FlatSem.evaluate]
    refine ⟨?_, ?_, ?_⟩
    · unfold ExprSim
      rw [sourceRun, flatRun]
      exact ⟨.value (.cons related .nil), states⟩
    · rw [sourceRun]
    · rw [flatRun]
  | literal lit =>
    intro source flat states
    refine ⟨exprSim_literal genv _ trace _ _ source flat states lit, ?_, ?_⟩ <;>
      simp [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate]
  | tuple args _ ih =>
    intro source flat states
    let env := { sourceEnv with v := nsBind name value sourceEnv.v }
    let fenv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
    let cmap := { compMap with v := nsBind name (.localName .none name) compMap.v }
    have listSim : ExprListSim genv cmap trace env fenv source flat args.reverse := by
      apply exprListSim_of_expressions genv cmap trace env fenv args.reverse
      · intro e member s f rel
        exact (ih e (by simpa using member) s f rel).1
      · exact states
    have sourceArgs : (EvaluateHOL.evaluate source env args.reverse).1 = source := by
      apply evaluateList_state_of_singletons
      intro e member
      exact (ih e (by simpa using member) source flat states).2.1
    have flatArgs : (FlatSem.evaluate fenv flat (compileExps trace cmap args).reverse).1 = flat := by
      rw [← compileExps_reverse]
      apply flatEvaluateList_state_of_singletons
      intro e member
      exact (ih e (by simpa using member) source flat states).2.2
    have unchanged := constructor_states_of_args source env flat fenv trace cmap none args sourceArgs flatArgs
    exact ⟨exprSim_tuple genv cmap trace env fenv source flat args listSim, unchanged.1, unchanged.2⟩
  | tannot expr typ _ ih =>
    intro source flat states
    obtain ⟨sim, sourceSame, flatSame⟩ := ih source flat states
    exact ⟨exprSim_tannot genv _ trace _ _ source flat expr typ sim,
      by simpa [EvaluateHOL.evaluate] using sourceSame,
      by simpa [compileExp] using flatSame⟩
  | lannot expr loc _ ih =>
    intro source flat states
    obtain ⟨sim, sourceSame, flatSame⟩ := ih source flat states
    refine ⟨exprSim_lannot genv _ trace _ _ source flat expr loc sim, ?_, ?_⟩
    · cases loc; simpa [EvaluateHOL.evaluate] using sourceSame
    · simpa [compileExp] using flatSame

/-- State-preserving covered local bodies discharge the growing step. -/
theorem localExpressionStep_boundPure {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (name : VarN) (value : Value) (flatValue : FlatSem.Value) (expr : AstHOL.Exp)
    (covered : BoundPureExpression name expr) (related : ValueRel genv value flatValue)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState) :
    LocalExpressionStep interp transform genv start finish other source flat
      { sourceEnv with v := nsBind name value sourceEnv.v } ⟨[(name, flatValue)]⟩ trace
      { compMap with v := nsBind name (.localName .none name) compMap.v } gen expr := by
  obtain ⟨sim, sourceSame, flatSame⟩ := boundPure_simulation genv name value flatValue related sourceEnv trace
    compMap expr covered source flat invariant.2.2.1
  refine ⟨genv, sim, ?_⟩
  cases result : (EvaluateHOL.evaluate source { sourceEnv with v := nsBind name value sourceEnv.v } [expr]).2 with
  | val values =>
    simp only [sourceSame, flatSame]
    exact ⟨GlobalGrowth.refl genv, invariant, generation, oracForwardRel_refl interp source.evalState⟩
  | err error =>
    cases error with
    | abort error => simp
    | raise value =>
      simp only [sourceSame, flatSame]
      exact ⟨GlobalGrowth.refl genv, invariant, generation, oracForwardRel_refl interp source.evalState⟩

/-- Named bindings with covered local bodies satisfy the preliminary growing
declaration-expression induction hypothesis. -/
theorem factoredExpressionIH_let_named_pure {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (first body : AstHOL.Exp) (covered : BoundPureExpression name body)
    (firstIH : FactoredExpressionIH (F := F) interp transform first) :
    FactoredExpressionIH (F := F) interp transform (.let_ (some name) first body) := by
  apply factoredExpressionIH_let_named_of_local interp transform name first body firstIH
  intro genv start finish other source flat sourceEnv trace compMap gen value flatValue related invariant generation _
  exact localExpressionStep_boundPure interp transform genv start finish other source flat sourceEnv trace
    compMap gen name value flatValue body covered related invariant generation

end Flapjack.Compiler.Backend.SourceToFlat

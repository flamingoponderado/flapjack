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

/-- Expression trees may contain named bindings whose bodies are covered
local pure expressions, alongside the previously covered constructs. -/
inductive FactoredBoundExpression : AstHOL.Exp → Prop where
  | base (expr : AstHOL.Exp) : FactoredEqualityExpression expr → FactoredBoundExpression expr
  | constructor (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp) :
      (∀ expr, expr ∈ args → FactoredBoundExpression expr) → FactoredBoundExpression (.con name args)
  | raise_ (body : AstHOL.Exp) : FactoredBoundExpression body → FactoredBoundExpression (.raise body)
  | letAnonymous (first body : AstHOL.Exp) : FactoredBoundExpression first → FactoredBoundExpression body →
      FactoredBoundExpression (.let_ none first body)
  | letNamed (name : VarN) (first body : AstHOL.Exp) : FactoredBoundExpression first →
      BoundPureExpression name body → FactoredBoundExpression (.let_ (some name) first body)
  | if_ (cond yes no : AstHOL.Exp) : FactoredBoundExpression cond → FactoredBoundExpression yes →
      FactoredBoundExpression no → FactoredBoundExpression (.if_ cond yes no)
  | log (op : Lop) (left right : AstHOL.Exp) : FactoredBoundExpression left → FactoredBoundExpression right →
      FactoredBoundExpression (.log op left right)
  | integerArith (action : Arith) (left right : AstHOL.Exp) : FactoredBoundExpression left →
      FactoredBoundExpression right → FactoredBoundExpression (.app (.arith action .intT) [left, right])
  | test (test : Test) (typ : PrimType) (left right : AstHOL.Exp) : FactoredBoundExpression left →
      FactoredBoundExpression right → FactoredBoundExpression (.app (.test test typ) [left, right])
  | equality (left right : AstHOL.Exp) : FactoredBoundExpression left →
      FactoredBoundExpression right → FactoredBoundExpression (.app .equality [left, right])
  | tannot (expr : AstHOL.Exp) (typ : AstT) : FactoredBoundExpression expr → FactoredBoundExpression (.tannot expr typ)
  | lannot (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) : FactoredBoundExpression expr →
      FactoredBoundExpression (.lannot expr loc)

/-- Covered expression trees satisfy the preliminary growing induction
hypothesis; this is not a reviewed HOL theorem. -/
theorem factoredExpressionIH_boundTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expr : AstHOL.Exp) (covered : FactoredBoundExpression expr) :
    FactoredExpressionIH (F := F) interp transform expr := by
  induction covered with
  | base expr supported => exact factoredExpressionIH_equalityTree interp transform expr supported
  | constructor name args _ ih => exact factoredExpressionIH_constructor interp transform name args ih
  | raise_ body _ ih => exact factoredExpressionIH_raise interp transform body ih
  | letAnonymous first body _ _ firstIH bodyIH =>
    exact factoredExpressionIH_let_anonymous interp transform first body firstIH bodyIH
  | letNamed name first body _ pure firstIH =>
    exact factoredExpressionIH_let_named_pure interp transform name first body pure firstIH
  | if_ cond yes no _ _ _ condIH yesIH noIH => exact factoredExpressionIH_if interp transform cond yes no condIH yesIH noIH
  | log op left right _ _ leftIH rightIH => exact factoredExpressionIH_log interp transform op left right leftIH rightIH
  | integerArith action left right _ _ leftIH rightIH =>
    exact factoredExpressionIH_integerArith interp transform action left right leftIH rightIH
  | test test typ left right _ _ leftIH rightIH =>
    exact factoredExpressionIH_test interp transform test typ left right leftIH rightIH
  | equality left right _ _ leftIH rightIH =>
    exact factoredExpressionIH_equality interp transform left right leftIH rightIH
  | tannot expr typ _ ih =>
    intro genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation safe
    apply dletExpressionStep_tannot interp transform genv start finish other source flat sourceEnv trace compMap gen expr typ
    apply ih genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation
    intro last bad
    apply safe last
    simpa [EvaluateHOL.evaluate] using bad
  | lannot expr loc _ ih =>
    intro genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation safe
    apply dletExpressionStep_lannot interp transform genv start finish other source flat sourceEnv trace compMap gen expr loc
    apply ih genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation
    intro last bad
    apply safe last
    cases loc
    simpa [EvaluateHOL.evaluate] using bad

end Flapjack.Compiler.Backend.SourceToFlat

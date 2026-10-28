import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateGrowingRaise

/-! Anonymous let sequencing over the preliminary growing expression
simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Anonymous let sequences two growing expression induction hypotheses,
propagating errors from the first expression without evaluating the body. -/
theorem factoredExpressionIH_let_anonymous {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (first body : AstHOL.Exp) (firstIH : FactoredExpressionIH (F := F) interp transform first)
    (bodyIH : FactoredExpressionIH (F := F) interp transform body) :
    FactoredExpressionIH (F := F) interp transform (.let_ none first body) := by
  intro genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation safe
  have firstSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [first] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, bad]
  obtain ⟨middleGenv, firstSim, firstPost⟩ := firstIH genv start finish other source flat sourceEnv trace compMap gen
    envInv invariant generation firstSafe
  unfold ExprSim at firstSim
  generalize sourceFirst : EvaluateHOL.evaluate source sourceEnv [first] = sourceResult at firstSim firstPost
  obtain ⟨middleSource, sourceResult⟩ := sourceResult
  generalize flatFirst : FlatSem.evaluate ⟨[]⟩ flat [compileExp trace compMap first] = flatResult at firstSim firstPost
  obtain ⟨middleFlat, flatResult⟩ := flatResult
  obtain ⟨firstRelated, firstStates⟩ := firstSim
  cases firstRelated with
  | abort error =>
    refine ⟨middleGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations ⟨[]⟩ flat
        [compileExp trace compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatFirst]
      exact ⟨.abort error, firstStates⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
      trivial
  | raise valueRel =>
    refine ⟨middleGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations ⟨[]⟩ flat
        [compileExp trace compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatFirst]
      exact ⟨.raise valueRel, firstStates⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations ⟨[]⟩ flat
        [compileExp trace compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatFirst]
      exact firstPost
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨sourceValue, sourceEq⟩ := EvaluateProps.evaluateSingFull source middleSource sourceEnv first sourceValues sourceFirst
    subst sourceValues
    cases valuesRel with
    | cons related tail =>
      cases tail with
      | nil =>
        obtain ⟨firstGrowth, middleInvariant, middleGeneration, firstForward⟩ := firstPost
        have middleEnv := globalEnvInv_growth genv middleGenv firstGrowth compMap (fun _ => False) sourceEnv envInv
        have bodySafe : ∀ last, EvaluateHOL.evaluate middleSource sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
          intro last bad
          apply safe last
          rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
          simpa [nsOptBind] using bad
        obtain ⟨finalGenv, bodySim, bodyPost⟩ := bodyIH middleGenv start finish other middleSource middleFlat sourceEnv
          trace compMap gen middleEnv middleInvariant middleGeneration bodySafe
        have sourceOuter : EvaluateHOL.evaluate source sourceEnv [.let_ none first body] =
            EvaluateHOL.evaluate middleSource sourceEnv [body] := by
          rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
          simp [nsOptBind]
        have flatOuter : FlatSem.evaluate ⟨[]⟩ flat [compileExp trace compMap (.let_ none first body)] =
            FlatSem.evaluate ⟨[]⟩ middleFlat [compileExp trace compMap body] := by
          rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations ⟨[]⟩ flat
            [compileExp trace compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatFirst]
        refine ⟨finalGenv, ?_, ?_⟩
        · unfold ExprSim at bodySim ⊢
          rw [sourceOuter, flatOuter]
          exact bodySim
        · rw [sourceOuter, flatOuter]
          cases result : (EvaluateHOL.evaluate middleSource sourceEnv [body]).2 with
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

/-- Covered expressions including anonymous let sequencing, constructors,
and raises, using the preliminary factored relations. -/
inductive FactoredLetExpression : AstHOL.Exp → Prop where
  | base (expr : AstHOL.Exp) : FactoredRaisedExpression expr → FactoredLetExpression expr
  | constructor (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp) :
      (∀ expr, expr ∈ args → FactoredLetExpression expr) → FactoredLetExpression (.con name args)
  | raise_ (body : AstHOL.Exp) : FactoredLetExpression body → FactoredLetExpression (.raise body)
  | letAnonymous (first body : AstHOL.Exp) : FactoredLetExpression first → FactoredLetExpression body →
      FactoredLetExpression (.let_ none first body)
  | tannot (expr : AstHOL.Exp) (typ : AstT) : FactoredLetExpression expr → FactoredLetExpression (.tannot expr typ)
  | lannot (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) : FactoredLetExpression expr →
      FactoredLetExpression (.lannot expr loc)

/-- Covered expressions satisfy the factored growing induction hypothesis. -/
theorem factoredExpressionIH_letTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expr : AstHOL.Exp) (covered : FactoredLetExpression expr) :
    FactoredExpressionIH (F := F) interp transform expr := by
  induction covered with
  | base expr supported => exact factoredExpressionIH_raisedTree interp transform expr supported
  | constructor name args _ ih => exact factoredExpressionIH_constructor interp transform name args ih
  | raise_ body _ ih => exact factoredExpressionIH_raise interp transform body ih
  | letAnonymous first body _ _ firstIH bodyIH =>
    exact factoredExpressionIH_let_anonymous interp transform first body firstIH bodyIH
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

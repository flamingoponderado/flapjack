import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateGrowingLet

/-! Conditional expression composition over the preliminary growing
source-to-flat simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- A conditional composes the growing induction hypotheses for its
condition and selected branch, preserving early errors. -/
theorem factoredExpressionIH_if {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (cond yes no : AstHOL.Exp) (condIH : FactoredExpressionIH (F := F) interp transform cond)
    (yesIH : FactoredExpressionIH (F := F) interp transform yes)
    (noIH : FactoredExpressionIH (F := F) interp transform no) :
    FactoredExpressionIH (F := F) interp transform (.if_ cond yes no) := by
  intro genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation safe
  have condSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [cond] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [cond] []).1, bad]
  obtain ⟨middleGenv, condSim, condPost⟩ := condIH genv start finish other source flat sourceEnv trace compMap gen
    envInv invariant generation condSafe
  have condSimCopy := condSim
  unfold ExprSim at condSim
  generalize sourceCond : EvaluateHOL.evaluate source sourceEnv [cond] = sourceResult at condSim condPost
  obtain ⟨middleSource, sourceResult⟩ := sourceResult
  generalize flatCond : FlatSem.evaluate ⟨[]⟩ flat [compileExp trace compMap cond] = flatResult at condSim condPost
  obtain ⟨middleFlat, flatResult⟩ := flatResult
  obtain ⟨condRelated, condStates⟩ := condSim
  cases condRelated with
  | abort error =>
    refine ⟨middleGenv, exprSim_if_error middleGenv compMap trace sourceEnv ⟨[]⟩ source flat cond yes no
      middleSource (.abort error) sourceCond condSimCopy, ?_⟩
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [cond] []).1, sourceCond]
    trivial
  | raise valueRel =>
    refine ⟨middleGenv, exprSim_if_error middleGenv compMap trace sourceEnv ⟨[]⟩ source flat cond yes no
      middleSource (.raise _) sourceCond condSimCopy, ?_⟩
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [cond] []).1, sourceCond]
    rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations ⟨[]⟩ flat
      [compileExp trace compMap cond] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatCond]
    exact condPost
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨conditionValue, sourceEq⟩ := EvaluateProps.evaluateSingFull source middleSource sourceEnv cond sourceValues sourceCond
    subst sourceValues
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        cases selection : SemanticPrimitivesHOL.doIf conditionValue yes no with
        | none =>
          have bad : EvaluateHOL.evaluate source sourceEnv [.if_ cond yes no] =
              (middleSource, .err (.abort .typeError)) := by
            rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [cond] []).1, sourceCond]
            simp only [EvaluateHOL.headValue, Flapjack.holHd]
            rw [selection]
            rfl
          exact False.elim (safe middleSource bad)
        | some branch =>
          obtain ⟨b, valueEq, _⟩ := SemanticPrimitivesHOL.doIf_success_boolean conditionValue yes no branch selection
          subst conditionValue
          obtain ⟨condGrowth, middleInvariant, middleGeneration, condForward⟩ := condPost
          have flatBoolean := (boolValueRel_iff middleGenv middleInvariant.1 b _).mp valueRel
          subst_vars
          have middleEnv := globalEnvInv_growth genv middleGenv condGrowth compMap (fun _ => False) sourceEnv envInv
          have sourceOuter : EvaluateHOL.evaluate source sourceEnv [.if_ cond yes no] =
              EvaluateHOL.evaluate middleSource sourceEnv [if b then yes else no] := by
            rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [cond] []).1, sourceCond]
            simp only [EvaluateHOL.headValue, Flapjack.holHd]
            rw [SemanticPrimitivesHOL.doIf_boolValue]
          have flatOuter : FlatSem.evaluate ⟨[]⟩ flat [compileExp trace compMap (.if_ cond yes no)] =
              FlatSem.evaluate ⟨[]⟩ middleFlat [compileExp trace compMap (if b then yes else no)] := by
            rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations ⟨[]⟩ flat
              [compileExp trace compMap cond] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatCond]
            cases b <;> simp [FlatSem.doIf, FlatSem.boolValue, BackendCommon.boolToTag,
              BackendCommon.trueTag, BackendCommon.falseTag, FlatLang.boolId]
          have branchSafe : ∀ last, EvaluateHOL.evaluate middleSource sourceEnv [if b then yes else no] ≠
              (last, .err (.abort .typeError)) := by
            intro last bad
            apply safe last
            exact sourceOuter.trans bad
          have branchIH : FactoredExpressionIH (F := F) interp transform (if b then yes else no) := by
            cases b <;> simp_all
          obtain ⟨finalGenv, branchSim, branchPost⟩ := branchIH middleGenv start finish other middleSource middleFlat
            sourceEnv trace compMap gen middleEnv middleInvariant middleGeneration branchSafe
          refine ⟨finalGenv, ?_, ?_⟩
          · unfold ExprSim at branchSim ⊢
            rw [sourceOuter, flatOuter]
            exact branchSim
          · rw [sourceOuter, flatOuter]
            cases result : (EvaluateHOL.evaluate middleSource sourceEnv [if b then yes else no]).2 with
            | err error =>
              cases error with
              | abort error => simp
              | raise value =>
                rw [result] at branchPost
                obtain ⟨growth, finalInvariant, finalGeneration, branchForward⟩ := branchPost
                exact ⟨condGrowth.trans growth, finalInvariant, finalGeneration,
                  oracForwardRel_trans interp _ _ _ ⟨condForward, branchForward⟩⟩
            | val values =>
              rw [result] at branchPost
              obtain ⟨growth, finalInvariant, finalGeneration, branchForward⟩ := branchPost
              exact ⟨condGrowth.trans growth, finalInvariant, finalGeneration,
                oracForwardRel_trans interp _ _ _ ⟨condForward, branchForward⟩⟩

/-- Expression coverage including conditionals and the previously covered
constructor, raise and anonymous-let forms. -/
inductive FactoredIfExpression : AstHOL.Exp → Prop where
  | base (expr : AstHOL.Exp) : FactoredLetExpression expr → FactoredIfExpression expr
  | constructor (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp) :
      (∀ expr, expr ∈ args → FactoredIfExpression expr) → FactoredIfExpression (.con name args)
  | raise_ (body : AstHOL.Exp) : FactoredIfExpression body → FactoredIfExpression (.raise body)
  | letAnonymous (first body : AstHOL.Exp) : FactoredIfExpression first → FactoredIfExpression body →
      FactoredIfExpression (.let_ none first body)
  | if_ (cond yes no : AstHOL.Exp) : FactoredIfExpression cond → FactoredIfExpression yes →
      FactoredIfExpression no → FactoredIfExpression (.if_ cond yes no)
  | tannot (expr : AstHOL.Exp) (typ : AstT) : FactoredIfExpression expr → FactoredIfExpression (.tannot expr typ)
  | lannot (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) : FactoredIfExpression expr →
      FactoredIfExpression (.lannot expr loc)

/-- Covered conditional expressions satisfy the factored induction hypothesis. -/
theorem factoredExpressionIH_ifTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expr : AstHOL.Exp) (covered : FactoredIfExpression expr) :
    FactoredExpressionIH (F := F) interp transform expr := by
  induction covered with
  | base expr supported => exact factoredExpressionIH_letTree interp transform expr supported
  | constructor name args _ ih => exact factoredExpressionIH_constructor interp transform name args ih
  | raise_ body _ ih => exact factoredExpressionIH_raise interp transform body ih
  | letAnonymous first body _ _ firstIH bodyIH =>
    exact factoredExpressionIH_let_anonymous interp transform first body firstIH bodyIH
  | if_ cond yes no _ _ _ condIH yesIH noIH =>
    exact factoredExpressionIH_if interp transform cond yes no condIH yesIH noIH
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

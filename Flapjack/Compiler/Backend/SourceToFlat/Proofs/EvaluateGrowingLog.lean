import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateGrowingIf

/-! Short-circuit logical expressions over the preliminary growing
source-to-flat simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Logical expressions compose the growing left and right induction
hypotheses, evaluating the right operand only when the Boolean result requires it. -/
theorem factoredExpressionIH_log {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (op : Lop) (left right : AstHOL.Exp) (leftIH : FactoredExpressionIH (F := F) interp transform left)
    (rightIH : FactoredExpressionIH (F := F) interp transform right) :
    FactoredExpressionIH (F := F) interp transform (.log op left right) := by
  intro genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation safe
  have leftSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [left] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [left] []).1, bad]
  obtain ⟨middleGenv, leftSim, leftPost⟩ := leftIH genv start finish other source flat sourceEnv trace compMap gen
    envInv invariant generation leftSafe
  have leftSimCopy := leftSim
  unfold ExprSim at leftSim
  generalize sourceLeft : EvaluateHOL.evaluate source sourceEnv [left] = sourceResult at leftSim leftPost
  obtain ⟨middleSource, sourceResult⟩ := sourceResult
  generalize flatLeft : FlatSem.evaluate ⟨[]⟩ flat [compileExp trace compMap left] = flatResult at leftSim leftPost
  obtain ⟨middleFlat, flatResult⟩ := flatResult
  obtain ⟨leftRelated, leftStates⟩ := leftSim
  cases leftRelated with
  | abort error =>
    refine ⟨middleGenv, exprSim_log_error middleGenv compMap trace sourceEnv ⟨[]⟩ source flat op left right
      middleSource (.abort error) sourceLeft leftSimCopy, ?_⟩
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [left] []).1, sourceLeft]
    trivial
  | raise valueRel =>
    refine ⟨middleGenv, exprSim_log_error middleGenv compMap trace sourceEnv ⟨[]⟩ source flat op left right
      middleSource (.raise _) sourceLeft leftSimCopy, ?_⟩
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [left] []).1, sourceLeft]
    cases op <;> rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations ⟨[]⟩ flat
      [compileExp trace compMap left] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatLeft] <;> exact leftPost
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨leftValue, sourceEq⟩ := EvaluateProps.evaluateSingFull source middleSource sourceEnv left sourceValues sourceLeft
    subst sourceValues
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        cases selection : SemanticPrimitivesHOL.doLog op leftValue right with
        | none =>
          have bad : EvaluateHOL.evaluate source sourceEnv [.log op left right] =
              (middleSource, .err (.abort .typeError)) := by
            rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [left] []).1, sourceLeft]
            simp only [EvaluateHOL.headValue, Flapjack.holHd]
            rw [selection]
            rfl
          exact False.elim (safe middleSource bad)
        | some selected =>
          obtain ⟨b, valueEq⟩ := SemanticPrimitivesHOL.doLog_success_boolean op leftValue right selected selection
          subst leftValue
          obtain ⟨leftGrowth, middleInvariant, middleGeneration, leftForward⟩ := leftPost
          have flatBoolean := (boolValueRel_iff middleGenv middleInvariant.1 b _).mp valueRel
          subst_vars
          have sourceOuter : EvaluateHOL.evaluate source sourceEnv [.log op left right] =
              if (op = .andalso ∧ b = true) ∨ (op = .orelse ∧ b = false) then
                EvaluateHOL.evaluate middleSource sourceEnv [right]
              else (middleSource, .val [SemanticPrimitivesHOL.boolValue b]) := by
            rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [left] []).1, sourceLeft]
            simp only [EvaluateHOL.headValue, Flapjack.holHd]
            cases op <;> cases b <;> rfl
          have flatOuter : FlatSem.evaluate ⟨[]⟩ flat [compileExp trace compMap (.log op left right)] =
              if (op = .andalso ∧ b = true) ∨ (op = .orelse ∧ b = false) then
                FlatSem.evaluate ⟨[]⟩ middleFlat [compileExp trace compMap right]
              else (middleFlat, .val [FlatSem.boolValue b]) := by
            cases op <;> cases b <;>
              rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations ⟨[]⟩ flat
                [compileExp trace compMap left] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatLeft] <;>
              simp [FlatSem.doIf, FlatSem.boolValue, BackendCommon.boolToTag,
                BackendCommon.trueTag, BackendCommon.falseTag, FlatLang.boolId, FlatLang.mkBool, FlatSem.evaluate]
          by_cases takeRight : (op = .andalso ∧ b = true) ∨ (op = .orelse ∧ b = false)
          · have rightSafe : ∀ last, EvaluateHOL.evaluate middleSource sourceEnv [right] ≠
                (last, .err (.abort .typeError)) := by
              intro last bad
              apply safe last
              rw [sourceOuter, if_pos takeRight]
              exact bad
            have middleEnv := globalEnvInv_growth genv middleGenv leftGrowth compMap (fun _ => False) sourceEnv envInv
            obtain ⟨finalGenv, rightSim, rightPost⟩ := rightIH middleGenv start finish other middleSource middleFlat
              sourceEnv trace compMap gen middleEnv middleInvariant middleGeneration rightSafe
            refine ⟨finalGenv, ?_, ?_⟩
            · unfold ExprSim at rightSim ⊢
              rw [sourceOuter, flatOuter, if_pos takeRight, if_pos takeRight]
              exact rightSim
            · rw [sourceOuter, flatOuter, if_pos takeRight, if_pos takeRight]
              cases result : (EvaluateHOL.evaluate middleSource sourceEnv [right]).2 with
              | err error =>
                cases error with
                | abort error => simp
                | raise value =>
                  rw [result] at rightPost
                  obtain ⟨growth, finalInvariant, finalGeneration, rightForward⟩ := rightPost
                  exact ⟨leftGrowth.trans growth, finalInvariant, finalGeneration,
                    oracForwardRel_trans interp _ _ _ ⟨leftForward, rightForward⟩⟩
              | val values =>
                rw [result] at rightPost
                obtain ⟨growth, finalInvariant, finalGeneration, rightForward⟩ := rightPost
                exact ⟨leftGrowth.trans growth, finalInvariant, finalGeneration,
                  oracForwardRel_trans interp _ _ _ ⟨leftForward, rightForward⟩⟩
          · refine ⟨middleGenv, ?_, ?_⟩
            · unfold ExprSim
              rw [sourceOuter, flatOuter, if_neg takeRight, if_neg takeRight]
              exact ⟨.value (.cons (boolValue_related middleGenv middleInvariant.1 b) .nil), leftStates⟩
            · rw [sourceOuter, flatOuter, if_neg takeRight, if_neg takeRight]
              exact ⟨leftGrowth, middleInvariant, middleGeneration, leftForward⟩

/-- Covered expressions including short-circuit Boolean operators and the
previously covered conditional, constructor, raise and anonymous-let forms. -/
inductive FactoredLogExpression : AstHOL.Exp → Prop where
  | base (expr : AstHOL.Exp) : FactoredIfExpression expr → FactoredLogExpression expr
  | constructor (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp) :
      (∀ expr, expr ∈ args → FactoredLogExpression expr) → FactoredLogExpression (.con name args)
  | raise_ (body : AstHOL.Exp) : FactoredLogExpression body → FactoredLogExpression (.raise body)
  | letAnonymous (first body : AstHOL.Exp) : FactoredLogExpression first → FactoredLogExpression body →
      FactoredLogExpression (.let_ none first body)
  | if_ (cond yes no : AstHOL.Exp) : FactoredLogExpression cond → FactoredLogExpression yes →
      FactoredLogExpression no → FactoredLogExpression (.if_ cond yes no)
  | log (op : Lop) (left right : AstHOL.Exp) : FactoredLogExpression left → FactoredLogExpression right →
      FactoredLogExpression (.log op left right)
  | tannot (expr : AstHOL.Exp) (typ : AstT) : FactoredLogExpression expr → FactoredLogExpression (.tannot expr typ)
  | lannot (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) : FactoredLogExpression expr →
      FactoredLogExpression (.lannot expr loc)

/-- Covered logical expressions satisfy the factored induction hypothesis. -/
theorem factoredExpressionIH_logTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expr : AstHOL.Exp) (covered : FactoredLogExpression expr) :
    FactoredExpressionIH (F := F) interp transform expr := by
  induction covered with
  | base expr supported => exact factoredExpressionIH_ifTree interp transform expr supported
  | constructor name args _ ih => exact factoredExpressionIH_constructor interp transform name args ih
  | raise_ body _ ih => exact factoredExpressionIH_raise interp transform body ih
  | letAnonymous first body _ _ firstIH bodyIH =>
    exact factoredExpressionIH_let_anonymous interp transform first body firstIH bodyIH
  | if_ cond yes no _ _ _ condIH yesIH noIH => exact factoredExpressionIH_if interp transform cond yes no condIH yesIH noIH
  | log op left right _ _ leftIH rightIH => exact factoredExpressionIH_log interp transform op left right leftIH rightIH
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

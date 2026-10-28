import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateBoundTest

/-! Local conditionals over the preliminary source-to-flat relations. These
relations and the resulting proof remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- A growing expression hypothesis for one bound local value, quantified
across related states and values. -/
def BoundLocalIH {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (expr : AstHOL.Exp) : Prop :=
  ∀ (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (value : Value) (flatValue : FlatSem.Value),
    ValueRel genv value flatValue →
    GlobalEnvInv genv compMap (fun _ => False) sourceEnv →
    factoredInvariant interp transform gen genv (start, finish, other) source flat →
    envGenRel gen source.evalState →
    (∀ last, EvaluateHOL.evaluate source { sourceEnv with v := nsBind name value sourceEnv.v } [expr] ≠
      (last, .err (.abort .typeError))) →
    LocalExpressionStep interp transform genv start finish other source flat
      { sourceEnv with v := nsBind name value sourceEnv.v } ⟨[(name, flatValue)]⟩ trace
      { compMap with v := nsBind name (.localName .none name) compMap.v } gen expr

/-- Conditional local expressions compose the condition and selected branch
while preserving growth, state invariants, and early errors. -/
theorem boundLocalIH_if {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (cond yes no : AstHOL.Exp)
    (condIH : BoundLocalIH (F := F) interp transform name cond)
    (yesIH : BoundLocalIH (F := F) interp transform name yes)
    (noIH : BoundLocalIH (F := F) interp transform name no) :
    BoundLocalIH (F := F) interp transform name (.if_ cond yes no) := by
  intro genv start finish other source flat baseEnv trace baseMap gen value flatValue related envInv invariant generation safe
  let sourceEnv := { baseEnv with v := nsBind name value baseEnv.v }
  let compMap := { baseMap with v := nsBind name (.localName .none name) baseMap.v }
  let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
  have condSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [cond] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [cond] []).1, bad]
  obtain ⟨middleGenv, condSim, condPost⟩ := condIH genv start finish other source flat baseEnv trace baseMap gen
    value flatValue related envInv invariant generation condSafe
  have condSimCopy := condSim
  unfold ExprSim at condSim
  generalize sourceCond : EvaluateHOL.evaluate source sourceEnv [cond] = sourceResult at condSim condPost
  obtain ⟨middleSource, sourceResult⟩ := sourceResult
  generalize flatCond : FlatSem.evaluate flatEnv flat [compileExp trace compMap cond] = flatResult at condSim condPost
  obtain ⟨middleFlat, flatResult⟩ := flatResult
  obtain ⟨condRelated, condStates⟩ := condSim
  cases condRelated with
  | abort error =>
    refine ⟨middleGenv, exprSim_if_error middleGenv compMap trace sourceEnv flatEnv source flat cond yes no
      middleSource (.abort error) sourceCond condSimCopy, ?_⟩
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [cond] []).1, sourceCond]
    trivial
  | raise valueRel =>
    refine ⟨middleGenv, exprSim_if_error middleGenv compMap trace sourceEnv flatEnv source flat cond yes no
      middleSource (.raise _) sourceCond condSimCopy, ?_⟩
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [cond] []).1, sourceCond]
    rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
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
          have middleRelated := valueRel_growth genv middleGenv condGrowth value flatValue related
          have middleEnv := globalEnvInv_growth genv middleGenv condGrowth baseMap (fun _ => False) baseEnv envInv
          have sourceOuter : EvaluateHOL.evaluate source sourceEnv [.if_ cond yes no] =
              EvaluateHOL.evaluate middleSource sourceEnv [if b then yes else no] := by
            rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [cond] []).1, sourceCond]
            simp only [EvaluateHOL.headValue, Flapjack.holHd]
            rw [SemanticPrimitivesHOL.doIf_boolValue]
          have flatOuter : FlatSem.evaluate flatEnv flat [compileExp trace compMap (.if_ cond yes no)] =
              FlatSem.evaluate flatEnv middleFlat [compileExp trace compMap (if b then yes else no)] := by
            rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
              [compileExp trace compMap cond] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatCond]
            cases b <;> simp [FlatSem.doIf, FlatSem.boolValue, BackendCommon.boolToTag,
              BackendCommon.trueTag, BackendCommon.falseTag, FlatLang.boolId]
          have branchSafe : ∀ last, EvaluateHOL.evaluate middleSource sourceEnv [if b then yes else no] ≠
              (last, .err (.abort .typeError)) := by
            intro last bad
            apply safe last
            exact sourceOuter.trans bad
          have branchIH : BoundLocalIH (F := F) interp transform name (if b then yes else no) := by
            cases b <;> simp_all
          obtain ⟨finalGenv, branchSim, branchPost⟩ := branchIH middleGenv start finish other middleSource middleFlat
            baseEnv trace baseMap gen value flatValue middleRelated middleEnv middleInvariant middleGeneration branchSafe
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


/-- Short-circuit local expressions compose their left and, when selected,
right induction hypotheses while preserving growth and errors. -/
theorem boundLocalIH_log {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (op : Lop) (left right : AstHOL.Exp)
    (leftIH : BoundLocalIH (F := F) interp transform name left)
    (rightIH : BoundLocalIH (F := F) interp transform name right) :
    BoundLocalIH (F := F) interp transform name (.log op left right) := by
  intro genv start finish other source flat baseEnv trace baseMap gen value flatValue related envInv invariant generation safe
  let sourceEnv := { baseEnv with v := nsBind name value baseEnv.v }
  let compMap := { baseMap with v := nsBind name (.localName .none name) baseMap.v }
  let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
  have leftSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [left] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [left] []).1, bad]
  obtain ⟨middleGenv, leftSim, leftPost⟩ := leftIH genv start finish other source flat baseEnv trace baseMap gen
    value flatValue related envInv invariant generation leftSafe
  have leftSimCopy := leftSim
  unfold ExprSim at leftSim
  generalize sourceLeft : EvaluateHOL.evaluate source sourceEnv [left] = sourceResult at leftSim leftPost
  obtain ⟨middleSource, sourceResult⟩ := sourceResult
  generalize flatLeft : FlatSem.evaluate flatEnv flat [compileExp trace compMap left] = flatResult at leftSim leftPost
  obtain ⟨middleFlat, flatResult⟩ := flatResult
  obtain ⟨leftRelated, leftStates⟩ := leftSim
  cases leftRelated with
  | abort error =>
    refine ⟨middleGenv, exprSim_log_error middleGenv compMap trace sourceEnv flatEnv source flat op left right
      middleSource (.abort error) sourceLeft leftSimCopy, ?_⟩
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [left] []).1, sourceLeft]
    trivial
  | raise valueRel =>
    refine ⟨middleGenv, exprSim_log_error middleGenv compMap trace sourceEnv flatEnv source flat op left right
      middleSource (.raise _) sourceLeft leftSimCopy, ?_⟩
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [left] []).1, sourceLeft]
    cases op <;> rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
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
          have flatOuter : FlatSem.evaluate flatEnv flat [compileExp trace compMap (.log op left right)] =
              if (op = .andalso ∧ b = true) ∨ (op = .orelse ∧ b = false) then
                FlatSem.evaluate flatEnv middleFlat [compileExp trace compMap right]
              else (middleFlat, .val [FlatSem.boolValue b]) := by
            cases op <;> cases b <;>
              rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
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
            have middleRelated := valueRel_growth genv middleGenv leftGrowth value flatValue related
            have middleEnv := globalEnvInv_growth genv middleGenv leftGrowth baseMap (fun _ => False) baseEnv envInv
            obtain ⟨finalGenv, rightSim, rightPost⟩ := rightIH middleGenv start finish other middleSource middleFlat
              baseEnv trace baseMap gen value flatValue middleRelated middleEnv middleInvariant middleGeneration rightSafe
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

/-- Local expression coverage combines pure expressions and primitive
operations with recursively nested conditionals. -/
inductive BoundLocalExpression (name : VarN) : AstHOL.Exp → Prop where
  | pure (expr : AstHOL.Exp) : BoundPureExpression name expr → BoundLocalExpression name expr
  | test (test : Test) (typ : PrimType) (left right : AstHOL.Exp) :
      BoundPureExpression name left → BoundPureExpression name right →
      BoundLocalExpression name (.app (.test test typ) [left, right])
  | equality (left right : AstHOL.Exp) : BoundPureExpression name left → BoundPureExpression name right →
      BoundLocalExpression name (.app .equality [left, right])
  | integerArith (action : Arith) (left right : AstHOL.Exp) :
      BoundPureExpression name left → BoundPureExpression name right →
      BoundLocalExpression name (.app (.arith action .intT) [left, right])
  | log (op : Lop) (left right : AstHOL.Exp) : BoundLocalExpression name left → BoundLocalExpression name right →
      BoundLocalExpression name (.log op left right)
  | if_ (cond yes no : AstHOL.Exp) : BoundLocalExpression name cond → BoundLocalExpression name yes →
      BoundLocalExpression name no → BoundLocalExpression name (.if_ cond yes no)

/-- Covered local expressions satisfy the preliminary growing induction
hypothesis. The underlying relations remain pending HOL review. -/
theorem boundLocalIH_covered {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (expr : AstHOL.Exp) (covered : BoundLocalExpression name expr) :
    BoundLocalIH (F := F) interp transform name expr := by
  induction covered with
  | pure expr pure =>
    intro genv start finish other source flat env trace map gen value flatValue related _ invariant generation _
    exact localExpressionStep_boundPure interp transform genv start finish other source flat env trace map gen
      name value flatValue expr pure related invariant generation
  | test test typ left right lc rc =>
    intro genv start finish other source flat env trace map gen value flatValue related _ invariant generation safe
    exact localExpressionStep_boundTest interp transform genv start finish other source flat env trace map gen
      name value flatValue test typ left right lc rc related invariant generation safe
  | equality left right lc rc =>
    intro genv start finish other source flat env trace map gen value flatValue related _ invariant generation safe
    exact localExpressionStep_boundEquality interp transform genv start finish other source flat env trace map gen
      name value flatValue left right lc rc related invariant generation safe
  | integerArith action left right lc rc =>
    intro genv start finish other source flat env trace map gen value flatValue related _ invariant generation safe
    exact localExpressionStep_boundIntegerArith interp transform genv start finish other source flat env trace map gen
      name value flatValue action left right lc rc related invariant generation safe
  | log op left right _ _ leftIH rightIH =>
    exact boundLocalIH_log interp transform name op left right leftIH rightIH
  | if_ cond yes no _ _ _ condIH yesIH noIH =>
    exact boundLocalIH_if interp transform name cond yes no condIH yesIH noIH

/-- A named binding whose body has the above local coverage satisfies the
preliminary declaration-expression induction hypothesis. -/
theorem factoredExpressionIH_let_named_local {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (first body : AstHOL.Exp) (covered : BoundLocalExpression name body)
    (firstIH : FactoredExpressionIH (F := F) interp transform first) :
    FactoredExpressionIH (F := F) interp transform (.let_ (some name) first body) := by
  apply factoredExpressionIH_let_named_of_local interp transform name first body firstIH
  exact boundLocalIH_covered interp transform name body covered

end Flapjack.Compiler.Backend.SourceToFlat

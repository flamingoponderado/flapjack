import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalEnvironment

/-! Control-flow composition for arbitrary related local environments.
These preliminary relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Compose localEnvIH_if in any related local environment. -/
theorem localEnvIH_if {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (cond yes no : AstHOL.Exp)
    (condIH : LocalEnvIH (F := F) interp transform cond)
    (yesIH : LocalEnvIH (F := F) interp transform yes)
    (noIH : LocalEnvIH (F := F) interp transform no) :
    LocalEnvIH (F := F) interp transform (.if_ cond yes no) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have condSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [cond] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [cond] []).1, bad]
  obtain ⟨middleGenv, condSim, condPost⟩ := condIH genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen
    localRel envInv tracesLen invariant generation condSafe
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
          have middleLocal := envRel_growth genv middleGenv condGrowth sourceLocal flatEnv.v localRel
          have middleEnv := globalEnvInv_growth genv middleGenv condGrowth baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv envInv
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
          have branchIH : LocalEnvIH (F := F) interp transform (if b then yes else no) := by
            cases b <;> simp_all
          obtain ⟨finalGenv, branchSim, branchPost⟩ := branchIH middleGenv start finish other middleSource middleFlat
            baseEnv sourceLocal flatEnv traces trace baseMap gen middleLocal middleEnv tracesLen middleInvariant middleGeneration branchSafe
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



/-- Compose localEnvIH_log in any related local environment. -/
theorem localEnvIH_log {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (op : Lop) (left right : AstHOL.Exp)
    (leftIH : LocalEnvIH (F := F) interp transform left)
    (rightIH : LocalEnvIH (F := F) interp transform right) :
    LocalEnvIH (F := F) interp transform (.log op left right) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have leftSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [left] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [left] []).1, bad]
  obtain ⟨middleGenv, leftSim, leftPost⟩ := leftIH genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen
    localRel envInv tracesLen invariant generation leftSafe
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
            have middleLocal := envRel_growth genv middleGenv leftGrowth sourceLocal flatEnv.v localRel
            have middleEnv := globalEnvInv_growth genv middleGenv leftGrowth baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv envInv
            obtain ⟨finalGenv, rightSim, rightPost⟩ := rightIH middleGenv start finish other middleSource middleFlat
              baseEnv sourceLocal flatEnv traces trace baseMap gen middleLocal middleEnv tracesLen middleInvariant middleGeneration rightSafe
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


/-- Compose localEnvIH_let_anonymous in any related local environment. -/
theorem localEnvIH_let_anonymous {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (first body : AstHOL.Exp)
    (firstIH : LocalEnvIH (F := F) interp transform first)
    (bodyIH : LocalEnvIH (F := F) interp transform body) :
    LocalEnvIH (F := F) interp transform (.let_ none first body) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have firstSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [first] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, bad]
  obtain ⟨middleGenv, firstSim, firstPost⟩ := firstIH genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen
    localRel envInv tracesLen invariant generation firstSafe
  unfold ExprSim at firstSim
  generalize sourceFirst : EvaluateHOL.evaluate source sourceEnv [first] = sourceResult at firstSim firstPost
  obtain ⟨middleSource, sourceResult⟩ := sourceResult
  generalize flatFirst : FlatSem.evaluate flatEnv flat [compileExp trace compMap first] = flatResult at firstSim firstPost
  obtain ⟨middleFlat, flatResult⟩ := flatResult
  obtain ⟨firstRelated, firstStates⟩ := firstSim
  cases firstRelated with
  | abort error =>
    refine ⟨middleGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatFirst]
      exact ⟨.abort error, firstStates⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
      trivial
  | raise valueRel =>
    refine ⟨middleGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatFirst]
      exact ⟨.raise valueRel, firstStates⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatFirst]
      exact firstPost
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨sourceValue, sourceEq⟩ := EvaluateProps.evaluateSingFull source middleSource sourceEnv first sourceValues sourceFirst
    subst sourceValues
    cases valuesRel with
    | cons headValueRel tail =>
      cases tail with
      | nil =>
        obtain ⟨firstGrowth, middleInvariant, middleGeneration, firstForward⟩ := firstPost
        have middleEnv := globalEnvInv_growth genv middleGenv firstGrowth baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv envInv
        have middleLocal := envRel_growth genv middleGenv firstGrowth sourceLocal flatEnv.v localRel
        have bodySafe : ∀ last, EvaluateHOL.evaluate middleSource sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
          intro last bad
          apply safe last
          rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
          simpa [nsOptBind] using bad
        obtain ⟨finalGenv, bodySim, bodyPost⟩ := bodyIH middleGenv start finish other middleSource middleFlat baseEnv sourceLocal flatEnv traces
          trace baseMap gen middleLocal middleEnv tracesLen middleInvariant middleGeneration bodySafe
        have sourceOuter : EvaluateHOL.evaluate source sourceEnv [.let_ none first body] =
            EvaluateHOL.evaluate middleSource sourceEnv [body] := by
          rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
          simp [nsOptBind]
        have flatOuter : FlatSem.evaluate flatEnv flat [compileExp trace compMap (.let_ none first body)] =
            FlatSem.evaluate flatEnv middleFlat [compileExp trace compMap body] := by
          rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
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



/-- Compose localEnvIH_raise in any related local environment. -/
theorem localEnvIH_raise {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (body : AstHOL.Exp) (bodyIH : LocalEnvIH (F := F) interp transform body) : LocalEnvIH (F := F) interp transform (.raise body) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.raise body] = _
    simp [EvaluateHOL.evaluate, bad]
  obtain ⟨nextGenv, bodySim, post⟩ := bodyIH genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen
    localRel envInv tracesLen invariant generation bodySafe
  change LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen
    (.raise body)
  refine ⟨nextGenv, exprSim_raise nextGenv compMap trace sourceEnv flatEnv source flat body bodySim, ?_⟩
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [body] = sourceResult at post ⊢
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap body] = flatResult at post ⊢
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  cases sourceResult with
  | err error =>
    cases error with
    | abort error => simp [EvaluateHOL.evaluate, sourceRun]
    | raise value =>
      cases flatResult <;> simpa [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, sourceRun, flatRun] using post
  | val values =>
    cases flatResult <;> simpa [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, sourceRun, flatRun] using post


/-- Compose localEnvIH_tannot in any related local environment. -/
theorem localEnvIH_tannot {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expr : AstHOL.Exp) (typ : AstT) (ih : LocalEnvIH (F := F) interp transform expr) : LocalEnvIH (F := F) interp transform (.tannot expr typ) := by
  intro genv start finish other source flat env sourceLocal flatEnv traces trace map gen localRel envInv tracesLen invariant generation safe
  have exprSafe : ∀ last, EvaluateHOL.evaluate source { env with v := nsAppend sourceLocal env.v } [expr] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    simpa [EvaluateHOL.evaluate] using bad
  obtain ⟨next, sim, post⟩ := ih genv start finish other source flat env sourceLocal flatEnv traces trace map gen localRel envInv tracesLen
    invariant generation exprSafe
  refine ⟨next, exprSim_tannot next _ trace _ _ source flat expr typ sim, ?_⟩
  simpa only [EvaluateHOL.evaluate, compileExp] using post


/-- Compose localEnvIH_lannot in any related local environment. -/
theorem localEnvIH_lannot {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) (ih : LocalEnvIH (F := F) interp transform expr) : LocalEnvIH (F := F) interp transform (.lannot expr loc) := by
  intro genv start finish other source flat env sourceLocal flatEnv traces trace map gen localRel envInv tracesLen invariant generation safe
  have exprSafe : ∀ last, EvaluateHOL.evaluate source { env with v := nsAppend sourceLocal env.v } [expr] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    cases loc
    simpa [EvaluateHOL.evaluate] using bad
  obtain ⟨next, sim, post⟩ := ih genv start finish other source flat env sourceLocal flatEnv traces trace map gen localRel envInv tracesLen
    invariant generation exprSafe
  refine ⟨next, exprSim_lannot next _ trace _ _ source flat expr loc sim, ?_⟩
  cases loc
  simpa only [EvaluateHOL.evaluate, compileExp] using post


/-- Covered expressions can combine nested bindings with conditionals,
short-circuit logic, sequencing, raising, and annotations. -/
inductive LocalEnvControlExpression : AstHOL.Exp → Prop where
  | base (expr : AstHOL.Exp) : LocalEnvExpression expr → LocalEnvControlExpression expr
  | letNamed (name : VarN) (first body : AstHOL.Exp) : LocalEnvControlExpression first →
      LocalEnvControlExpression body → LocalEnvControlExpression (.let_ (some name) first body)
  | letAnonymous (first body : AstHOL.Exp) : LocalEnvControlExpression first → LocalEnvControlExpression body →
      LocalEnvControlExpression (.let_ none first body)
  | if_ (cond yes no : AstHOL.Exp) : LocalEnvControlExpression cond → LocalEnvControlExpression yes →
      LocalEnvControlExpression no → LocalEnvControlExpression (.if_ cond yes no)
  | log (op : Lop) (left right : AstHOL.Exp) : LocalEnvControlExpression left → LocalEnvControlExpression right →
      LocalEnvControlExpression (.log op left right)
  | raise_ (body : AstHOL.Exp) : LocalEnvControlExpression body → LocalEnvControlExpression (.raise body)
  | tannot (expr : AstHOL.Exp) (typ : AstT) : LocalEnvControlExpression expr → LocalEnvControlExpression (.tannot expr typ)
  | lannot (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) : LocalEnvControlExpression expr →
      LocalEnvControlExpression (.lannot expr loc)

/-- Covered expressions satisfy the preliminary arbitrary-local hypothesis;
the relations remain pending HOL correspondence review. -/
theorem localEnvIH_controlTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expr : AstHOL.Exp) (covered : LocalEnvControlExpression expr) : LocalEnvIH (F := F) interp transform expr := by
  induction covered with
  | base expr covered => exact localEnvIH_covered interp transform expr covered
  | letNamed name first body _ _ firstIH bodyIH => exact localEnvIH_let_named interp transform name first body firstIH bodyIH
  | letAnonymous first body _ _ firstIH bodyIH => exact localEnvIH_let_anonymous interp transform first body firstIH bodyIH
  | if_ cond yes no _ _ _ condIH yesIH noIH => exact localEnvIH_if interp transform cond yes no condIH yesIH noIH
  | log op left right _ _ leftIH rightIH => exact localEnvIH_log interp transform op left right leftIH rightIH
  | raise_ body _ ih => exact localEnvIH_raise interp transform body ih
  | tannot expr typ _ ih => exact localEnvIH_tannot interp transform expr typ ih
  | lannot expr loc _ ih => exact localEnvIH_lannot interp transform expr loc ih

end Flapjack.Compiler.Backend.SourceToFlat

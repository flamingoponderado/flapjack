import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBounded

/-! Clock-bounded local control-flow composition. These factored relations
remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Named local bindings extend the related environments and compose the
initializer and body simulations, including shadowing and early errors. -/
theorem localEnvBounded_let_named {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (name : VarN) (first body : AstHOL.Exp)
    (firstIH : LocalEnvBoundedIH (F := F) interp transform limit first)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.let_ (some name) first body) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have firstSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [first] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, bad]
  obtain ⟨middleGenv, firstSim, firstPost⟩ := firstIH genv start finish other source flat baseEnv sourceLocal flatEnv traces
    (name :: trace) baseMap gen clockBound localRel envInv tracesLen invariant generation firstSafe
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
          (.none :: traces) trace baseMap gen
          (Nat.le_trans (EvaluateHOL.evaluateClockFull source middleSource sourceEnv [first] _ sourceFirst) clockBound) extendedRel extendedInv (by simpa using tracesLen)
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


/-- Compose localEnvBounded_if in any related local environment. -/
theorem localEnvBounded_if {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (cond yes no : AstHOL.Exp)
    (condIH : LocalEnvBoundedIH (F := F) interp transform limit cond)
    (yesIH : LocalEnvBoundedIH (F := F) interp transform limit yes)
    (noIH : LocalEnvBoundedIH (F := F) interp transform limit no) :
    LocalEnvBoundedIH (F := F) interp transform limit (.if_ cond yes no) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have condSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [cond] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [cond] []).1, bad]
  obtain ⟨middleGenv, condSim, condPost⟩ := condIH genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen
    clockBound localRel envInv tracesLen invariant generation condSafe
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
          have branchIH : LocalEnvBoundedIH (F := F) interp transform limit (if b then yes else no) := by
            cases b <;> simp_all
          obtain ⟨finalGenv, branchSim, branchPost⟩ := branchIH middleGenv start finish other middleSource middleFlat
            baseEnv sourceLocal flatEnv traces trace baseMap gen
            (Nat.le_trans (EvaluateHOL.evaluateClockFull source middleSource sourceEnv [cond] _ sourceCond) clockBound)
            middleLocal middleEnv tracesLen middleInvariant middleGeneration branchSafe
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




/-- Compose localEnvBounded_log in any related local environment. -/
theorem localEnvBounded_log {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (op : Lop) (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.log op left right) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have leftSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [left] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [left] []).1, bad]
  obtain ⟨middleGenv, leftSim, leftPost⟩ := leftIH genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen
    clockBound localRel envInv tracesLen invariant generation leftSafe
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
              baseEnv sourceLocal flatEnv traces trace baseMap gen
              (Nat.le_trans (EvaluateHOL.evaluateClockFull source middleSource sourceEnv [left] _ sourceLeft) clockBound)
              middleLocal middleEnv tracesLen middleInvariant middleGeneration rightSafe
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


/-- Compose localEnvBounded_let_anonymous in any related local environment. -/
theorem localEnvBounded_let_anonymous {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (first body : AstHOL.Exp)
    (firstIH : LocalEnvBoundedIH (F := F) interp transform limit first)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.let_ none first body) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have firstSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [first] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, bad]
  obtain ⟨middleGenv, firstSim, firstPost⟩ := firstIH genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen
    clockBound localRel envInv tracesLen invariant generation firstSafe
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
          trace baseMap gen
          (Nat.le_trans (EvaluateHOL.evaluateClockFull source middleSource sourceEnv [first] _ sourceFirst) clockBound)
          middleLocal middleEnv tracesLen middleInvariant middleGeneration bodySafe
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



/-- Compose localEnvBounded_raise in any related local environment. -/
theorem localEnvBounded_raise {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (body : AstHOL.Exp) (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) : LocalEnvBoundedIH (F := F) interp transform limit (.raise body) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.raise body] = _
    simp [EvaluateHOL.evaluate, bad]
  obtain ⟨nextGenv, bodySim, post⟩ := bodyIH genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen
    clockBound localRel envInv tracesLen invariant generation bodySafe
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


/-- Compose localEnvBounded_tannot in any related local environment. -/
theorem localEnvBounded_tannot {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (expr : AstHOL.Exp) (typ : AstT) (ih : LocalEnvBoundedIH (F := F) interp transform limit expr) : LocalEnvBoundedIH (F := F) interp transform limit (.tannot expr typ) := by
  intro genv start finish other source flat env sourceLocal flatEnv traces trace map gen clockBound localRel envInv tracesLen invariant generation safe
  have exprSafe : ∀ last, EvaluateHOL.evaluate source { env with v := nsAppend sourceLocal env.v } [expr] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    simpa [EvaluateHOL.evaluate] using bad
  obtain ⟨next, sim, post⟩ := ih genv start finish other source flat env sourceLocal flatEnv traces trace map gen clockBound localRel envInv tracesLen
    invariant generation exprSafe
  refine ⟨next, exprSim_tannot next _ trace _ _ source flat expr typ sim, ?_⟩
  simpa only [EvaluateHOL.evaluate, compileExp] using post


/-- Compose localEnvBounded_lannot in any related local environment. -/
theorem localEnvBounded_lannot {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) (ih : LocalEnvBoundedIH (F := F) interp transform limit expr) : LocalEnvBoundedIH (F := F) interp transform limit (.lannot expr loc) := by
  intro genv start finish other source flat env sourceLocal flatEnv traces trace map gen clockBound localRel envInv tracesLen invariant generation safe
  have exprSafe : ∀ last, EvaluateHOL.evaluate source { env with v := nsAppend sourceLocal env.v } [expr] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    cases loc
    simpa [EvaluateHOL.evaluate] using bad
  obtain ⟨next, sim, post⟩ := ih genv start finish other source flat env sourceLocal flatEnv traces trace map gen clockBound localRel envInv tracesLen
    invariant generation exprSafe
  refine ⟨next, exprSim_lannot next _ trace _ _ source flat expr loc sim, ?_⟩
  cases loc
  simpa only [EvaluateHOL.evaluate, compileExp] using post



/-- Local mutually recursive bindings preserve the arbitrary-environment
simulation when the body does. -/
theorem localEnvBounded_letrec {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (funs : List (VarN × VarN × AstHOL.Exp)) (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.letrec funs body) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
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
    { flatEnv with v := flatLocal' } newTraces trace baseMap gen clockBound extendedRel extendedInv
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


end Flapjack.Compiler.Backend.SourceToFlat

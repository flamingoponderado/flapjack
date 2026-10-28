import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateBoundConstructor

/-! Local sequencing and exception propagation over preliminary factored
relations, pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Anonymous local sequencing composes the growing initializer and body,
propagating early errors. -/
theorem boundLocalIH_let_anonymous {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (first body : AstHOL.Exp)
    (firstIH : BoundLocalIH (F := F) interp transform name first)
    (bodyIH : BoundLocalIH (F := F) interp transform name body) :
    BoundLocalIH (F := F) interp transform name (.let_ none first body) := by
  intro genv start finish other source flat baseEnv trace baseMap gen value flatValue related envInv invariant generation safe
  let sourceEnv := { baseEnv with v := nsBind name value baseEnv.v }
  let compMap := { baseMap with v := nsBind name (.localName .none name) baseMap.v }
  let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
  have firstSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [first] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, bad]
  obtain ⟨middleGenv, firstSim, firstPost⟩ := firstIH genv start finish other source flat baseEnv trace baseMap gen
    value flatValue related envInv invariant generation firstSafe
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
        have middleEnv := globalEnvInv_growth genv middleGenv firstGrowth baseMap (fun _ => False) baseEnv envInv
        have middleRelated := valueRel_growth genv middleGenv firstGrowth value flatValue related
        have bodySafe : ∀ last, EvaluateHOL.evaluate middleSource sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
          intro last bad
          apply safe last
          rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv [first] []).1, sourceFirst]
          simpa [nsOptBind] using bad
        obtain ⟨finalGenv, bodySim, bodyPost⟩ := bodyIH middleGenv start finish other middleSource middleFlat baseEnv
          trace baseMap gen value flatValue middleRelated middleEnv middleInvariant middleGeneration bodySafe
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


/-- Raising a locally simulated expression preserves its abort-sensitive
state, oracle, and environment-growth postconditions. -/
theorem boundLocalIH_raise {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (body : AstHOL.Exp) (bodyIH : BoundLocalIH (F := F) interp transform name body) :
    BoundLocalIH (F := F) interp transform name (.raise body) := by
  intro genv start finish other source flat baseEnv trace baseMap gen value flatValue related envInv invariant generation safe
  let sourceEnv := { baseEnv with v := nsBind name value baseEnv.v }
  let compMap := { baseMap with v := nsBind name (.localName .none name) baseMap.v }
  let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.raise body] = _
    simp [EvaluateHOL.evaluate, bad]
  obtain ⟨nextGenv, bodySim, post⟩ := bodyIH genv start finish other source flat baseEnv trace baseMap gen
    value flatValue related envInv invariant generation bodySafe
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

/-- A type annotation preserves a local growing induction hypothesis. -/
theorem boundLocalIH_tannot {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (expr : AstHOL.Exp) (typ : AstT) (ih : BoundLocalIH (F := F) interp transform name expr) :
    BoundLocalIH (F := F) interp transform name (.tannot expr typ) := by
  intro genv start finish other source flat env trace map gen value flatValue related envInv invariant generation safe
  have exprSafe : ∀ last, EvaluateHOL.evaluate source { env with v := nsBind name value env.v } [expr] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    simpa [EvaluateHOL.evaluate] using bad
  obtain ⟨next, sim, post⟩ := ih genv start finish other source flat env trace map gen value flatValue related envInv
    invariant generation exprSafe
  refine ⟨next, exprSim_tannot next _ trace _ _ source flat expr typ sim, ?_⟩
  simpa only [EvaluateHOL.evaluate, compileExp] using post

/-- A source-location annotation preserves a local growing induction hypothesis. -/
theorem boundLocalIH_lannot {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs)
    (ih : BoundLocalIH (F := F) interp transform name expr) :
    BoundLocalIH (F := F) interp transform name (.lannot expr loc) := by
  intro genv start finish other source flat env trace map gen value flatValue related envInv invariant generation safe
  have exprSafe : ∀ last, EvaluateHOL.evaluate source { env with v := nsBind name value env.v } [expr] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    cases loc
    simpa [EvaluateHOL.evaluate] using bad
  obtain ⟨next, sim, post⟩ := ih genv start finish other source flat env trace map gen value flatValue related envInv
    invariant generation exprSafe
  refine ⟨next, exprSim_lannot next _ trace _ _ source flat expr loc sim, ?_⟩
  cases loc
  simpa only [EvaluateHOL.evaluate, compileExp] using post

/-- Binding a local name leaves all other short names and all qualified
lookups unchanged. -/
theorem nsLookup_bind_other {α : Type} (env : Namespace ModN VarN α) (name : VarN) (value : α)
    (id : Ident ModN VarN) (other : id ≠ .short name) :
    nsLookup (nsBind name value env) id = nsLookup env id := by
  cases env with
  | bind values modules =>
    cases id with
    | short key =>
      have different : key ≠ name := by
        intro equal
        subst key
        exact other rfl
      have neq : (key == name) = false := by
        change decide (key = name) = false
        simp [different]
      simp [nsBind, nsLookup, List.lookup_cons, neq]
    | long moduleName inner => rfl

/-- Local variable lookup chooses the new binding when names coincide and
otherwise uses the related surrounding global binding. -/
theorem boundLocalIH_variable {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (id : Ident ModN VarN) :
    BoundLocalIH (F := F) interp transform name (.var id) := by
  intro genv start finish other source flat baseEnv trace baseMap gen value flatValue related envInv invariant generation safe
  by_cases same : id = .short name
  · subst id
    exact localExpressionStep_boundVariable interp transform genv start finish other source flat baseEnv trace
      baseMap gen name value flatValue related invariant generation
  · let sourceEnv := { baseEnv with v := nsBind name value baseEnv.v }
    let compMap := { baseMap with v := nsBind name (.localName .none name) baseMap.v }
    let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
    change LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen
      (.var id)
    have lookupEq : nsLookup sourceEnv.v id = nsLookup baseEnv.v id :=
      nsLookup_bind_other baseEnv.v name value id same
    cases lookup : nsLookup baseEnv.v id with
    | none =>
      have bad : EvaluateHOL.evaluate source sourceEnv [.var id] = (source, .err (.abort .typeError)) := by
        simp [EvaluateHOL.evaluate, lookupEq, lookup, EvaluateHOL.typeError]
      exact False.elim (safe source bad)
    | some sourceValue =>
      have oldRel : GlobalLookupRel genv baseMap id sourceValue := by
        cases envInv with
        | intro _ _ _ values _ => exact values id sourceValue (by simp) lookup
      have newRel : GlobalLookupRel genv compMap id sourceValue := by
        cases oldRel with
        | intro _ _ _ index stored tr compiled bound slot valueRel =>
          apply GlobalLookupRel.intro genv compMap id sourceValue index stored tr _ bound slot valueRel
          simpa [compMap, nsLookup_bind_other baseMap.v name (.localName .none name) id same] using compiled
      have sourceLookup : nsLookup sourceEnv.v id = some sourceValue := by rw [lookupEq, lookup]
      obtain ⟨flatValue', sourceRun, flatRun, valueRel, states⟩ :=
        evaluate_global_unbounded genv compMap sourceEnv flatEnv source flat invariant.2.2.1
          invariant.2.2.2.2.2.2.1.symm trace id sourceValue sourceLookup newRel
      refine ⟨genv, ?_, ?_⟩
      · unfold ExprSim
        rw [sourceRun, flatRun]
        exact ⟨.value (.cons valueRel .nil), states⟩
      · rw [sourceRun, flatRun]
        exact ⟨GlobalGrowth.refl genv, invariant, generation, oracForwardRel_refl interp source.evalState⟩

/-- Function creation captures the related local binding and preserves both
states. Its surrounding global invariant is restricted by local shadowing. -/
theorem boundLocalIH_function {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name arg : VarN) (body : AstHOL.Exp) :
    BoundLocalIH (F := F) interp transform name (.fn arg body) := by
  intro genv start finish other source flat baseEnv trace baseMap gen value flatValue related envInv invariant generation _
  let localEnv : Namespace ModN VarN Value := nsBind name value nsEmpty
  let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
  have localRel : EnvRel genv localEnv flatEnv.v :=
    .bind genv name value nsEmpty [] flatValue (.empty genv) related
  have shadowInv : GlobalEnvInv genv baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv := by
    cases envInv with
    | intro _ _ _ values constructors =>
      apply GlobalEnvInv.intro
      · intro id v _ lookup
        exact values id v (by simp) lookup
      · exact constructors
  have sim := exprSim_function genv baseMap baseEnv localEnv flatEnv localRel shadowInv
    [.none] rfl source flat invariant.2.2.1 trace arg body
  have adjusted : ExprSim genv { baseMap with v := nsBind name (.localName .none name) baseMap.v } trace
      { baseEnv with v := nsBind name value baseEnv.v } flatEnv source flat (.fn arg body) := by
    cases envEq : baseEnv.v with
    | bind values modules =>
      cases mapEq : baseMap.v with
      | bind names namespaces =>
        simpa [localEnv, flatEnv, envEq, mapEq, nsBind, nsEmpty, nsAppend, bindLocals, nsBindList] using sim
  refine ⟨genv, adjusted, ?_⟩
  simpa only [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate] using
    And.intro (GlobalGrowth.refl genv) (And.intro invariant
      (And.intro generation (oracForwardRel_refl interp source.evalState)))

/-- Local expressions with sequencing, exceptions, annotations, and the previously covered forms. -/
inductive BoundControlExpression (name : VarN) : AstHOL.Exp → Prop where
  | base (expr : AstHOL.Exp) : BoundConstructorExpression name expr → BoundControlExpression name expr
  | variable_ (id : Ident ModN VarN) : BoundControlExpression name (.var id)
  | function_ (arg : VarN) (body : AstHOL.Exp) : BoundControlExpression name (.fn arg body)
  | raise_ (body : AstHOL.Exp) : BoundControlExpression name body → BoundControlExpression name (.raise body)
  | letAnonymous (first body : AstHOL.Exp) : BoundControlExpression name first → BoundControlExpression name body →
      BoundControlExpression name (.let_ none first body)
  | tannot (expr : AstHOL.Exp) (typ : AstT) : BoundControlExpression name expr → BoundControlExpression name (.tannot expr typ)
  | lannot (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) : BoundControlExpression name expr →
      BoundControlExpression name (.lannot expr loc)
  | constructor (id : Ident ModN ConN) (args : List AstHOL.Exp) :
      (∀ expr, expr ∈ args → BoundControlExpression name expr) →
      BoundControlExpression name (.con (some id) args)
  | tuple (args : List AstHOL.Exp) : (∀ expr, expr ∈ args → BoundControlExpression name expr) →
      BoundControlExpression name (.con none args)
  | test (test : Test) (typ : PrimType) (left right : AstHOL.Exp) :
      BoundControlExpression name left → BoundControlExpression name right →
      BoundControlExpression name (.app (.test test typ) [left, right])
  | equality (left right : AstHOL.Exp) : BoundControlExpression name left → BoundControlExpression name right →
      BoundControlExpression name (.app .equality [left, right])
  | integerArith (action : Arith) (left right : AstHOL.Exp) :
      BoundControlExpression name left → BoundControlExpression name right →
      BoundControlExpression name (.app (.arith action .intT) [left, right])
  | log (op : Lop) (left right : AstHOL.Exp) : BoundControlExpression name left →
      BoundControlExpression name right → BoundControlExpression name (.log op left right)
  | if_ (cond yes no : AstHOL.Exp) : BoundControlExpression name cond → BoundControlExpression name yes →
      BoundControlExpression name no → BoundControlExpression name (.if_ cond yes no)

/-- Control-covered expressions satisfy the preliminary local induction
hypothesis; correspondence of its relations with HOL remains unreviewed. -/
theorem boundLocalIH_controlTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (expr : AstHOL.Exp) (covered : BoundControlExpression name expr) :
    BoundLocalIH (F := F) interp transform name expr := by
  induction covered with
  | base expr covered => exact boundLocalIH_constructorTree interp transform name expr covered
  | variable_ id => exact boundLocalIH_variable interp transform name id
  | function_ arg body => exact boundLocalIH_function interp transform name arg body
  | raise_ body _ ih => exact boundLocalIH_raise interp transform name body ih
  | letAnonymous first body _ _ firstIH bodyIH =>
    exact boundLocalIH_let_anonymous interp transform name first body firstIH bodyIH
  | tannot expr typ _ ih => exact boundLocalIH_tannot interp transform name expr typ ih
  | lannot expr loc _ ih => exact boundLocalIH_lannot interp transform name expr loc ih
  | constructor id args _ ih => exact boundLocalIH_constructor interp transform name id args ih
  | tuple args _ ih => exact boundLocalIH_tuple interp transform name args ih
  | test test typ left right _ _ leftIH rightIH =>
    exact boundLocalIH_test interp transform name test typ left right leftIH rightIH
  | equality left right _ _ leftIH rightIH => exact boundLocalIH_equality interp transform name left right leftIH rightIH
  | integerArith action left right _ _ leftIH rightIH =>
    exact boundLocalIH_integerArith interp transform name action left right leftIH rightIH
  | log op left right _ _ leftIH rightIH => exact boundLocalIH_log interp transform name op left right leftIH rightIH
  | if_ cond yes no _ _ _ condIH yesIH noIH =>
    exact boundLocalIH_if interp transform name cond yes no condIH yesIH noIH

/-- Named bindings with control-covered local bodies satisfy the
preliminary declaration-expression hypothesis. -/
theorem factoredExpressionIH_let_named_control {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (first body : AstHOL.Exp) (covered : BoundControlExpression name body)
    (firstIH : FactoredExpressionIH (F := F) interp transform first) :
    FactoredExpressionIH (F := F) interp transform (.let_ (some name) first body) := by
  apply factoredExpressionIH_let_named_of_local interp transform name first body firstIH
  exact boundLocalIH_controlTree interp transform name body covered

end Flapjack.Compiler.Backend.SourceToFlat

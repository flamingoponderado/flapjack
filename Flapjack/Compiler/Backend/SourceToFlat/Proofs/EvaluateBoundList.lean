import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateBoundPair

/-! Growing argument lists in local environments. The factored relations
remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Abort-sensitive growing simulation for a local expression list. -/
def LocalExpressionListStep {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore) (args : List AstHOL.Exp) : Prop :=
  let sourceResult := EvaluateHOL.evaluate source sourceEnv args
  let flatResult := FlatSem.evaluate flatEnv flat (compileExps trace compMap args)
  ∃ nextGenv, ExprListSim nextGenv compMap trace sourceEnv flatEnv source flat args ∧
    match sourceResult.2 with
    | .err (.abort _) => True
    | _ => GlobalGrowth genv nextGenv ∧
        factoredInvariant interp transform gen nextGenv (start, finish, other) sourceResult.1 flatResult.1 ∧
        envGenRel gen sourceResult.1.evalState ∧ oracForwardRel interp source.evalState sourceResult.1.evalState

/-- A singleton expression step supplies the corresponding list step. -/
theorem localExpressionListStep_singleton {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore) (expr : AstHOL.Exp)
    (step : LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen expr) :
    LocalExpressionListStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen [expr] := by
  obtain ⟨nextGenv, sim, post⟩ := step
  refine ⟨nextGenv, exprListSim_singleton nextGenv compMap trace sourceEnv flatEnv source flat expr sim, ?_⟩
  cases result : (EvaluateHOL.evaluate source sourceEnv [expr]).2 with
  | val value => simpa only [result, compileExps] using post
  | err error =>
    cases error with
    | abort error => simp
    | raise value => simpa only [result, compileExps] using post

/-- The empty local argument list leaves both states unchanged. -/
theorem localExpressionListStep_empty {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (trace : List VarN) (compMap : Environment)
    (gen : EnvironmentGenerationStore)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState) :
    LocalExpressionListStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen [] := by
  refine ⟨genv, ?_, ?_⟩
  · simp only [ExprListSim, EvaluateHOL.evaluate, compileExps, FlatSem.evaluate]
    exact ⟨.value .nil, invariant.2.2.1⟩
  · simp only [EvaluateHOL.evaluate, compileExps, FlatSem.evaluate]
    exact ⟨GlobalGrowth.refl genv, invariant, generation, oracForwardRel_refl interp source.evalState⟩

private theorem sourceEvaluate_cons {F : Type} (source : State F) (env : SemEnv Value)
    (first second : AstHOL.Exp) (rest : List AstHOL.Exp) :
    EvaluateHOL.evaluate source env (first :: second :: rest) =
      let head := EvaluateHOL.evaluate source env [first]
      match head.2 with
      | .err error => (head.1, .err error)
      | .val values =>
        let tail := EvaluateHOL.evaluate head.1 env (second :: rest)
        match tail.2 with
        | .err error => (tail.1, .err error)
        | .val values' => (tail.1, .val (EvaluateHOL.headValue values :: values')) := by
  rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source env [first] []).1]
  rfl

private theorem flatEvaluate_cons {C F : Type} (flat : FlatSem.State C F)
    (flatEnv : FlatSem.Environment FlatSem.Value) (trace : List VarN)
    (compMap : Environment) (first second : AstHOL.Exp) (rest : List AstHOL.Exp) :
    FlatSem.evaluate flatEnv flat (compileExps trace compMap (first :: second :: rest)) =
      let head := FlatSem.evaluate flatEnv flat [compileExp trace compMap first]
      match head.2 with
      | .err error => (head.1, .err error)
      | .val values =>
        let tail := FlatSem.evaluate flatEnv head.1 (compileExps trace compMap (second :: rest))
        match tail.2 with
        | .err error => (tail.1, .err error)
        | .val values' => (tail.1, .val (@Flapjack.holHd FlatSem.Value ⟨FlatSem.unitValue⟩ values :: values')) := by
  simp only [compileExps]
  rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
    [compileExp trace compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1]
  rfl

/-- Sequential composition of a growing expression step and the growing
induction hypothesis for a nonempty tail. -/
theorem localExpressionListStep_cons {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (first second : AstHOL.Exp) (rest : List AstHOL.Exp)
    (headStep : LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen first)
    (tailIH : ∀ (middleGenv : GlobalEnv) (middleSource : State F) (middleFlat : FlatSem.State C F)
      (headValue : Value), EvaluateHOL.evaluate source sourceEnv [first] = (middleSource, .val [headValue]) →
      GlobalGrowth genv middleGenv →
      factoredInvariant interp transform gen middleGenv (start, finish, other) middleSource middleFlat →
      envGenRel gen middleSource.evalState →
      LocalExpressionListStep interp transform middleGenv start finish other middleSource middleFlat
        sourceEnv flatEnv trace compMap gen (second :: rest)) :
    LocalExpressionListStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen
      (first :: second :: rest) := by
  obtain ⟨middleGenv, headSim, headPost⟩ := headStep
  unfold ExprSim at headSim
  generalize sourceHead : EvaluateHOL.evaluate source sourceEnv [first] = sourceHeadResult at headSim headPost
  obtain ⟨middleSource, sourceHeadResult⟩ := sourceHeadResult
  generalize flatHead : FlatSem.evaluate flatEnv flat [compileExp trace compMap first] = flatHeadResult at headSim headPost
  obtain ⟨middleFlat, flatHeadResult⟩ := flatHeadResult
  obtain ⟨headRelated, headStates⟩ := headSim
  cases headRelated with
  | abort error =>
    refine ⟨middleGenv, ?_, ?_⟩
    · unfold ExprListSim
      rw [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead]
      exact ⟨.abort error, headStates⟩
    · rw [sourceEvaluate_cons, sourceHead]
      trivial
  | raise headValue =>
    refine ⟨middleGenv, ?_, ?_⟩
    · unfold ExprListSim
      rw [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead]
      exact ⟨.raise headValue, headStates⟩
    · rw [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead]
      exact headPost
  | @value sourceValues flatValues headValues =>
    obtain ⟨sourceValue, sourceEq⟩ := EvaluateProps.evaluateSingFull source middleSource sourceEnv first sourceValues sourceHead
    subst sourceValues
    cases headValues with
    | cons headValue tailValues =>
      cases tailValues with
      | nil =>
        obtain ⟨headGrowth, middleInvariant, middleGeneration, headForward⟩ := headPost
        obtain ⟨finalGenv, tailSim, tailPost⟩ := tailIH middleGenv middleSource middleFlat sourceValue sourceHead headGrowth
          middleInvariant middleGeneration
        unfold ExprListSim at tailSim
        generalize sourceTail : EvaluateHOL.evaluate middleSource sourceEnv (second :: rest) = sourceTailResult at tailSim tailPost
        obtain ⟨finalSource, sourceTailResult⟩ := sourceTailResult
        generalize flatTail : FlatSem.evaluate flatEnv middleFlat (compileExps trace compMap (second :: rest)) = flatTailResult at tailSim tailPost
        obtain ⟨finalFlat, flatTailResult⟩ := flatTailResult
        obtain ⟨tailRelated, tailStates⟩ := tailSim
        cases tailRelated with
        | abort error =>
          refine ⟨finalGenv, ?_, ?_⟩
          · unfold ExprListSim
            simp only [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead, sourceTail, flatTail]
            exact ⟨.abort error, tailStates⟩
          · simp only [sourceEvaluate_cons, sourceHead, sourceTail]
        | raise tailValue =>
          obtain ⟨tailGrowth, finalInvariant, finalGeneration, tailForward⟩ := tailPost
          refine ⟨finalGenv, ?_, ?_⟩
          · unfold ExprListSim
            simp only [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead, sourceTail, flatTail]
            exact ⟨.raise tailValue, tailStates⟩
          · simp only [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead, sourceTail, flatTail]
            exact ⟨headGrowth.trans tailGrowth, finalInvariant, finalGeneration,
              oracForwardRel_trans interp _ _ _ ⟨headForward, tailForward⟩⟩
        | value tailValues =>
          obtain ⟨tailGrowth, finalInvariant, finalGeneration, tailForward⟩ := tailPost
          refine ⟨finalGenv, ?_, ?_⟩
          · unfold ExprListSim
            simp only [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead, sourceTail, flatTail]
            simp only [EvaluateHOL.headValue, Flapjack.holHd]
            exact ⟨.value (.cons (valueRel_growth middleGenv finalGenv tailGrowth _ _ headValue) tailValues), tailStates⟩
          · simp only [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead, sourceTail, flatTail]
            exact ⟨headGrowth.trans tailGrowth, finalInvariant, finalGeneration,
              oracForwardRel_trans interp _ _ _ ⟨headForward, tailForward⟩⟩


/-- Local expression induction hypotheses compose over arbitrary lists, with
the safe tail derived only after the preceding expression succeeds. -/
theorem boundLocalListStep_of_each {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (expressions : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ expressions → BoundLocalIH (F := F) interp transform name expr) :
    ∀ (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
      (source : State F) (flat : FlatSem.State C F) (baseEnv : SemEnv Value)
      (trace : List VarN) (baseMap : Environment) (gen : EnvironmentGenerationStore)
      (value : Value) (flatValue : FlatSem.Value),
      ValueRel genv value flatValue →
      factoredInvariant interp transform gen genv (start, finish, other) source flat →
      envGenRel gen source.evalState →
      (∀ last, EvaluateHOL.evaluate source { baseEnv with v := nsBind name value baseEnv.v } expressions ≠
        (last, .err (.abort .typeError))) →
      LocalExpressionListStep interp transform genv start finish other source flat
        { baseEnv with v := nsBind name value baseEnv.v } ⟨[(name, flatValue)]⟩ trace
        { baseMap with v := nsBind name (.localName .none name) baseMap.v } gen expressions := by
  induction expressions with
  | nil =>
    intro genv start finish other source flat baseEnv trace baseMap gen value flatValue _ invariant generation _
    exact localExpressionListStep_empty interp transform genv start finish other source flat _ _ trace _ gen
      invariant generation
  | cons first rest ih =>
    intro genv start finish other source flat baseEnv trace baseMap gen value flatValue related invariant generation safe
    let sourceEnv := { baseEnv with v := nsBind name value baseEnv.v }
    let compMap := { baseMap with v := nsBind name (.localName .none name) baseMap.v }
    let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
    cases rest with
    | nil =>
      apply localExpressionListStep_singleton
      exact each first (by simp) genv start finish other source flat baseEnv trace baseMap gen value flatValue
        related invariant generation safe
    | cons second tail =>
      have headSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [first] ≠ (last, .err (.abort .typeError)) := by
        intro last bad
        apply safe last
        change EvaluateHOL.evaluate source sourceEnv (first :: second :: tail) = _
        simp only [sourceEvaluate_cons, bad]
      have headStep := each first (by simp) genv start finish other source flat baseEnv trace baseMap gen value flatValue
        related invariant generation headSafe
      change LocalExpressionListStep interp transform genv start finish other source flat sourceEnv flatEnv trace
        compMap gen (first :: second :: tail)
      apply localExpressionListStep_cons interp transform genv start finish other source flat sourceEnv flatEnv trace
        compMap gen first second tail headStep
      intro middleGenv middleSource middleFlat headValue headRun growth middleInvariant middleGeneration
      have tailSafe : ∀ last, EvaluateHOL.evaluate middleSource sourceEnv (second :: tail) ≠
          (last, .err (.abort .typeError)) := by
        intro last bad
        apply safe last
        change EvaluateHOL.evaluate source sourceEnv (first :: second :: tail) = _
        simp only [sourceEvaluate_cons, headRun, bad]
      apply ih
      · intro expr member
        exact each expr (List.mem_cons_of_mem _ member)
      · exact valueRel_growth genv middleGenv growth value flatValue related
      · exact middleInvariant
      · exact middleGeneration
      · exact tailSafe

/-- Tuple construction composes growing local argument simulations in the
source evaluator's right-to-left order. -/
theorem boundLocalIH_tuple {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → BoundLocalIH (F := F) interp transform name expr) :
    BoundLocalIH (F := F) interp transform name (.con none args) := by
  intro genv start finish other source flat baseEnv trace baseMap gen value flatValue related invariant generation safe
  let sourceEnv := { baseEnv with v := nsBind name value baseEnv.v }
  let compMap := { baseMap with v := nsBind name (.localName .none name) baseMap.v }
  let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
  change LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen
    (.con none args)
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv args.reverse ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.con none args] = _
    simp [EvaluateHOL.evaluate, doConCheck, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundLocalListStep_of_each interp transform name args.reverse
    (fun expr member => each expr (List.mem_reverse.mp member)) genv start finish other source flat baseEnv
    trace baseMap gen value flatValue related invariant generation argsSafe
  refine ⟨nextGenv, exprSim_tuple nextGenv compMap trace sourceEnv flatEnv source flat args argsSim, ?_⟩
  unfold ExprListSim at argsSim
  rw [compileExps_reverse] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv args.reverse = sourceResult at argsSim post ⊢
  obtain ⟨sourceNext, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat (compileExps trace compMap args).reverse = flatResult at argsSim post ⊢
  obtain ⟨flatNext, flatResult⟩ := flatResult
  obtain ⟨resultRel, _⟩ := argsSim
  cases resultRel with
  | abort error =>
    simp [EvaluateHOL.evaluate, doConCheck, sourceRun]
  | raise related =>
    simpa [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, doConCheck, sourceRun, flatRun] using post
  | value related =>
    simpa [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, doConCheck, buildConv, sourceRun, flatRun] using post

/-- Recursive local coverage additionally permits tuples of arbitrary
covered local expressions. -/
inductive BoundTupleExpression (name : VarN) : AstHOL.Exp → Prop where
  | base (expr : AstHOL.Exp) : BoundRecursiveExpression name expr → BoundTupleExpression name expr
  | tuple (args : List AstHOL.Exp) : (∀ expr, expr ∈ args → BoundTupleExpression name expr) →
      BoundTupleExpression name (.con none args)
  | test (test : Test) (typ : PrimType) (left right : AstHOL.Exp) :
      BoundTupleExpression name left → BoundTupleExpression name right →
      BoundTupleExpression name (.app (.test test typ) [left, right])
  | equality (left right : AstHOL.Exp) : BoundTupleExpression name left → BoundTupleExpression name right →
      BoundTupleExpression name (.app .equality [left, right])
  | integerArith (action : Arith) (left right : AstHOL.Exp) :
      BoundTupleExpression name left → BoundTupleExpression name right →
      BoundTupleExpression name (.app (.arith action .intT) [left, right])
  | log (op : Lop) (left right : AstHOL.Exp) : BoundTupleExpression name left →
      BoundTupleExpression name right → BoundTupleExpression name (.log op left right)
  | if_ (cond yes no : AstHOL.Exp) : BoundTupleExpression name cond → BoundTupleExpression name yes →
      BoundTupleExpression name no → BoundTupleExpression name (.if_ cond yes no)

/-- Tuple-covered expressions satisfy the preliminary growing local
induction hypothesis; HOL correspondence review remains outstanding. -/
theorem boundLocalIH_tupleTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (expr : AstHOL.Exp) (covered : BoundTupleExpression name expr) :
    BoundLocalIH (F := F) interp transform name expr := by
  induction covered with
  | base expr covered => exact boundLocalIH_recursive interp transform name expr covered
  | tuple args _ ih => exact boundLocalIH_tuple interp transform name args ih
  | test test typ left right _ _ leftIH rightIH =>
    exact boundLocalIH_test interp transform name test typ left right leftIH rightIH
  | equality left right _ _ leftIH rightIH =>
    exact boundLocalIH_equality interp transform name left right leftIH rightIH
  | integerArith action left right _ _ leftIH rightIH =>
    exact boundLocalIH_integerArith interp transform name action left right leftIH rightIH
  | log op left right _ _ leftIH rightIH => exact boundLocalIH_log interp transform name op left right leftIH rightIH
  | if_ cond yes no _ _ _ condIH yesIH noIH =>
    exact boundLocalIH_if interp transform name cond yes no condIH yesIH noIH

/-- Named bindings with tuple-covered local bodies satisfy the factored
declaration-expression induction hypothesis. -/
theorem factoredExpressionIH_let_named_tuple {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (first body : AstHOL.Exp) (covered : BoundTupleExpression name body)
    (firstIH : FactoredExpressionIH (F := F) interp transform first) :
    FactoredExpressionIH (F := F) interp transform (.let_ (some name) first body) := by
  apply factoredExpressionIH_let_named_of_local interp transform name first body firstIH
  exact boundLocalIH_tupleTree interp transform name body covered

end Flapjack.Compiler.Backend.SourceToFlat

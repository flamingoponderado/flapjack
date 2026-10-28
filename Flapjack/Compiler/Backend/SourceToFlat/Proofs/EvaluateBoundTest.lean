import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateBoundPure

/-! Primitive comparisons of state-preserving local expressions over the
preliminary factored source-to-flat relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- A comparison of covered local expressions preserves the growing step,
including right-to-left evaluation and rejected primitive operands. -/
theorem localExpressionStep_boundTest {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (baseEnv : SemEnv Value)
    (trace : List VarN) (baseMap : Environment) (gen : EnvironmentGenerationStore)
    (name : VarN) (value : Value) (flatValue : FlatSem.Value) (test : Test) (typ : PrimType)
    (left right : AstHOL.Exp) (leftCovered : BoundPureExpression name left)
    (rightCovered : BoundPureExpression name right) (relatedValue : ValueRel genv value flatValue)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (safe : ∀ last, EvaluateHOL.evaluate source { baseEnv with v := nsBind name value baseEnv.v }
      [.app (.test test typ) [left, right]] ≠ (last, .err (.abort .typeError))) :
    LocalExpressionStep interp transform genv start finish other source flat
      { baseEnv with v := nsBind name value baseEnv.v } ⟨[(name, flatValue)]⟩ trace
      { baseMap with v := nsBind name (.localName .none name) baseMap.v } gen
      (.app (.test test typ) [left, right]) := by
  let sourceEnv := { baseEnv with v := nsBind name value baseEnv.v }
  let compMap := { baseMap with v := nsBind name (.localName .none name) baseMap.v }
  let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
  have each : ∀ e, e ∈ [right, left] → ∀ (s : State F) (f : FlatSem.State C F), StateRel genv s f →
      ExprSim genv compMap trace sourceEnv flatEnv s f e ∧
      (EvaluateHOL.evaluate s sourceEnv [e]).1 = s ∧
      (FlatSem.evaluate flatEnv f [compileExp trace compMap e]).1 = f := by
    intro e member s f states
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact boundPure_simulation genv name value flatValue relatedValue baseEnv trace baseMap _ rightCovered s f states
    · exact boundPure_simulation genv name value flatValue relatedValue baseEnv trace baseMap _ leftCovered s f states
  have argsSim : ExprListSim genv compMap trace sourceEnv flatEnv source flat [right, left] := by
    apply exprListSim_of_expressions genv compMap trace sourceEnv flatEnv [right, left]
    · intro e member s f states; exact (each e member s f states).1
    · exact invariant.2.2.1
  have sourceSame : (EvaluateHOL.evaluate source sourceEnv [right, left]).1 = source := by
    apply evaluateList_state_of_singletons
    intro e member
    exact (each e member source flat invariant.2.2.1).2.1
  have flatSame : (FlatSem.evaluate flatEnv flat (compileExps trace compMap [right, left])).1 = flat := by
    apply flatEvaluateList_state_of_singletons
    intro e member
    exact (each e member source flat invariant.2.2.1).2.2
  let nextGenv := genv
  have post : match (EvaluateHOL.evaluate source sourceEnv [right, left]).2 with
    | .err (.abort _) => True
    | _ => GlobalGrowth genv nextGenv ∧
        factoredInvariant interp transform gen nextGenv (start, finish, other)
          (EvaluateHOL.evaluate source sourceEnv [right, left]).1
          (FlatSem.evaluate flatEnv flat (compileExps trace compMap [right, left])).1 ∧
        envGenRel gen (EvaluateHOL.evaluate source sourceEnv [right, left]).1.evalState ∧
        oracForwardRel interp source.evalState (EvaluateHOL.evaluate source sourceEnv [right, left]).1.evalState := by
    cases result : (EvaluateHOL.evaluate source sourceEnv [right, left]).2 with
    | val values =>
      simp only [sourceSame, flatSame]
      exact ⟨GlobalGrowth.refl genv, invariant, generation, oracForwardRel_refl interp source.evalState⟩
    | err error =>
      cases error with
      | abort error => simp
      | raise value =>
        simp only [sourceSame, flatSame]
        exact ⟨GlobalGrowth.refl genv, invariant, generation, oracForwardRel_refl interp source.evalState⟩
  have argsSimCopy := argsSim
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    refine ⟨nextGenv, exprSim_test nextGenv compMap trace sourceEnv flatEnv source flat left right test typ
      nextInvariant.1 argsSimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat
      [compileExp trace compMap right, compileExp trace compMap left]
      (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
    exact ⟨growth, nextInvariant, nextGeneration, forward⟩
  | @value sourceValues flatValues valuesRel =>
    have length := EvaluateProps.evaluateLengthFull source nextSource sourceEnv [right, left] sourceValues sourceRun
    have two : ∃ v p, sourceValues = [v, p] := by
      cases sourceValues with
      | nil => simp at length
      | cons v tail =>
        cases tail with
        | nil => simp at length
        | cons p rest =>
          cases rest with
          | nil => exact ⟨v, p, rfl⟩
          | cons q rest => simp at length
    obtain ⟨sourceRight, sourceLeft, rfl⟩ := two
    cases valuesRel with
    | cons rightRel tail =>
      cases tail with
      | cons leftRel tail =>
        cases tail with
        | nil =>
          rename_i flatRight flatLeft
          obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
          cases comparison : SemanticPrimitivesHOL.doTest test typ sourceLeft sourceRight with
          | typeError =>
            apply False.elim
            apply safe nextSource
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, doApp, comparison, EvaluateHOL.typeError]
          | val b =>
            have flatComparison := doTest_related nextGenv nextInvariant.1 test typ sourceLeft sourceRight
              flatLeft flatRight b leftRel rightRel comparison
            refine ⟨nextGenv, exprSim_test nextGenv compMap trace sourceEnv flatEnv source flat left right test typ
              nextInvariant.1 argsSimCopy safe, ?_⟩
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flat
              [compileExp trace compMap right, compileExp trace compMap left]
              (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            simpa [getOpClass, doApp, comparison, astOpToFlatOp, FlatSem.applyResult,
              FlatSem.doApp, FlatSem.doAppNumeric, flatComparison, EvaluateHOL.listResult] using
              And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))


/-- Equality of covered local expressions preserves the growing step,
including right-to-left evaluation and rejected primitive operands. -/
theorem localExpressionStep_boundEquality {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (baseEnv : SemEnv Value)
    (trace : List VarN) (baseMap : Environment) (gen : EnvironmentGenerationStore)
    (name : VarN) (value : Value) (flatValue : FlatSem.Value)
    (left right : AstHOL.Exp) (leftCovered : BoundPureExpression name left)
    (rightCovered : BoundPureExpression name right) (relatedValue : ValueRel genv value flatValue)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (safe : ∀ last, EvaluateHOL.evaluate source { baseEnv with v := nsBind name value baseEnv.v }
      [.app .equality [left, right]] ≠ (last, .err (.abort .typeError))) :
    LocalExpressionStep interp transform genv start finish other source flat
      { baseEnv with v := nsBind name value baseEnv.v } ⟨[(name, flatValue)]⟩ trace
      { baseMap with v := nsBind name (.localName .none name) baseMap.v } gen
      (.app .equality [left, right]) := by
  let sourceEnv := { baseEnv with v := nsBind name value baseEnv.v }
  let compMap := { baseMap with v := nsBind name (.localName .none name) baseMap.v }
  let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
  have each : ∀ e, e ∈ [right, left] → ∀ (s : State F) (f : FlatSem.State C F), StateRel genv s f →
      ExprSim genv compMap trace sourceEnv flatEnv s f e ∧
      (EvaluateHOL.evaluate s sourceEnv [e]).1 = s ∧
      (FlatSem.evaluate flatEnv f [compileExp trace compMap e]).1 = f := by
    intro e member s f states
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact boundPure_simulation genv name value flatValue relatedValue baseEnv trace baseMap _ rightCovered s f states
    · exact boundPure_simulation genv name value flatValue relatedValue baseEnv trace baseMap _ leftCovered s f states
  have argsSim : ExprListSim genv compMap trace sourceEnv flatEnv source flat [right, left] := by
    apply exprListSim_of_expressions genv compMap trace sourceEnv flatEnv [right, left]
    · intro e member s f states; exact (each e member s f states).1
    · exact invariant.2.2.1
  have sourceSame : (EvaluateHOL.evaluate source sourceEnv [right, left]).1 = source := by
    apply evaluateList_state_of_singletons
    intro e member
    exact (each e member source flat invariant.2.2.1).2.1
  have flatSame : (FlatSem.evaluate flatEnv flat (compileExps trace compMap [right, left])).1 = flat := by
    apply flatEvaluateList_state_of_singletons
    intro e member
    exact (each e member source flat invariant.2.2.1).2.2
  let nextGenv := genv
  have post : match (EvaluateHOL.evaluate source sourceEnv [right, left]).2 with
    | .err (.abort _) => True
    | _ => GlobalGrowth genv nextGenv ∧
        factoredInvariant interp transform gen nextGenv (start, finish, other)
          (EvaluateHOL.evaluate source sourceEnv [right, left]).1
          (FlatSem.evaluate flatEnv flat (compileExps trace compMap [right, left])).1 ∧
        envGenRel gen (EvaluateHOL.evaluate source sourceEnv [right, left]).1.evalState ∧
        oracForwardRel interp source.evalState (EvaluateHOL.evaluate source sourceEnv [right, left]).1.evalState := by
    cases result : (EvaluateHOL.evaluate source sourceEnv [right, left]).2 with
    | val values =>
      simp only [sourceSame, flatSame]
      exact ⟨GlobalGrowth.refl genv, invariant, generation, oracForwardRel_refl interp source.evalState⟩
    | err error =>
      cases error with
      | abort error => simp
      | raise value =>
        simp only [sourceSame, flatSame]
        exact ⟨GlobalGrowth.refl genv, invariant, generation, oracForwardRel_refl interp source.evalState⟩
  have argsSimCopy := argsSim
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    refine ⟨nextGenv, exprSim_equality nextGenv compMap trace sourceEnv flatEnv source flat left right
      nextInvariant.1 argsSimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat
      [compileExp trace compMap right, compileExp trace compMap left]
      (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
    exact ⟨growth, nextInvariant, nextGeneration, forward⟩
  | @value sourceValues flatValues valuesRel =>
    have length := EvaluateProps.evaluateLengthFull source nextSource sourceEnv [right, left] sourceValues sourceRun
    have two : ∃ v p, sourceValues = [v, p] := by
      cases sourceValues with
      | nil => simp at length
      | cons v tail =>
        cases tail with
        | nil => simp at length
        | cons p rest =>
          cases rest with
          | nil => exact ⟨v, p, rfl⟩
          | cons q rest => simp at length
    obtain ⟨sourceRight, sourceLeft, rfl⟩ := two
    cases valuesRel with
    | cons rightRel tail =>
      cases tail with
      | cons leftRel tail =>
        cases tail with
        | nil =>
          rename_i flatRight flatLeft
          obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
          cases comparison : SemanticPrimitivesHOL.doEq sourceLeft sourceRight with
          | typeError =>
            apply False.elim
            apply safe nextSource
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, doApp, doAppNumericCore, doAppBasic, comparison, EvaluateHOL.typeError]
          | val b =>
            have flatComparison := equality_preserved nextGenv nextInvariant.1 sourceLeft sourceRight
              flatLeft flatRight leftRel rightRel
            refine ⟨nextGenv, exprSim_equality nextGenv compMap trace sourceEnv flatEnv source flat left right
              nextInvariant.1 argsSimCopy safe, ?_⟩
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flat
              [compileExp trace compMap right, compileExp trace compMap left]
              (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            simpa [getOpClass, doApp, doAppNumericCore, doAppBasic, comparison, astOpToFlatOp, FlatSem.applyResult,
              FlatSem.doApp, FlatSem.doAppNumeric, flatComparison, EvaluateHOL.listResult] using
              And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))


/-- A named binding with a primitive comparison of covered local operands
satisfies the preliminary declaration-expression induction hypothesis. -/
theorem factoredExpressionIH_let_named_test {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (first : AstHOL.Exp) (test : Test) (typ : PrimType) (left right : AstHOL.Exp)
    (leftCovered : BoundPureExpression name left) (rightCovered : BoundPureExpression name right)
    (firstIH : FactoredExpressionIH (F := F) interp transform first) :
    FactoredExpressionIH (F := F) interp transform (.let_ (some name) first (.app (.test test typ) [left, right])) := by
  apply factoredExpressionIH_let_named_of_local interp transform name first _ firstIH
  intro genv start finish other source flat sourceEnv trace compMap gen value flatValue related invariant generation safe
  exact localExpressionStep_boundTest interp transform genv start finish other source flat sourceEnv trace compMap gen
    name value flatValue test typ left right leftCovered rightCovered related invariant generation safe

/-- A named binding with equality over covered local operands satisfies the
preliminary declaration-expression induction hypothesis. -/
theorem factoredExpressionIH_let_named_equality {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (first left right : AstHOL.Exp)
    (leftCovered : BoundPureExpression name left) (rightCovered : BoundPureExpression name right)
    (firstIH : FactoredExpressionIH (F := F) interp transform first) :
    FactoredExpressionIH (F := F) interp transform (.let_ (some name) first (.app .equality [left, right])) := by
  apply factoredExpressionIH_let_named_of_local interp transform name first _ firstIH
  intro genv start finish other source flat sourceEnv trace compMap gen value flatValue related invariant generation safe
  exact localExpressionStep_boundEquality interp transform genv start finish other source flat sourceEnv trace compMap gen
    name value flatValue left right leftCovered rightCovered related invariant generation safe

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
  | letNamedTest (name : VarN) (first : AstHOL.Exp) (test : Test) (typ : PrimType) (left right : AstHOL.Exp) :
      FactoredBoundExpression first → BoundPureExpression name left → BoundPureExpression name right →
      FactoredBoundExpression (.let_ (some name) first (.app (.test test typ) [left, right]))
  | letNamedEquality (name : VarN) (first left right : AstHOL.Exp) :
      FactoredBoundExpression first → BoundPureExpression name left → BoundPureExpression name right →
      FactoredBoundExpression (.let_ (some name) first (.app .equality [left, right]))
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
  | letNamedTest name first test typ left right _ lc rc firstIH =>
    exact factoredExpressionIH_let_named_test interp transform name first test typ left right lc rc firstIH
  | letNamedEquality name first left right _ lc rc firstIH =>
    exact factoredExpressionIH_let_named_equality interp transform name first left right lc rc firstIH
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

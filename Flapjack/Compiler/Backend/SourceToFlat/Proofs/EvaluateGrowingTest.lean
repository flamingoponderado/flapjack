import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateGrowingArith

/-! Primitive comparisons over the preliminary growing expression simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Primitive comparisons compose growing operand induction hypotheses,
including early errors and right-to-left operand evaluation. -/
theorem factoredExpressionIH_test {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (test : Test) (typ : PrimType) (left right : AstHOL.Exp)
    (leftIH : FactoredExpressionIH (F := F) interp transform left)
    (rightIH : FactoredExpressionIH (F := F) interp transform right) :
    FactoredExpressionIH (F := F) interp transform (.app (.test test typ) [left, right]) := by
  intro genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation safe
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, bad]
  have argsStep := dletExpressionListStep_of_each interp transform [right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> assumption)
    genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation argsSafe
  obtain ⟨nextGenv, argsSim, post⟩ := argsStep
  have argsSimCopy := argsSim
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate ⟨[]⟩ flat [compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
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
      rw [(FlatSem.fixClock_evaluations ⟨[]⟩ flat
        [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    refine ⟨nextGenv, exprSim_test nextGenv compMap trace sourceEnv ⟨[]⟩ source flat left right test typ
      nextInvariant.1 argsSimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(FlatSem.fixClock_evaluations ⟨[]⟩ flat
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
            refine ⟨nextGenv, exprSim_test nextGenv compMap trace sourceEnv ⟨[]⟩ source flat left right test typ
              nextInvariant.1 argsSimCopy safe, ?_⟩
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(FlatSem.fixClock_evaluations ⟨[]⟩ flat
              [compileExp trace compMap right, compileExp trace compMap left]
              (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            simpa [getOpClass, doApp, comparison, astOpToFlatOp, FlatSem.applyResult,
              FlatSem.doApp, FlatSem.doAppNumeric, flatComparison, EvaluateHOL.listResult] using
              And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))

/-- Covered expression trees including primitive comparisons and the earlier
arithmetic, logical, conditional, sequencing, constructor and raise forms. -/
inductive FactoredTestExpression : AstHOL.Exp → Prop where
  | base (expr : AstHOL.Exp) : FactoredArithExpression expr → FactoredTestExpression expr
  | constructor (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp) :
      (∀ expr, expr ∈ args → FactoredTestExpression expr) → FactoredTestExpression (.con name args)
  | raise_ (body : AstHOL.Exp) : FactoredTestExpression body → FactoredTestExpression (.raise body)
  | letAnonymous (first body : AstHOL.Exp) : FactoredTestExpression first → FactoredTestExpression body →
      FactoredTestExpression (.let_ none first body)
  | if_ (cond yes no : AstHOL.Exp) : FactoredTestExpression cond → FactoredTestExpression yes →
      FactoredTestExpression no → FactoredTestExpression (.if_ cond yes no)
  | log (op : Lop) (left right : AstHOL.Exp) : FactoredTestExpression left → FactoredTestExpression right →
      FactoredTestExpression (.log op left right)
  | integerArith (action : Arith) (left right : AstHOL.Exp) : FactoredTestExpression left →
      FactoredTestExpression right → FactoredTestExpression (.app (.arith action .intT) [left, right])
  | test (test : Test) (typ : PrimType) (left right : AstHOL.Exp) : FactoredTestExpression left →
      FactoredTestExpression right → FactoredTestExpression (.app (.test test typ) [left, right])
  | tannot (expr : AstHOL.Exp) (typ : AstT) : FactoredTestExpression expr → FactoredTestExpression (.tannot expr typ)
  | lannot (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) : FactoredTestExpression expr →
      FactoredTestExpression (.lannot expr loc)

/-- Covered comparison expression trees satisfy the factored induction
hypothesis. The underlying relations remain pending HOL review. -/
theorem factoredExpressionIH_testTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expr : AstHOL.Exp) (covered : FactoredTestExpression expr) :
    FactoredExpressionIH (F := F) interp transform expr := by
  induction covered with
  | base expr supported => exact factoredExpressionIH_arithTree interp transform expr supported
  | constructor name args _ ih => exact factoredExpressionIH_constructor interp transform name args ih
  | raise_ body _ ih => exact factoredExpressionIH_raise interp transform body ih
  | letAnonymous first body _ _ firstIH bodyIH =>
    exact factoredExpressionIH_let_anonymous interp transform first body firstIH bodyIH
  | if_ cond yes no _ _ _ condIH yesIH noIH => exact factoredExpressionIH_if interp transform cond yes no condIH yesIH noIH
  | log op left right _ _ leftIH rightIH => exact factoredExpressionIH_log interp transform op left right leftIH rightIH
  | integerArith action left right _ _ leftIH rightIH =>
    exact factoredExpressionIH_integerArith interp transform action left right leftIH rightIH
  | test test typ left right _ _ leftIH rightIH =>
    exact factoredExpressionIH_test interp transform test typ left right leftIH rightIH
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

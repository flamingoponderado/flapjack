import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateGrowingLog
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateApply

/-! Integer arithmetic over the preliminary growing expression simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Integer arithmetic composes growing operand induction hypotheses,
including division exceptions and right-to-left operand evaluation. -/
theorem factoredExpressionIH_integerArith {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (action : Arith) (left right : AstHOL.Exp)
    (leftIH : FactoredExpressionIH (F := F) interp transform left)
    (rightIH : FactoredExpressionIH (F := F) interp transform right) :
    FactoredExpressionIH (F := F) interp transform (.app (.arith action .intT) [left, right]) := by
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
    refine ⟨nextGenv, exprSim_integerArith nextGenv compMap trace sourceEnv ⟨[]⟩ source flat left right action
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
          have successful : doApp (nextSource.refs, nextSource.ffi) (.arith action .intT)
              [sourceLeft, sourceRight] ≠ none := by
            intro failed
            apply safe nextSource
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨leftInt, rightInt, operands⟩ := integerArith_operands nextSource action [sourceLeft, sourceRight] successful
          simp only [List.cons.injEq] at operands
          obtain ⟨rfl, rfl, _⟩ := operands
          have flatLeftEq := (valueRel_literal_iff nextGenv (.intLit leftInt) flatLeft).mp leftRel
          have flatRightEq := (valueRel_literal_iff nextGenv (.intLit rightInt) flatRight).mp rightRel
          subst flatLeft
          subst flatRight
          have primitive := integerArith_related nextGenv nextInvariant.1 nextSource nextFlat action leftInt rightInt
          cases sourceApp : doApp (nextSource.refs, nextSource.ffi) (.arith action .intT)
              [.litv (.intLit leftInt), .litv (.intLit rightInt)] with
          | none => exact (successful sourceApp).elim
          | some sourceOut =>
            cases sourceOut with
            | mk store sourceResult =>
              cases store with
              | mk refs ffi =>
                cases flatApp : FlatSem.doAppNumeric nextFlat (.arith action .intT)
                    [.litv (.intLit leftInt), .litv (.intLit rightInt)] with
                | none => simp [sourceApp, flatApp] at primitive
                | some flatOut =>
                  cases flatOut with
                  | none => simp [sourceApp, flatApp] at primitive
                  | some flatOut =>
                    cases flatOut with
                    | mk flatAfter flatResult =>
                      simp only [sourceApp, flatApp] at primitive
                      obtain ⟨rfl, rfl, rfl, resultRel⟩ := primitive
                      refine ⟨nextGenv, exprSim_integerArith nextGenv compMap trace sourceEnv ⟨[]⟩ source flat
                        left right action nextInvariant.1 argsSimCopy safe, ?_⟩
                      rw [EvaluateHOL.evaluate]
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
                      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                      rw [FlatSem.evaluate]
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                      rw [(FlatSem.fixClock_evaluations ⟨[]⟩ flat
                        [compileExp trace compMap right, compileExp trace compMap left]
                        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                        getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp, flatApp]
                      cases resultRel with
                      | value valueRel =>
                        simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant
                          (And.intro nextGeneration forward))
                      | raise valueRel =>
                        simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant
                          (And.intro nextGeneration forward))
                      | abort error => simp [EvaluateHOL.listResult]

/-- Covered expression trees including integer arithmetic and the prior
logical, conditional, sequencing, constructor and raise forms. -/
inductive FactoredArithExpression : AstHOL.Exp → Prop where
  | base (expr : AstHOL.Exp) : FactoredLogExpression expr → FactoredArithExpression expr
  | constructor (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp) :
      (∀ expr, expr ∈ args → FactoredArithExpression expr) → FactoredArithExpression (.con name args)
  | raise_ (body : AstHOL.Exp) : FactoredArithExpression body → FactoredArithExpression (.raise body)
  | letAnonymous (first body : AstHOL.Exp) : FactoredArithExpression first → FactoredArithExpression body →
      FactoredArithExpression (.let_ none first body)
  | if_ (cond yes no : AstHOL.Exp) : FactoredArithExpression cond → FactoredArithExpression yes →
      FactoredArithExpression no → FactoredArithExpression (.if_ cond yes no)
  | log (op : Lop) (left right : AstHOL.Exp) : FactoredArithExpression left → FactoredArithExpression right →
      FactoredArithExpression (.log op left right)
  | integerArith (action : Arith) (left right : AstHOL.Exp) : FactoredArithExpression left →
      FactoredArithExpression right → FactoredArithExpression (.app (.arith action .intT) [left, right])
  | tannot (expr : AstHOL.Exp) (typ : AstT) : FactoredArithExpression expr → FactoredArithExpression (.tannot expr typ)
  | lannot (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) : FactoredArithExpression expr →
      FactoredArithExpression (.lannot expr loc)

/-- Covered arithmetic expression trees satisfy the factored induction
hypothesis. The underlying relations remain pending HOL review. -/
theorem factoredExpressionIH_arithTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expr : AstHOL.Exp) (covered : FactoredArithExpression expr) :
    FactoredExpressionIH (F := F) interp transform expr := by
  induction covered with
  | base expr supported => exact factoredExpressionIH_logTree interp transform expr supported
  | constructor name args _ ih => exact factoredExpressionIH_constructor interp transform name args ih
  | raise_ body _ ih => exact factoredExpressionIH_raise interp transform body ih
  | letAnonymous first body _ _ firstIH bodyIH =>
    exact factoredExpressionIH_let_anonymous interp transform first body firstIH bodyIH
  | if_ cond yes no _ _ _ condIH yesIH noIH => exact factoredExpressionIH_if interp transform cond yes no condIH yesIH noIH
  | log op left right _ _ leftIH rightIH => exact factoredExpressionIH_log interp transform op left right leftIH rightIH
  | integerArith action left right _ _ leftIH rightIH =>
    exact factoredExpressionIH_integerArith interp transform action left right leftIH rightIH
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

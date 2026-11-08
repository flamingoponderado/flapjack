import Flapjack.EvaluateProps.NoEvalBase

/-! Branching cases for evaluation without an Eval state. -/
namespace Flapjack.EvaluateProps
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- The conditional-expression induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_If {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (cond yes no : AstHOL.Exp)
    (ih : (∀ middle outcome values branch, evaluate s env [cond] = (middle, outcome) ∧
      outcome = .val values ∧ doIf (headValue values) yes no = some branch →
      NoEvalExpsAt es middle env [branch]) ∧ NoEvalExpsAt es s env [cond]) :
    NoEvalExpsAt es s env [.if_ cond yes no] := by
  obtain ⟨branchIH, condIH⟩ := ih
  intro s' res ⟨run, absent, safe⟩
  rw [evaluate, (fixClockEvaluate s env [cond] []).1] at run
  cases condRun : evaluate s env [cond] with
  | mk middle result =>
    cases result with
    | err error =>
      simp only [condRun] at run
      cases run
      have target := condIH s' (.err error) ⟨condRun, absent, safe⟩
      refine ⟨target.1, ?_⟩
      rw [evaluate, (fixClockEvaluate _ _ [cond] []).1, target.2]
    | val values =>
      simp only [condRun] at run
      split at run
      next _ =>
        simp [typeError] at run
        obtain ⟨_, rfl⟩ := run
        exact (safe rfl).elim
      next branch chosen =>
        have targetCond := condIH middle (.val values) ⟨condRun, absent, by simp⟩
        have targetBranch := branchIH middle (.val values) values branch ⟨condRun, rfl, chosen⟩ s' res
          ⟨run, targetCond.1, safe⟩
        refine ⟨targetBranch.1, ?_⟩
        rw [evaluate, (fixClockEvaluate _ _ [cond] []).1, targetCond.2]
        dsimp only
        split
        next failed => rw [chosen] at failed; contradiction
        next selected selectedEq =>
          have equal : selected = branch := Option.some.inj (selectedEq.symm.trans chosen)
          subst selected
          exact targetBranch.2

/-- The match-expression induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Mat {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (expr : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp))
    (ih : (∀ middle outcome values, evaluate s env [expr] = (middle, outcome) ∧
      outcome = .val values ∧ canPmatchAll env.c middle.refs (rows.map Prod.fst) (headValue values) = true →
      NoEvalMatchAt es middle env (headValue values) rows bindExnV) ∧ NoEvalExpsAt es s env [expr]) :
    NoEvalExpsAt es s env [.mat expr rows] := by
  obtain ⟨matchIH, exprIH⟩ := ih
  intro s' res ⟨run, absent, safe⟩
  rw [evaluate, (fixClockEvaluate s env [expr] []).1] at run
  cases exprRun : evaluate s env [expr] with
  | mk middle result =>
    cases result with
    | err error =>
      simp only [exprRun] at run
      cases run
      have target := exprIH s' (.err error) ⟨exprRun, absent, safe⟩
      refine ⟨target.1, ?_⟩
      rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, target.2]
    | val values =>
      simp only [exprRun] at run
      by_cases check : canPmatchAll env.c middle.refs (rows.map Prod.fst) (headValue values) = true
      · simp only [check, ↓reduceIte] at run
        have targetExpr := exprIH middle (.val values) ⟨exprRun, absent, by simp⟩
        have targetMatch := matchIH middle (.val values) values ⟨exprRun, rfl, check⟩ s' res
          ⟨run, targetExpr.1, safe⟩
        refine ⟨targetMatch.1, ?_⟩
        rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, targetExpr.2]
        simpa [check] using targetMatch.2
      · simp [check, typeError] at run
        obtain ⟨_, rfl⟩ := run
        exact (safe rfl).elim

/-- The exception-handler induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Handle {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (expr : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp))
    (ih : (∀ middle outcome err value, evaluate s env [expr] = (middle, outcome) ∧
      outcome = .err err ∧ err = .raise value ∧
      canPmatchAll env.c middle.refs (rows.map Prod.fst) value = true →
      NoEvalMatchAt es middle env value rows value) ∧ NoEvalExpsAt es s env [expr]) :
    NoEvalExpsAt es s env [.handle expr rows] := by
  obtain ⟨matchIH, exprIH⟩ := ih
  intro s' res ⟨run, absent, safe⟩
  rw [evaluate, (fixClockEvaluate s env [expr] []).1] at run
  cases exprRun : evaluate s env [expr] with
  | mk middle result =>
    cases result with
    | val values =>
      simp only [exprRun] at run
      cases run
      have target := exprIH s' (.val values) ⟨exprRun, absent, by simp⟩
      refine ⟨target.1, ?_⟩
      rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, target.2]
    | err error =>
      cases error with
      | abort error =>
        simp only [exprRun] at run
        cases run
        have target := exprIH s' (.err (.abort error)) ⟨exprRun, absent, safe⟩
        refine ⟨target.1, ?_⟩
        rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, target.2]
      | raise value =>
        simp only [exprRun] at run
        by_cases check : canPmatchAll env.c middle.refs (rows.map Prod.fst) value = true
        · simp only [check, ↓reduceIte] at run
          have targetExpr := exprIH middle (.err (.raise value)) ⟨exprRun, absent, by simp⟩
          have targetMatch := matchIH middle (.err (.raise value)) (.raise value) value
            ⟨exprRun, rfl, rfl, check⟩ s' res ⟨run, targetExpr.1, safe⟩
          refine ⟨targetMatch.1, ?_⟩
          rw [evaluate, (fixClockEvaluate _ _ [expr] []).1, targetExpr.2]
          simpa [check] using targetMatch.2
        · simp [check, typeError] at run
          obtain ⟨_, rfl⟩ := run
          exact (safe rfl).elim
/-- The short-circuit induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_Log {F : Type} (es : Option EvalState) (s : State F) (env : SemEnv Value)
    (op : Lop) (first second : AstHOL.Exp)
    (ih : (∀ middle outcome values selection branch, evaluate s env [first] = (middle, outcome) ∧
      outcome = .val values ∧ doLog op (headValue values) second = some selection ∧ selection = .exp branch →
      NoEvalExpsAt es middle env [branch]) ∧ NoEvalExpsAt es s env [first]) :
    NoEvalExpsAt es s env [.log op first second] := by
  obtain ⟨branchIH, firstIH⟩ := ih
  intro s' res ⟨run, absent, safe⟩
  rw [evaluate, (fixClockEvaluate s env [first] []).1] at run
  cases firstRun : evaluate s env [first] with
  | mk middle result =>
    cases result with
    | err error =>
      simp only [firstRun] at run
      cases run
      have target := firstIH s' (.err error) ⟨firstRun, absent, safe⟩
      refine ⟨target.1, ?_⟩
      rw [evaluate, (fixClockEvaluate _ _ [first] []).1, target.2]
    | val values =>
      simp only [firstRun] at run
      split at run
      next _ =>
        simp [typeError] at run
        obtain ⟨_, rfl⟩ := run
        exact (safe rfl).elim
      next value chosen =>
        cases run
        have target := firstIH s' (.val values) ⟨firstRun, absent, by simp⟩
        refine ⟨target.1, ?_⟩
        rw [evaluate, (fixClockEvaluate _ _ [first] []).1, target.2]
        dsimp only
        split
        next failed => rw [chosen] at failed; contradiction
        next selected selectedEq =>
          have equal := Option.some.inj (selectedEq.symm.trans chosen)
          cases equal
          rfl
        next selected selectedEq =>
          have equal := Option.some.inj (selectedEq.symm.trans chosen)
          cases equal
      next branch chosen =>
        have targetFirst := firstIH middle (.val values) ⟨firstRun, absent, by simp⟩
        have targetBranch := branchIH middle (.val values) values (.exp branch) branch
          ⟨firstRun, rfl, chosen, rfl⟩ s' res ⟨run, targetFirst.1, safe⟩
        refine ⟨targetBranch.1, ?_⟩
        rw [evaluate, (fixClockEvaluate _ _ [first] []).1, targetFirst.2]
        dsimp only
        split
        next failed => rw [chosen] at failed; contradiction
        next selected selectedEq =>
          have equal := Option.some.inj (selectedEq.symm.trans chosen)
          cases equal
        next selected selectedEq =>
          have equal := Option.some.inj (selectedEq.symm.trans chosen)
          cases equal
          exact targetBranch.2
end Flapjack.EvaluateProps

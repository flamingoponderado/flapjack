module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.InsertCorrectBase

@[expose] public section

/-! Branching-expression cases of source oracle insertion correctness. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- The let-expression case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Let {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (name : Option VarN) (bound body : AstHOL.Exp)
    (ih : (∀ middle outcome values, evaluate s env [bound] = (middle, outcome) ∧ outcome = .val values →
      ExpsInsertAt ci oracle middle { env with v := nsOptBind name (headValue values) env.v } [body]) ∧
      ExpsInsertAt ci oracle s env [bound]) : ExpsInsertAt ci oracle s env [.let_ name bound body] := by
  obtain ⟨bodyIH, boundIH⟩ := ih
  intro s' res ⟨run, recorded, agrees, wf, safe⟩
  rw [evaluate, (fixClockEvaluate s env [bound] []).1] at run
  cases boundRun : evaluate s env [bound] with
  | mk middle result =>
    cases result with
    | err error =>
      simp only [boundRun] at run
      cases run
      have target := boundIH s' (.err error) ⟨boundRun, recorded, agrees, wf, safe⟩
      rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env [bound] []).1, target]
    | val values =>
      simp only [boundRun] at run
      have firstRecorded := (evaluate_is_record_forward ci).1 s env [bound] middle (.val values)
        ⟨boundRun, recorded⟩
      have lastRecorded := (evaluate_is_record_forward ci).1 middle
        { env with v := nsOptBind name (headValue values) env.v } [body] s' res ⟨run, firstRecorded.1⟩
      have agreesMiddle := oracleAgrees_backward oracle s'.evalState middle.evalState ⟨agrees, lastRecorded.2.1⟩
      have targetBound := boundIH middle (.val values) ⟨boundRun, recorded, agreesMiddle, wf, by simp⟩
      have targetBody := bodyIH middle (.val values) values ⟨boundRun, rfl⟩ s' res
        ⟨run, firstRecorded.1, agrees, wf, safe⟩
      rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env [bound] []).1, targetBound]
      exact targetBody
/-- The conditional-expression case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_If {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (cond yes no : AstHOL.Exp)
    (ih : (∀ middle outcome values branch, evaluate s env [cond] = (middle, outcome) ∧
      outcome = .val values ∧ doIf (headValue values) yes no = some branch →
      ExpsInsertAt ci oracle middle env [branch]) ∧ ExpsInsertAt ci oracle s env [cond]) :
    ExpsInsertAt ci oracle s env [.if_ cond yes no] := by
  obtain ⟨branchIH, condIH⟩ := ih
  intro s' res ⟨run, recorded, agrees, wf, safe⟩
  rw [evaluate, (fixClockEvaluate s env [cond] []).1] at run
  cases condRun : evaluate s env [cond] with
  | mk middle result =>
    cases result with
    | err error =>
      simp only [condRun] at run
      cases run
      have target := condIH s' (.err error) ⟨condRun, recorded, agrees, wf, safe⟩
      rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env [cond] []).1, target]
    | val values =>
      simp only [condRun] at run
      split at run
      next _ =>
        simp [typeError] at run
        obtain ⟨_, rfl⟩ := run
        exact (safe rfl).elim
      next branch chosen =>
        have firstRecorded := (evaluate_is_record_forward ci).1 s env [cond] middle (.val values)
          ⟨condRun, recorded⟩
        have lastRecorded := (evaluate_is_record_forward ci).1 middle env [branch] s' res ⟨run, firstRecorded.1⟩
        have agreesMiddle := oracleAgrees_backward oracle s'.evalState middle.evalState ⟨agrees, lastRecorded.2.1⟩
        have targetCond := condIH middle (.val values) ⟨condRun, recorded, agreesMiddle, wf, by simp⟩
        have targetBranch := branchIH middle (.val values) values branch ⟨condRun, rfl, chosen⟩ s' res
          ⟨run, firstRecorded.1, agrees, wf, safe⟩
        rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env [cond] []).1, targetCond]
        dsimp only
        split
        next failed => rw [chosen] at failed; contradiction
        next selected selectedEq =>
          have equal : selected = branch := Option.some.inj (selectedEq.symm.trans chosen)
          subst selected
          exact targetBranch
/-- The short-circuit expression case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Log {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (op : Lop) (first second : AstHOL.Exp)
    (ih : (∀ middle outcome values selection branch, evaluate s env [first] = (middle, outcome) ∧
      outcome = .val values ∧ doLog op (headValue values) second = some selection ∧ selection = .exp branch →
      ExpsInsertAt ci oracle middle env [branch]) ∧ ExpsInsertAt ci oracle s env [first]) :
    ExpsInsertAt ci oracle s env [.log op first second] := by
  obtain ⟨branchIH, firstIH⟩ := ih
  intro s' res ⟨run, recorded, agrees, wf, safe⟩
  rw [evaluate, (fixClockEvaluate s env [first] []).1] at run
  cases firstRun : evaluate s env [first] with
  | mk middle result =>
    cases result with
    | err error =>
      simp only [firstRun] at run
      cases run
      have target := firstIH s' (.err error) ⟨firstRun, recorded, agrees, wf, safe⟩
      rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env [first] []).1, target]
    | val values =>
      simp only [firstRun] at run
      split at run
      next _ =>
        simp [typeError] at run
        obtain ⟨_, rfl⟩ := run
        exact (safe rfl).elim
      next value chosen =>
        cases run
        have target := firstIH s' (.val values) ⟨firstRun, recorded, agrees, wf, by simp⟩
        rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env [first] []).1, target]
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
        have firstRecorded := (evaluate_is_record_forward ci).1 s env [first] middle (.val values)
          ⟨firstRun, recorded⟩
        have lastRecorded := (evaluate_is_record_forward ci).1 middle env [branch] s' res ⟨run, firstRecorded.1⟩
        have agreesMiddle := oracleAgrees_backward oracle s'.evalState middle.evalState ⟨agrees, lastRecorded.2.1⟩
        have targetFirst := firstIH middle (.val values) ⟨firstRun, recorded, agreesMiddle, wf, by simp⟩
        have targetBranch := branchIH middle (.val values) values (.exp branch) branch
          ⟨firstRun, rfl, chosen, rfl⟩ s' res ⟨run, firstRecorded.1, agrees, wf, safe⟩
        rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env [first] []).1, targetFirst]
        dsimp only
        split
        next failed => rw [chosen] at failed; contradiction
        next selected selectedEq =>
          have equal := Option.some.inj (selectedEq.symm.trans chosen)
          cases equal
        next selected selectedEq =>
          have equal := Option.some.inj (selectedEq.symm.trans chosen)
          cases equal
          exact targetBranch
/-- The match-expression case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Mat {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (expr : AstHOL.Exp)
    (rows : List (Pat × AstHOL.Exp))
    (ih : (∀ middle outcome values, evaluate s env [expr] = (middle, outcome) ∧
      outcome = .val values ∧ canPmatchAll env.c middle.refs (rows.map Prod.fst) (headValue values) = true →
      MatchInsertAt ci oracle middle env (headValue values) rows bindExnV) ∧ ExpsInsertAt ci oracle s env [expr]) :
    ExpsInsertAt ci oracle s env [.mat expr rows] := by
  obtain ⟨matchIH, exprIH⟩ := ih
  intro s' res ⟨run, recorded, agrees, wf, safe⟩
  rw [evaluate, (fixClockEvaluate s env [expr] []).1] at run
  cases exprRun : evaluate s env [expr] with
  | mk middle result =>
    cases result with
    | err error =>
      simp only [exprRun] at run
      cases run
      have target := exprIH s' (.err error) ⟨exprRun, recorded, agrees, wf, safe⟩
      rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env [expr] []).1, target]
    | val values =>
      simp only [exprRun] at run
      by_cases check : canPmatchAll env.c middle.refs (rows.map Prod.fst) (headValue values) = true
      · simp only [check, ↓reduceIte] at run
        have firstRecorded := (evaluate_is_record_forward ci).1 s env [expr] middle (.val values)
          ⟨exprRun, recorded⟩
        have lastRecorded := (evaluate_is_record_forward ci).2.1 middle env (headValue values) rows bindExnV
          s' res ⟨run, firstRecorded.1⟩
        have agreesMiddle := oracleAgrees_backward oracle s'.evalState middle.evalState ⟨agrees, lastRecorded.2.1⟩
        have targetExpr := exprIH middle (.val values) ⟨exprRun, recorded, agreesMiddle, wf, by simp⟩
        have targetMatch := matchIH middle (.val values) values ⟨exprRun, rfl, check⟩ s' res
          ⟨run, firstRecorded.1, agrees, wf, safe⟩
        rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env [expr] []).1, targetExpr]
        simpa [insertOracleState, check] using targetMatch
      · simp [check, typeError] at run
        obtain ⟨_, rfl⟩ := run
        exact (safe rfl).elim
/-- The exception-handler case of oracle insertion correctness. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_Handle {Config F : Type} (ci : CompilerInstance Config)
    (oracle : EvalOracleFun) (s : State F) (env : SemEnv Value) (expr : AstHOL.Exp)
    (rows : List (Pat × AstHOL.Exp))
    (ih : (∀ middle outcome err value, evaluate s env [expr] = (middle, outcome) ∧
      outcome = .err err ∧ err = .raise value ∧
      canPmatchAll env.c middle.refs (rows.map Prod.fst) value = true →
      MatchInsertAt ci oracle middle env value rows value) ∧ ExpsInsertAt ci oracle s env [expr]) :
    ExpsInsertAt ci oracle s env [.handle expr rows] := by
  obtain ⟨matchIH, exprIH⟩ := ih
  intro s' res ⟨run, recorded, agrees, wf, safe⟩
  rw [evaluate, (fixClockEvaluate s env [expr] []).1] at run
  cases exprRun : evaluate s env [expr] with
  | mk middle result =>
    cases result with
    | val values =>
      simp only [exprRun] at run
      cases run
      have target := exprIH s' (.val values) ⟨exprRun, recorded, agrees, wf, by simp⟩
      rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env [expr] []).1, target]
    | err error =>
      cases error with
      | abort error =>
        simp only [exprRun] at run
        cases run
        have target := exprIH s' (.err (.abort error)) ⟨exprRun, recorded, agrees, wf, safe⟩
        rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env [expr] []).1, target]
      | raise value =>
        simp only [exprRun] at run
        by_cases check : canPmatchAll env.c middle.refs (rows.map Prod.fst) value = true
        · simp only [check, ↓reduceIte] at run
          have firstRecorded := (evaluate_is_record_forward ci).1 s env [expr] middle (.err (.raise value))
            ⟨exprRun, recorded⟩
          have lastRecorded := (evaluate_is_record_forward ci).2.1 middle env value rows value s' res
            ⟨run, firstRecorded.1⟩
          have agreesMiddle := oracleAgrees_backward oracle s'.evalState middle.evalState ⟨agrees, lastRecorded.2.1⟩
          have targetExpr := exprIH middle (.err (.raise value)) ⟨exprRun, recorded, agreesMiddle, wf, by simp⟩
          have targetMatch := matchIH middle (.err (.raise value)) (.raise value) value
            ⟨exprRun, rfl, rfl, check⟩ s' res ⟨run, firstRecorded.1, agrees, wf, safe⟩
          rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env [expr] []).1, targetExpr]
          simpa [insertOracleState, check] using targetMatch
        · simp [check, typeError] at run
          obtain ⟨_, rfl⟩ := run
          exact (safe rfl).elim
end Flapjack.Compiler.Backend.SourceEval.Proofs

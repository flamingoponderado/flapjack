import Flapjack.Compiler.Backend.SourceEval.Proofs.EvaluateApp
import Flapjack.Compiler.Backend.SourceEval.Proofs.EvaluateMatch

/-! Mutual lexicographic induction for source evaluator oracle adjustment. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL Flapjack.NamespaceHOL

mutual
/-- Expression part of the oracle-adjusted evaluator induction. -/
theorem evaluateOracleFull {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (preserves : DeclarationCompilerPreserves (F := F) compile)
    (state : State F) (env : SemEnv Value) (exprs : List AstHOL.Exp) :
    ExpsOracleAdjustedAt ci f compile state env exprs := by
  intro next result run inserted safe
  cases exprs with
  | nil => exact adjustOracle_evaluate_ExpsNil ci f compile preserves state next env result run inserted safe
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply adjustOracle_evaluate_ExpsCons ci f compile preserves first second tail state next env ?_ ?_ result run inserted safe
      · exact evaluateOracleFull ci f compile preserves state env [first]
      · intro middle values firstRun
        have bound := evaluateClockFull state middle env [first] (.val values) firstRun
        exact evaluateOracleFull ci f compile preserves middle env (second :: tail)
    | nil =>
      cases first with
      | lit lit => exact adjustOracle_evaluate_Lit ci f compile preserves lit state next env result run inserted safe
      | var name => exact adjustOracle_evaluate_Var ci f compile preserves state next env name result run inserted safe
      | fn name body => exact adjustOracle_evaluate_Fn ci f compile preserves name body state next env result run inserted safe
      | raise expr =>
        exact adjustOracle_evaluate_Raise ci f compile preserves expr state next env
          (evaluateOracleFull ci f compile preserves state env [expr]) result run inserted safe
      | tannot expr typ =>
        exact adjustOracle_evaluate_Tannot ci f compile preserves expr typ state next env
          (evaluateOracleFull ci f compile preserves state env [expr]) result run inserted safe
      | lannot expr loc =>
        exact adjustOracle_evaluate_Lannot ci f compile preserves expr loc state next env
          (evaluateOracleFull ci f compile preserves state env [expr]) result run inserted safe
      | con name args =>
        apply adjustOracle_evaluate_Con ci f compile preserves name args state next env ?_ result run inserted safe
        intro _
        exact evaluateOracleFull ci f compile preserves state env args.reverse
      | letrec funs body =>
        apply adjustOracle_evaluate_Letrec ci f compile preserves state next env funs body ?_ result run inserted safe
        intro _
        exact evaluateOracleFull ci f compile preserves state { env with v := buildRecEnv funs env env.v } [body]
      | let_ name bound body =>
        apply adjustOracle_evaluate_Let ci f compile preserves name bound body state next env ?_ ?_ result run inserted safe
        · exact evaluateOracleFull ci f compile preserves state env [bound]
        · intro middle values boundRun
          have clockBound := evaluateClockFull state middle env [bound] (.val values) boundRun
          exact evaluateOracleFull ci f compile preserves middle { env with v := nsOptBind name (headValue values) env.v } [body]
      | if_ condition yes no =>
        apply adjustOracle_evaluate_If ci f compile preserves condition yes no state next env ?_ ?_ result run inserted safe
        · exact evaluateOracleFull ci f compile preserves state env [condition]
        · intro middle values branch conditionRun chosen
          have clockBound := evaluateClockFull state middle env [condition] (.val values) conditionRun
          rcases doIf_selected (headValue values) yes no branch chosen with equal | equal
          · subst branch
            exact evaluateOracleFull ci f compile preserves middle env [yes]
          · subst branch
            exact evaluateOracleFull ci f compile preserves middle env [no]
      | log op first second =>
        apply adjustOracle_evaluate_Log ci f compile preserves op first second state next env ?_ ?_ result run inserted safe
        · exact evaluateOracleFull ci f compile preserves state env [first]
        · intro middle values branch firstRun chosen
          have clockBound := evaluateClockFull state middle env [first] (.val values) firstRun
          have equal := doLog_selected op (headValue values) second branch chosen
          subst branch
          exact evaluateOracleFull ci f compile preserves middle env [second]
      | mat expr clauses =>
        apply adjustOracle_evaluate_Mat ci f compile preserves expr clauses state next env ?_ ?_ result run inserted safe
        · exact evaluateOracleFull ci f compile preserves state env [expr]
        · intro middle values exprRun _
          have clockBound := evaluateClockFull state middle env [expr] (.val values) exprRun
          exact evaluateMatchOracleFull ci f compile preserves middle env (headValue values) clauses bindExnV
      | handle expr clauses =>
        apply adjustOracle_evaluate_Handle ci f compile preserves expr clauses state next env ?_ ?_ result run inserted safe
        · exact evaluateOracleFull ci f compile preserves state env [expr]
        · intro middle value exprRun _
          have clockBound := evaluateClockFull state middle env [expr] (.err (.raise value)) exprRun
          exact evaluateMatchOracleFull ci f compile preserves middle env value clauses value
      | app op args =>
        apply adjustOracle_evaluate_App ci f compile preserves state next env op args ?_ ?_ ?_ ?_ result run inserted safe
        · exact evaluateOracleFull ci f compile preserves state env args.reverse
        · intro _ middle values callEnv body argsRun _ nonzero
          have clockBound := evaluateClockFull state middle env args.reverse (.val values) argsRun
          exact evaluateOracleFull ci f compile preserves (decClock middle) callEnv [body]
        · intro _ middle values thunk callEnv body argsRun _ _ nonzero
          have clockBound := evaluateClockFull state middle env args.reverse (.val values) argsRun
          exact evaluateOracleFull ci f compile preserves (decClock middle) callEnv [body]
        · intro _ middle decoded values evalEnv decs argsRun decodedRun nonzero
          have clockBound := evaluateClockFull state middle env args.reverse (.val values) argsRun
          have clockEq : decoded.clock = middle.clock := by
            have hclock := congrArg (fun pair => pair.1.clock) decodedRun
            have hc := doEvalRes_clock values.reverse middle (β := Value)
            exact hclock.symm.trans hc
          exact evaluateDecsOracleFull ci f compile preserves (decClock decoded) evalEnv decs
termination_by (state.clock, sizeOf exprs)
decreasing_by
  all_goals try subst_vars
  all_goals simp_wf
  all_goals try simp only [listSize_reverse]
  all_goals try simp only [Prod.lex_def, decClock]
  all_goals try (have := expSize_pos second)
  all_goals try (have := listSize_pos tail)
  all_goals try dsimp only [decClock] at *
  all_goals try simp only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega

/-- Pattern-match part of the oracle-adjusted evaluator induction. -/
theorem evaluateMatchOracleFull {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (preserves : DeclarationCompilerPreserves (F := F) compile)
    (state : State F) (env : SemEnv Value) (value : Value) (clauses : List (Pat × AstHOL.Exp)) (errValue : Value) :
    MatchOracleAdjustedAt ci f compile state env value clauses errValue := by
  intro next result run inserted safe
  cases clauses with
  | nil => exact adjustOracle_evaluate_MatchNil ci f compile preserves state next env value errValue result run inserted safe
  | cons clause rest =>
    cases clause with
    | mk pat expr =>
      apply adjustOracle_evaluate_MatchCons ci f compile preserves pat expr rest state next env value errValue ?_ ?_ result run inserted safe
      · intro bindings _ _
        exact evaluateOracleFull ci f compile preserves state { env with v := nsAppend (alistToNs bindings) env.v } [expr]
      · intro _ _
        exact evaluateMatchOracleFull ci f compile preserves state env value rest errValue
termination_by (state.clock, sizeOf clauses)
decreasing_by
  all_goals try subst_vars
  all_goals simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals try (have := patSize_pos pat)
  all_goals try (have := listSize_pos rest)
  all_goals try simp only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega

/-- Declaration part of the oracle-adjusted evaluator induction. -/
theorem evaluateDecsOracleFull {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (preserves : DeclarationCompilerPreserves (F := F) compile)
    (state : State F) (env : SemEnv Value) (decs : List Dec) :
    DecsOracleAdjustedAt ci f compile state env decs := by
  intro next result run inserted safe
  cases decs with
  | nil => exact adjustOracle_evaluate_DecsNil ci f compile preserves state next env result run inserted safe
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply adjustOracle_evaluate_DecsCons ci f compile preserves first second tail state next env ?_ ?_ result run inserted safe
      · exact evaluateDecsOracleFull ci f compile preserves state env [first]
      · intro middle inner firstRun
        have clockBound := evaluateDecsClockFull state middle env [first] (.val inner) firstRun
        exact evaluateDecsOracleFull ci f compile preserves middle (extendDecEnv inner env) (second :: tail)
    | nil =>
      cases first with
      | dtabbrev loc vars name typ => exact adjustOracle_evaluate_Dtabbrev ci f compile preserves state next env loc vars name typ result run inserted safe
      | dexn loc name types => exact adjustOracle_evaluate_Dexn ci f compile preserves state next env loc name types result run inserted safe
      | dtype loc types => exact adjustOracle_evaluate_Dtype ci f compile preserves state next env loc types result run inserted safe
      | denv name => exact adjustOracle_evaluate_Denv ci f compile preserves state next env name result run inserted safe
      | dletrec loc funs => exact adjustOracle_evaluate_Dletrec ci f compile preserves state next env loc funs result run inserted safe
      | dmod name ds =>
        exact adjustOracle_evaluate_Dmod ci f compile preserves name ds state next env
          (evaluateDecsOracleFull ci f compile preserves state env ds) result run inserted safe
      | dlet loc pat expr =>
        apply adjustOracle_evaluate_Dlet ci f compile preserves loc pat expr state next env ?_ result run inserted safe
        intro _
        exact evaluateOracleFull ci f compile preserves state env [expr]
      | dlocal locals body =>
        apply adjustOracle_evaluate_Dlocal ci f compile preserves locals body state next env ?_ ?_ result run inserted safe
        · exact evaluateDecsOracleFull ci f compile preserves state env locals
        · intro middle inner firstRun
          have clockBound := evaluateDecsClockFull state middle env locals (.val inner) firstRun
          exact evaluateDecsOracleFull ci f compile preserves middle (extendDecEnv inner env) body
termination_by (state.clock, sizeOf decs)
decreasing_by
  all_goals try subst_vars
  all_goals simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals try (have := decSize_pos second)
  all_goals try (have := listSize_pos tail)
  all_goals try (have := patSize_pos pat)
  all_goals try simp only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega
end

/-- The three original evaluator simulations under oracle adjustment. Source
AST, evaluator and carrier correspondence remain pending review. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjust_oracle_evaluate {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (preserves : DeclarationCompilerPreserves (F := F) compile) :
    (∀ (state : State F) (env : SemEnv Value) (exprs : List AstHOL.Exp),
      ExpsOracleAdjustedAt ci f compile state env exprs) ∧
    (∀ (state : State F) (env : SemEnv Value) (value : Value) (clauses : List (Pat × AstHOL.Exp)) (errValue : Value),
      MatchOracleAdjustedAt ci f compile state env value clauses errValue) ∧
    (∀ (state : State F) (env : SemEnv Value) (decs : List Dec),
      DecsOracleAdjustedAt ci f compile state env decs) := by
  exact ⟨evaluateOracleFull ci f compile preserves, evaluateMatchOracleFull ci f compile preserves,
    evaluateDecsOracleFull ci f compile preserves⟩

/-- Oracle adjustment preserves program observations under the original
declaration-compiler preservation and non-failure hypotheses. Source and
carrier correspondence remain pending review. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_semantics_prog"]
theorem adjust_oracle_semantics_prog {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (preserves : DeclarationCompilerPreserves (F := F) compile)
    (state : State F) (env : SemEnv Value) (program : List Dec) (outcome : HolBehaviour)
    (inserted : isInsertOracle ci f state.evalState)
    (noFail : ¬ Flapjack.SemanticsHOL.semanticsProg state env program .fail)
    (source : Flapjack.SemanticsHOL.semanticsProg state env program outcome) :
    Flapjack.SemanticsHOL.semanticsProg
      { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env program outcome := by
  apply adjusted_semanticsProg_of_simulation ci f compile ?_ state env program outcome inserted noFail source
  intro s s' e ds r evaluation isInserted safe
  exact (evaluateDecsOracleFull ci f compile preserves s e ds s' r evaluation isInserted safe).2

end Flapjack.Compiler.Backend.SourceEval.Proofs

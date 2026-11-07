import Flapjack.Compiler.Backend.SourceEval.Proofs.InsertCorrectApp
import Flapjack.EvaluateHOL.Clock

/-! Complete mutual oracle insertion correctness for the source evaluator. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

mutual
/-- Flapjack infrastructure: expression component of the mutual induction. -/
private theorem expsInsertionFull {Config F : Type} (ci : CompilerInstance Config) (oracle : EvalOracleFun)
    (state : State F) (env : SemEnv Value) (exprs : List AstHOL.Exp) :
    ExpsInsertAt ci oracle state env exprs := by
  cases exprs with
  | nil => exact insertOracleCorrect_ExpsNil ci oracle state env
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply insertOracleCorrect_ExpsCons ci oracle state env first second tail
      refine ⟨?_, expsInsertionFull ci oracle state env [first]⟩
      intro middle outcome values ⟨run, rfl⟩
      have bound := evaluateClockFull state middle env [first] outcome run
      exact expsInsertionFull ci oracle middle env (second :: tail)
    | nil =>
      cases first with
      | lit lit => exact insertOracleCorrect_Lit ci oracle state env lit
      | var name => exact insertOracleCorrect_Var ci oracle state env name
      | fn name body => exact insertOracleCorrect_Fn ci oracle state env name body
      | raise expr => exact insertOracleCorrect_Raise ci oracle state env expr (expsInsertionFull ci oracle state env [expr])
      | tannot expr typ => exact insertOracleCorrect_Tannot ci oracle state env expr typ (expsInsertionFull ci oracle state env [expr])
      | lannot expr loc => exact insertOracleCorrect_Lannot ci oracle state env expr loc (expsInsertionFull ci oracle state env [expr])
      | con name args =>
        apply insertOracleCorrect_Con ci oracle state env name args
        intro _
        exact expsInsertionFull ci oracle state env args.reverse
      | letrec funs body =>
        apply insertOracleCorrect_Letrec ci oracle state env funs body
        intro _
        exact expsInsertionFull ci oracle state { env with v := buildRecEnv funs env env.v } [body]
      | let_ name bound body =>
        apply insertOracleCorrect_Let ci oracle state env name bound body
        refine ⟨?_, expsInsertionFull ci oracle state env [bound]⟩
        intro middle outcome values ⟨run, rfl⟩
        have clockBound := evaluateClockFull state middle env [bound] outcome run
        exact expsInsertionFull ci oracle middle { env with v := nsOptBind name (headValue values) env.v } [body]
      | if_ condition yes no =>
        apply insertOracleCorrect_If ci oracle state env condition yes no
        refine ⟨?_, expsInsertionFull ci oracle state env [condition]⟩
        intro middle outcome values branch ⟨run, rfl, chosen⟩
        have clockBound := evaluateClockFull state middle env [condition] outcome run
        rcases doIf_selected (headValue values) yes no branch chosen with equal | equal
        · subst branch; exact expsInsertionFull ci oracle middle env [yes]
        · subst branch; exact expsInsertionFull ci oracle middle env [no]
      | log op first second =>
        apply insertOracleCorrect_Log ci oracle state env op first second
        refine ⟨?_, expsInsertionFull ci oracle state env [first]⟩
        intro middle outcome values selection branch ⟨run, rfl, chosen, selectionEq⟩
        subst selection
        have clockBound := evaluateClockFull state middle env [first] outcome run
        have equal := doLog_selected op (headValue values) second branch chosen
        subst branch
        exact expsInsertionFull ci oracle middle env [second]
      | mat expr clauses =>
        apply insertOracleCorrect_Mat ci oracle state env expr clauses
        refine ⟨?_, expsInsertionFull ci oracle state env [expr]⟩
        intro middle outcome values ⟨run, rfl, _⟩
        have clockBound := evaluateClockFull state middle env [expr] outcome run
        exact matchInsertionFull ci oracle middle env (headValue values) clauses bindExnV
      | handle expr clauses =>
        apply insertOracleCorrect_Handle ci oracle state env expr clauses
        refine ⟨?_, expsInsertionFull ci oracle state env [expr]⟩
        intro middle outcome err value ⟨run, rfl, rfl, _⟩
        have clockBound := evaluateClockFull state middle env [expr] outcome run
        exact matchInsertionFull ci oracle middle env value clauses value
      | app op args =>
        apply insertOracleCorrect_App ci oracle state env op args
        refine ⟨?_, ?_, ?_, expsInsertionFull ci oracle state env args.reverse⟩
        · intro middle outcome values pair callEnv body ⟨run, rfl, _, _, rfl, nonzero⟩
          have clockBound := evaluateClockFull state middle env args.reverse outcome run
          exact expsInsertionFull ci oracle (decClock middle) callEnv [body]
        · intro middle outcome values decoded decodedResult pair evalEnv decs
            ⟨run, rfl, _, decodedRun, rfl, rfl, nonzero⟩
          have clockBound := evaluateClockFull state middle env args.reverse outcome run
          have clockEq : decoded.clock = middle.clock := by
            have hclock := congrArg (fun pair => pair.1.clock) decodedRun
            have hc := doEvalRes_clock values.reverse middle (β := Value)
            exact hclock.symm.trans hc
          exact decsInsertionFull ci oracle (decClock decoded) evalEnv decs
        · intro middle outcome values mode thunk pair callEnv body ⟨run, rfl, _, _, rfl, _, rfl, nonzero⟩
          have clockBound := evaluateClockFull state middle env args.reverse outcome run
          exact expsInsertionFull ci oracle (decClock middle) callEnv [body]
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

/-- Flapjack infrastructure: matching component of the mutual induction. -/
private theorem matchInsertionFull {Config F : Type} (ci : CompilerInstance Config) (oracle : EvalOracleFun)
    (state : State F) (env : SemEnv Value) (value : Value) (clauses : List (Pat × AstHOL.Exp)) (err : Value) :
    MatchInsertAt ci oracle state env value clauses err := by
  cases clauses with
  | nil => exact insertOracleCorrect_MatchNil ci oracle state env value err
  | cons clause rest =>
    obtain ⟨pat, expr⟩ := clause
    apply insertOracleCorrect_MatchCons ci oracle state env value pat expr rest err
    constructor
    · intro bindings _
      exact expsInsertionFull ci oracle state { env with v := nsAppend (alistToNs bindings) env.v } [expr]
    · intro _
      exact matchInsertionFull ci oracle state env value rest err
termination_by (state.clock, sizeOf clauses)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals try (have := patSize_pos pat)
  all_goals try (have := listSize_pos rest)
  all_goals try simp only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega

/-- Flapjack infrastructure: declaration component of the mutual induction. -/
private theorem decsInsertionFull {Config F : Type} (ci : CompilerInstance Config) (oracle : EvalOracleFun)
    (state : State F) (env : SemEnv Value) (decs : List Dec) : DecsInsertAt ci oracle state env decs := by
  cases decs with
  | nil => exact insertOracleCorrect_DecsNil ci oracle state env
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply insertOracleCorrect_DecsCons ci oracle state env first second tail
      refine ⟨?_, decsInsertionFull ci oracle state env [first]⟩
      intro middle outcome inner ⟨run, rfl⟩
      have clockBound := evaluateDecsClockFull state middle env [first] outcome run
      exact decsInsertionFull ci oracle middle (extendDecEnv inner env) (second :: tail)
    | nil =>
      cases first with
      | dtabbrev loc vars name typ => exact insertOracleCorrect_Dtabbrev ci oracle state env loc vars name typ
      | dexn loc name types => exact insertOracleCorrect_Dexn ci oracle state env loc name types
      | dtype loc types => exact insertOracleCorrect_Dtype ci oracle state env loc types
      | denv name => exact insertOracleCorrect_Denv ci oracle state env name
      | dletrec loc funs => exact insertOracleCorrect_Dletrec ci oracle state env loc funs
      | dmod name ds => exact insertOracleCorrect_Dmod ci oracle state env name ds (decsInsertionFull ci oracle state env ds)
      | dlet loc pat expr =>
        apply insertOracleCorrect_Dlet ci oracle state env loc pat expr
        intro _
        exact expsInsertionFull ci oracle state env [expr]
      | dlocal locals body =>
        apply insertOracleCorrect_Dlocal ci oracle state env locals body
        refine ⟨?_, decsInsertionFull ci oracle state env locals⟩
        intro middle outcome inner ⟨run, rfl⟩
        have clockBound := evaluateDecsClockFull state middle env locals outcome run
        exact decsInsertionFull ci oracle middle (extendDecEnv inner env) body
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


/-- Inserting an agreeing, well-formed oracle preserves all three source evaluator
results except type errors. The evaluator inherits the rational-cut real assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insert_oracle_correct {Config F : Type} (ci : CompilerInstance Config) (oracle : EvalOracleFun) :
    (∀ (s : State F) (env : SemEnv Value) (exps : List AstHOL.Exp)
      (s' : State F) (res : Result (List Value) Value),
      evaluate s env exps = (s', res) ∧ isRecord ci s.evalState ∧ oracleAgrees oracle s'.evalState ∧
        oracleExtendedWellFormed (mkCompilerFunFromCi ci) oracle ∧ res ≠ .err (.abort .typeError) →
      evaluate { s with evalState := insertGenOracle ci id (fun args => args.1.1) oracle s.evalState } env exps =
        ({ s' with evalState := insertGenOracle ci id (fun args => args.1.1) oracle s'.evalState }, res)) ∧
    (∀ (s : State F) (env : SemEnv Value) (x : Value) (rows : List (Pat × AstHOL.Exp)) (err : Value)
      (s' : State F) (res : Result (List Value) Value),
      evaluateMatch s env x rows err = (s', res) ∧ isRecord ci s.evalState ∧ oracleAgrees oracle s'.evalState ∧
        oracleExtendedWellFormed (mkCompilerFunFromCi ci) oracle ∧ res ≠ .err (.abort .typeError) →
      evaluateMatch { s with evalState := insertGenOracle ci id (fun args => args.1.1) oracle s.evalState } env x rows err =
        ({ s' with evalState := insertGenOracle ci id (fun args => args.1.1) oracle s'.evalState }, res)) ∧
    (∀ (s : State F) (env : SemEnv Value) (decs : List Dec)
      (s' : State F) (res : Result (SemEnv Value) Value),
      evaluateDecs s env decs = (s', res) ∧ isRecord ci s.evalState ∧ oracleAgrees oracle s'.evalState ∧
        oracleExtendedWellFormed (mkCompilerFunFromCi ci) oracle ∧ res ≠ .err (.abort .typeError) →
      evaluateDecs { s with evalState := insertGenOracle ci id (fun args => args.1.1) oracle s.evalState } env decs =
        ({ s' with evalState := insertGenOracle ci id (fun args => args.1.1) oracle s'.evalState }, res)) := by
  exact ⟨fun s env exps => expsInsertionFull ci oracle s env exps,
    fun s env x rows err => matchInsertionFull ci oracle s env x rows err,
    fun s env decs => decsInsertionFull ci oracle s env decs⟩
end Flapjack.Compiler.Backend.SourceEval.Proofs

import Flapjack.Compiler.Backend.SourceEval.Proofs.RecordForwardApp
import Flapjack.EvaluateHOL.Clock

/-! Complete mutual recording-state preservation for the source evaluator. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

mutual
/-- Flapjack infrastructure: expression component of the mutual induction. -/
private theorem expsRecordingFull {Config F : Type} (ci : CompilerInstance Config)
    (state : State F) (env : SemEnv Value) (exprs : List AstHOL.Exp) :
    ExpsRecordAt ci state env exprs := by
  cases exprs with
  | nil => exact evaluateIsRecordForward_ExpsNil ci state env
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply evaluateIsRecordForward_ExpsCons ci state env first second tail
      refine ⟨?_, expsRecordingFull ci state env [first]⟩
      intro middle outcome values ⟨run, rfl⟩
      have bound := evaluateClockFull state middle env [first] outcome run
      exact expsRecordingFull ci middle env (second :: tail)
    | nil =>
      cases first with
      | lit lit => exact evaluateIsRecordForward_Lit ci state env lit
      | var name => exact evaluateIsRecordForward_Var ci state env name
      | fn name body => exact evaluateIsRecordForward_Fn ci state env name body
      | raise expr => exact evaluateIsRecordForward_Raise ci state env expr (expsRecordingFull ci state env [expr])
      | tannot expr typ => exact evaluateIsRecordForward_Tannot ci state env expr typ (expsRecordingFull ci state env [expr])
      | lannot expr loc => exact evaluateIsRecordForward_Lannot ci state env expr loc (expsRecordingFull ci state env [expr])
      | con name args =>
        apply evaluateIsRecordForward_Con ci state env name args
        intro _
        exact expsRecordingFull ci state env args.reverse
      | letrec funs body =>
        apply evaluateIsRecordForward_Letrec ci state env funs body
        intro _
        exact expsRecordingFull ci state { env with v := buildRecEnv funs env env.v } [body]
      | let_ name bound body =>
        apply evaluateIsRecordForward_Let ci state env name bound body
        refine ⟨?_, expsRecordingFull ci state env [bound]⟩
        intro middle outcome values ⟨run, rfl⟩
        have clockBound := evaluateClockFull state middle env [bound] outcome run
        exact expsRecordingFull ci middle { env with v := nsOptBind name (headValue values) env.v } [body]
      | if_ condition yes no =>
        apply evaluateIsRecordForward_If ci state env condition yes no
        refine ⟨?_, expsRecordingFull ci state env [condition]⟩
        intro middle outcome values branch ⟨run, rfl, chosen⟩
        have clockBound := evaluateClockFull state middle env [condition] outcome run
        rcases doIf_selected (headValue values) yes no branch chosen with equal | equal
        · subst branch; exact expsRecordingFull ci middle env [yes]
        · subst branch; exact expsRecordingFull ci middle env [no]
      | log op first second =>
        apply evaluateIsRecordForward_Log ci state env op first second
        refine ⟨?_, expsRecordingFull ci state env [first]⟩
        intro middle outcome values selection branch ⟨run, rfl, chosen, selectionEq⟩
        subst selection
        have clockBound := evaluateClockFull state middle env [first] outcome run
        have equal := doLog_selected op (headValue values) second branch chosen
        subst branch
        exact expsRecordingFull ci middle env [second]
      | mat expr clauses =>
        apply evaluateIsRecordForward_Mat ci state env expr clauses
        refine ⟨?_, expsRecordingFull ci state env [expr]⟩
        intro middle outcome values ⟨run, rfl, _⟩
        have clockBound := evaluateClockFull state middle env [expr] outcome run
        exact matchRecordingFull ci middle env (headValue values) clauses bindExnV
      | handle expr clauses =>
        apply evaluateIsRecordForward_Handle ci state env expr clauses
        refine ⟨?_, expsRecordingFull ci state env [expr]⟩
        intro middle outcome err value ⟨run, rfl, rfl, _⟩
        have clockBound := evaluateClockFull state middle env [expr] outcome run
        exact matchRecordingFull ci middle env value clauses value
      | app op args =>
        apply evaluateIsRecordForward_App ci state env op args
        refine ⟨?_, ?_, ?_, expsRecordingFull ci state env args.reverse⟩
        · intro middle outcome values pair callEnv body ⟨run, rfl, _, _, rfl, nonzero⟩
          have clockBound := evaluateClockFull state middle env args.reverse outcome run
          exact expsRecordingFull ci (decClock middle) callEnv [body]
        · intro middle outcome values decoded decodedResult pair evalEnv decs
            ⟨run, rfl, _, decodedRun, rfl, rfl, nonzero⟩
          have clockBound := evaluateClockFull state middle env args.reverse outcome run
          have clockEq : decoded.clock = middle.clock := by
            have hclock := congrArg (fun pair => pair.1.clock) decodedRun
            have hc := doEvalRes_clock values.reverse middle (β := Value)
            exact hclock.symm.trans hc
          exact decsRecordingFull ci (decClock decoded) evalEnv decs
        · intro middle outcome values mode thunk pair callEnv body ⟨run, rfl, _, _, rfl, _, rfl, nonzero⟩
          have clockBound := evaluateClockFull state middle env args.reverse outcome run
          exact expsRecordingFull ci (decClock middle) callEnv [body]
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
private theorem matchRecordingFull {Config F : Type} (ci : CompilerInstance Config)
    (state : State F) (env : SemEnv Value) (value : Value) (clauses : List (Pat × AstHOL.Exp)) (err : Value) :
    MatchRecordAt ci state env value clauses err := by
  cases clauses with
  | nil => exact evaluateIsRecordForward_MatchNil ci state env value err
  | cons clause rest =>
    obtain ⟨pat, expr⟩ := clause
    apply evaluateIsRecordForward_MatchCons ci state env value pat expr rest err
    constructor
    · intro bindings _
      exact expsRecordingFull ci state { env with v := nsAppend (alistToNs bindings) env.v } [expr]
    · intro _
      exact matchRecordingFull ci state env value rest err
termination_by (state.clock, sizeOf clauses)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals try (have := patSize_pos pat)
  all_goals try (have := listSize_pos rest)
  all_goals try simp only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega

/-- Flapjack infrastructure: declaration component of the mutual induction. -/
private theorem decsRecordingFull {Config F : Type} (ci : CompilerInstance Config)
    (state : State F) (env : SemEnv Value) (decs : List Dec) : DecsRecordAt ci state env decs := by
  cases decs with
  | nil => exact evaluateIsRecordForward_DecsNil ci state env
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply evaluateIsRecordForward_DecsCons ci state env first second tail
      refine ⟨?_, decsRecordingFull ci state env [first]⟩
      intro middle outcome inner ⟨run, rfl⟩
      have clockBound := evaluateDecsClockFull state middle env [first] outcome run
      exact decsRecordingFull ci middle (extendDecEnv inner env) (second :: tail)
    | nil =>
      cases first with
      | dtabbrev loc vars name typ => exact evaluateIsRecordForward_Dtabbrev ci state env loc vars name typ
      | dexn loc name types => exact evaluateIsRecordForward_Dexn ci state env loc name types
      | dtype loc types => exact evaluateIsRecordForward_Dtype ci state env loc types
      | denv name => exact evaluateIsRecordForward_Denv ci state env name
      | dletrec loc funs => exact evaluateIsRecordForward_Dletrec ci state env loc funs
      | dmod name ds => exact evaluateIsRecordForward_Dmod ci state env name ds (decsRecordingFull ci state env ds)
      | dlet loc pat expr =>
        apply evaluateIsRecordForward_Dlet ci state env loc pat expr
        intro _
        exact expsRecordingFull ci state env [expr]
      | dlocal locals body =>
        apply evaluateIsRecordForward_Dlocal ci state env locals body
        refine ⟨?_, decsRecordingFull ci state env locals⟩
        intro middle outcome inner ⟨run, rfl⟩
        have clockBound := evaluateDecsClockFull state middle env locals outcome run
        exact decsRecordingFull ci middle (extendDecEnv inner env) body
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


/-- Source evaluation preserves recording state, extends the recorded oracle,
and preserves recorded-oracle well-formedness in all three evaluators. The
evaluator inherits the rational-cut real-number assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluate_is_record_forward {Config F : Type} (ci : CompilerInstance Config) :
    (∀ (s : State F) (env : SemEnv Value) (exps : List AstHOL.Exp)
      (s' : State F) (res : Result (List Value) Value),
      evaluate s env exps = (s', res) ∧ isRecord ci s.evalState →
      isRecord ci s'.evalState ∧ recordForward s.evalState s'.evalState ∧
      (recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState s.evalState).oracle →
        recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState s'.evalState).oracle)) ∧
    (∀ (s : State F) (env : SemEnv Value) (x : Value) (rows : List (Pat × AstHOL.Exp)) (err : Value)
      (s' : State F) (res : Result (List Value) Value),
      evaluateMatch s env x rows err = (s', res) ∧ isRecord ci s.evalState →
      isRecord ci s'.evalState ∧ recordForward s.evalState s'.evalState ∧
      (recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState s.evalState).oracle →
        recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState s'.evalState).oracle)) ∧
    (∀ (s : State F) (env : SemEnv Value) (decs : List Dec)
      (s' : State F) (res : Result (SemEnv Value) Value),
      evaluateDecs s env decs = (s', res) ∧ isRecord ci s.evalState →
      isRecord ci s'.evalState ∧ recordForward s.evalState s'.evalState ∧
      (recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState s.evalState).oracle →
        recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState s'.evalState).oracle)) := by
  exact ⟨fun s env exps => expsRecordingFull ci s env exps,
    fun s env x rows err => matchRecordingFull ci s env x rows err,
    fun s env decs => decsRecordingFull ci s env decs⟩
end Flapjack.Compiler.Backend.SourceEval.Proofs

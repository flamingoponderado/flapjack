import Flapjack.Compiler.Backend.SourceEval.Proofs.RecordSuffixApp
import Flapjack.EvaluateHOL.Clock

/-! Complete mutual recording-oracle clock suffix for the source evaluator. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- The source proof's clock split, including its original logical premise. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "less_sub_1_cases"]
theorem lessSubOneCases (k clock : Nat) (P : Prop)
    (premises : k ≤ clock ∧ (k ≤ clock - 1 → P)) :
    k = clock ∨ k ≤ clock - 1 := by
  omega

mutual
/-- Flapjack infrastructure: expression component of the mutual induction. -/
private theorem expsSuffixFull {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (state : State F) (env : SemEnv Value) (exprs : List AstHOL.Exp) :
    ExpsSuffixAt ci k state env exprs := by
  cases exprs with
  | nil => exact evaluateRecordSuffix_ExpsNil ci k state env
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply evaluateRecordSuffix_ExpsCons ci k state env first second tail
      refine ⟨?_, expsSuffixFull ci k state env [first]⟩
      intro middle outcome values ⟨run, rfl⟩
      have bound := evaluateClockFull state middle env [first] outcome run
      exact expsSuffixFull ci k middle env (second :: tail)
    | nil =>
      cases first with
      | lit lit => exact evaluateRecordSuffix_Lit ci k state env lit
      | var name => exact evaluateRecordSuffix_Var ci k state env name
      | fn name body => exact evaluateRecordSuffix_Fn ci k state env name body
      | raise expr => exact evaluateRecordSuffix_Raise ci k state env expr (expsSuffixFull ci k state env [expr])
      | tannot expr typ => exact evaluateRecordSuffix_Tannot ci k state env expr typ (expsSuffixFull ci k state env [expr])
      | lannot expr loc => exact evaluateRecordSuffix_Lannot ci k state env expr loc (expsSuffixFull ci k state env [expr])
      | con name args =>
        apply evaluateRecordSuffix_Con ci k state env name args
        intro _
        exact expsSuffixFull ci k state env args.reverse
      | letrec funs body =>
        apply evaluateRecordSuffix_Letrec ci k state env funs body
        intro _
        exact expsSuffixFull ci k state { env with v := buildRecEnv funs env env.v } [body]
      | let_ name bound body =>
        apply evaluateRecordSuffix_Let ci k state env name bound body
        refine ⟨?_, expsSuffixFull ci k state env [bound]⟩
        intro middle outcome values ⟨run, rfl⟩
        have clockBound := evaluateClockFull state middle env [bound] outcome run
        exact expsSuffixFull ci k middle { env with v := nsOptBind name (headValue values) env.v } [body]
      | if_ condition yes no =>
        apply evaluateRecordSuffix_If ci k state env condition yes no
        refine ⟨?_, expsSuffixFull ci k state env [condition]⟩
        intro middle outcome values branch ⟨run, rfl, chosen⟩
        have clockBound := evaluateClockFull state middle env [condition] outcome run
        rcases doIf_selected (headValue values) yes no branch chosen with equal | equal
        · subst branch; exact expsSuffixFull ci k middle env [yes]
        · subst branch; exact expsSuffixFull ci k middle env [no]
      | log op first second =>
        apply evaluateRecordSuffix_Log ci k state env op first second
        refine ⟨?_, expsSuffixFull ci k state env [first]⟩
        intro middle outcome values selection branch ⟨run, rfl, chosen, selectionEq⟩
        subst selection
        have clockBound := evaluateClockFull state middle env [first] outcome run
        have equal := doLog_selected op (headValue values) second branch chosen
        subst branch
        exact expsSuffixFull ci k middle env [second]
      | mat expr clauses =>
        apply evaluateRecordSuffix_Mat ci k state env expr clauses
        refine ⟨?_, expsSuffixFull ci k state env [expr]⟩
        intro middle outcome values ⟨run, rfl, _⟩
        have clockBound := evaluateClockFull state middle env [expr] outcome run
        exact matchSuffixFull ci k middle env (headValue values) clauses bindExnV
      | handle expr clauses =>
        apply evaluateRecordSuffix_Handle ci k state env expr clauses
        refine ⟨?_, expsSuffixFull ci k state env [expr]⟩
        intro middle outcome err value ⟨run, rfl, rfl, _⟩
        have clockBound := evaluateClockFull state middle env [expr] outcome run
        exact matchSuffixFull ci k middle env value clauses value
      | app op args =>
        apply evaluateRecordSuffix_App ci k state env op args
        refine ⟨?_, ?_, ?_, expsSuffixFull ci k state env args.reverse⟩
        · intro middle outcome values pair callEnv body ⟨run, rfl, _, _, rfl, nonzero⟩
          have clockBound := evaluateClockFull state middle env args.reverse outcome run
          exact expsSuffixFull ci k (decClock middle) callEnv [body]
        · intro middle outcome values decoded decodedResult pair evalEnv decs
            ⟨run, rfl, _, decodedRun, rfl, rfl, nonzero⟩
          have clockBound := evaluateClockFull state middle env args.reverse outcome run
          have clockEq : decoded.clock = middle.clock := by
            have hclock := congrArg (fun pair => pair.1.clock) decodedRun
            have hc := doEvalRes_clock values.reverse middle (β := Value)
            exact hclock.symm.trans hc
          exact decsSuffixFull ci k (decClock decoded) evalEnv decs
        · intro middle outcome values mode thunk pair callEnv body ⟨run, rfl, _, _, rfl, _, rfl, nonzero⟩
          have clockBound := evaluateClockFull state middle env args.reverse outcome run
          exact expsSuffixFull ci k (decClock middle) callEnv [body]
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
private theorem matchSuffixFull {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (state : State F) (env : SemEnv Value) (value : Value) (clauses : List (Pat × AstHOL.Exp)) (err : Value) :
    MatchSuffixAt ci k state env value clauses err := by
  cases clauses with
  | nil => exact evaluateRecordSuffix_MatchNil ci k state env value err
  | cons clause rest =>
    obtain ⟨pat, expr⟩ := clause
    apply evaluateRecordSuffix_MatchCons ci k state env value pat expr rest err
    constructor
    · intro bindings _
      exact expsSuffixFull ci k state { env with v := nsAppend (alistToNs bindings) env.v } [expr]
    · intro _
      exact matchSuffixFull ci k state env value rest err
termination_by (state.clock, sizeOf clauses)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals try (have := patSize_pos pat)
  all_goals try (have := listSize_pos rest)
  all_goals try simp only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega

/-- Flapjack infrastructure: declaration component of the mutual induction. -/
private theorem decsSuffixFull {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (state : State F) (env : SemEnv Value) (decs : List Dec) : DecsSuffixAt ci k state env decs := by
  cases decs with
  | nil => exact evaluateRecordSuffix_DecsNil ci k state env
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply evaluateRecordSuffix_DecsCons ci k state env first second tail
      refine ⟨?_, decsSuffixFull ci k state env [first]⟩
      intro middle outcome inner ⟨run, rfl⟩
      have clockBound := evaluateDecsClockFull state middle env [first] outcome run
      exact decsSuffixFull ci k middle (extendDecEnv inner env) (second :: tail)
    | nil =>
      cases first with
      | dtabbrev loc vars name typ => exact evaluateRecordSuffix_Dtabbrev ci k state env loc vars name typ
      | dexn loc name types => exact evaluateRecordSuffix_Dexn ci k state env loc name types
      | dtype loc types => exact evaluateRecordSuffix_Dtype ci k state env loc types
      | denv name => exact evaluateRecordSuffix_Denv ci k state env name
      | dletrec loc funs => exact evaluateRecordSuffix_Dletrec ci k state env loc funs
      | dmod name ds => exact evaluateRecordSuffix_Dmod ci k state env name ds (decsSuffixFull ci k state env ds)
      | dlet loc pat expr =>
        apply evaluateRecordSuffix_Dlet ci k state env loc pat expr
        intro _
        exact expsSuffixFull ci k state env [expr]
      | dlocal locals body =>
        apply evaluateRecordSuffix_Dlocal ci k state env locals body
        refine ⟨?_, decsSuffixFull ci k state env locals⟩
        intro middle outcome inner ⟨run, rfl⟩
        have clockBound := evaluateDecsClockFull state middle env locals outcome run
        exact decsSuffixFull ci k middle (extendDecEnv inner env) body
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


/-- Reducing the source evaluator clock either preserves the result with a
reduced final clock, or times out at a recorded-oracle prefix. The evaluator
inherits the rational-cut real-number assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluate_record_suffix {Config F : Type} (ci : CompilerInstance Config) (k : Nat) :
    (∀ (s : State F) (env : SemEnv Value) (exps : List AstHOL.Exp)
      (s' : State F) (res : Result (List Value) Value),
      evaluate s env exps = (s', res) ∧ isRecord ci s.evalState ∧ k ≤ s.clock →
      let ev := evaluate { s with clock := s.clock - k } env exps
      (k ≤ s'.clock ∧ ev = ({ s' with clock := s'.clock - k }, res)) ∨
        ∃ s'', ev = (s'', .err (.abort .timeoutError)) ∧ recordForward s''.evalState s'.evalState) ∧
    (∀ (s : State F) (env : SemEnv Value) (x : Value) (rows : List (Pat × AstHOL.Exp)) (err : Value)
      (s' : State F) (res : Result (List Value) Value),
      evaluateMatch s env x rows err = (s', res) ∧ isRecord ci s.evalState ∧ k ≤ s.clock →
      let ev := evaluateMatch { s with clock := s.clock - k } env x rows err
      (k ≤ s'.clock ∧ ev = ({ s' with clock := s'.clock - k }, res)) ∨
        ∃ s'', ev = (s'', .err (.abort .timeoutError)) ∧ recordForward s''.evalState s'.evalState) ∧
    (∀ (s : State F) (env : SemEnv Value) (decs : List Dec)
      (s' : State F) (res : Result (SemEnv Value) Value),
      evaluateDecs s env decs = (s', res) ∧ isRecord ci s.evalState ∧ k ≤ s.clock →
      let ev := evaluateDecs { s with clock := s.clock - k } env decs
      (k ≤ s'.clock ∧ ev = ({ s' with clock := s'.clock - k }, res)) ∨
        ∃ s'', ev = (s'', .err (.abort .timeoutError)) ∧ recordForward s''.evalState s'.evalState) := by
  exact ⟨fun s env exps => expsSuffixFull ci k s env exps,
    fun s env x rows err => matchSuffixFull ci k s env x rows err,
    fun s env decs => decsSuffixFull ci k s env decs⟩
end Flapjack.Compiler.Backend.SourceEval.Proofs

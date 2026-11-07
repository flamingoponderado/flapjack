import Flapjack.EvaluateProps.NoEvalApp
import Flapjack.EvaluateHOL.Clock

/-! Complete mutual simulation from an absent Eval state for the source evaluator. -/
namespace Flapjack.EvaluateProps
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

mutual
/-- Flapjack infrastructure: expression component of the mutual induction. -/
private theorem expsNoEvalFull {F : Type} (es : Option EvalState)
    (state : State F) (env : SemEnv Value) (exprs : List AstHOL.Exp) :
    NoEvalExpsAt es state env exprs := by
  cases exprs with
  | nil => exact evalNoEval_ExpsNil es state env
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply evalNoEval_ExpsCons es state env first second tail
      refine ⟨?_, expsNoEvalFull es state env [first]⟩
      intro middle outcome values ⟨run, rfl⟩
      have bound := evaluateClockFull state middle env [first] outcome run
      exact expsNoEvalFull es middle env (second :: tail)
    | nil =>
      cases first with
      | lit lit => exact evalNoEval_Lit es state env lit
      | var name => exact evalNoEval_Var es state env name
      | fn name body => exact evalNoEval_Fn es state env name body
      | raise expr => exact evalNoEval_Raise es state env expr (expsNoEvalFull es state env [expr])
      | tannot expr typ => exact evalNoEval_Tannot es state env expr typ (expsNoEvalFull es state env [expr])
      | lannot expr loc => exact evalNoEval_Lannot es state env expr loc (expsNoEvalFull es state env [expr])
      | con name args =>
        apply evalNoEval_Con es state env name args
        intro _
        exact expsNoEvalFull es state env args.reverse
      | letrec funs body =>
        apply evalNoEval_Letrec es state env funs body
        intro _
        exact expsNoEvalFull es state { env with v := buildRecEnv funs env env.v } [body]
      | let_ name bound body =>
        apply evalNoEval_Let es state env name bound body
        refine ⟨?_, expsNoEvalFull es state env [bound]⟩
        intro middle outcome values ⟨run, rfl⟩
        have clockBound := evaluateClockFull state middle env [bound] outcome run
        exact expsNoEvalFull es middle { env with v := nsOptBind name (headValue values) env.v } [body]
      | if_ condition yes no =>
        apply evalNoEval_If es state env condition yes no
        refine ⟨?_, expsNoEvalFull es state env [condition]⟩
        intro middle outcome values branch ⟨run, rfl, chosen⟩
        have clockBound := evaluateClockFull state middle env [condition] outcome run
        rcases doIf_selected (headValue values) yes no branch chosen with equal | equal
        · subst branch; exact expsNoEvalFull es middle env [yes]
        · subst branch; exact expsNoEvalFull es middle env [no]
      | log op first second =>
        apply evalNoEval_Log es state env op first second
        refine ⟨?_, expsNoEvalFull es state env [first]⟩
        intro middle outcome values selection branch ⟨run, rfl, chosen, selectionEq⟩
        subst selection
        have clockBound := evaluateClockFull state middle env [first] outcome run
        have equal := doLog_selected op (headValue values) second branch chosen
        subst branch
        exact expsNoEvalFull es middle env [second]
      | mat expr clauses =>
        apply evalNoEval_Mat es state env expr clauses
        refine ⟨?_, expsNoEvalFull es state env [expr]⟩
        intro middle outcome values ⟨run, rfl, _⟩
        have clockBound := evaluateClockFull state middle env [expr] outcome run
        exact matchNoEvalFull es middle env (headValue values) clauses bindExnV
      | handle expr clauses =>
        apply evalNoEval_Handle es state env expr clauses
        refine ⟨?_, expsNoEvalFull es state env [expr]⟩
        intro middle outcome err value ⟨run, rfl, rfl, _⟩
        have clockBound := evaluateClockFull state middle env [expr] outcome run
        exact matchNoEvalFull es middle env value clauses value
      | app op args =>
        apply evalNoEval_App es state env op args
        refine ⟨?_, ?_, ?_, expsNoEvalFull es state env args.reverse⟩
        · intro middle outcome values pair callEnv body ⟨run, rfl, _, _, rfl, nonzero⟩
          have clockBound := evaluateClockFull state middle env args.reverse outcome run
          exact expsNoEvalFull es (decClock middle) callEnv [body]
        · intro middle outcome values decoded decodedResult pair evalEnv decs
            ⟨run, rfl, _, decodedRun, rfl, rfl, nonzero⟩
          have clockBound := evaluateClockFull state middle env args.reverse outcome run
          have clockEq : decoded.clock = middle.clock := by
            have hclock := congrArg (fun pair => pair.1.clock) decodedRun
            have hc := doEvalRes_clock values.reverse middle (β := Value)
            exact hclock.symm.trans hc
          exact decsNoEvalFull es (decClock decoded) evalEnv decs
        · intro middle outcome values mode thunk pair callEnv body ⟨run, rfl, _, _, rfl, _, rfl, nonzero⟩
          have clockBound := evaluateClockFull state middle env args.reverse outcome run
          exact expsNoEvalFull es (decClock middle) callEnv [body]
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
private theorem matchNoEvalFull {F : Type} (es : Option EvalState)
    (state : State F) (env : SemEnv Value) (value : Value) (clauses : List (Pat × AstHOL.Exp)) (err : Value) :
    NoEvalMatchAt es state env value clauses err := by
  cases clauses with
  | nil => exact evalNoEval_MatchNil es state env value err
  | cons clause rest =>
    obtain ⟨pat, expr⟩ := clause
    apply evalNoEval_MatchCons es state env value pat expr rest err
    constructor
    · intro bindings _
      exact expsNoEvalFull es state { env with v := nsAppend (alistToNs bindings) env.v } [expr]
    · intro _
      exact matchNoEvalFull es state env value rest err
termination_by (state.clock, sizeOf clauses)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals try (have := patSize_pos pat)
  all_goals try (have := listSize_pos rest)
  all_goals try simp only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega

/-- Flapjack infrastructure: declaration component of the mutual induction. -/
private theorem decsNoEvalFull {F : Type} (es : Option EvalState)
    (state : State F) (env : SemEnv Value) (decs : List Dec) : NoEvalDecsAt es state env decs := by
  cases decs with
  | nil => exact evalNoEval_DecsNil es state env
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply evalNoEval_DecsCons es state env first second tail
      refine ⟨?_, decsNoEvalFull es state env [first]⟩
      intro middle outcome inner ⟨run, rfl⟩
      have clockBound := evaluateDecsClockFull state middle env [first] outcome run
      exact decsNoEvalFull es middle (extendDecEnv inner env) (second :: tail)
    | nil =>
      cases first with
      | dtabbrev loc vars name typ => exact evalNoEval_Dtabbrev es state env loc vars name typ
      | dexn loc name types => exact evalNoEval_Dexn es state env loc name types
      | dtype loc types => exact evalNoEval_Dtype es state env loc types
      | denv name => exact evalNoEval_Denv es state env name
      | dletrec loc funs => exact evalNoEval_Dletrec es state env loc funs
      | dmod name ds => exact evalNoEval_Dmod es state env name ds (decsNoEvalFull es state env ds)
      | dlet loc pat expr =>
        apply evalNoEval_Dlet es state env loc pat expr
        intro _
        exact expsNoEvalFull es state env [expr]
      | dlocal locals body =>
        apply evalNoEval_Dlocal es state env locals body
        refine ⟨?_, decsNoEvalFull es state env locals⟩
        intro middle outcome inner ⟨run, rfl⟩
        have clockBound := evaluateDecsClockFull state middle env locals outcome run
        exact decsNoEvalFull es middle (extendDecEnv inner env) body
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


/-- Replacing an absent Eval state preserves any source evaluation that does
not yield a type error, and the original final Eval state remains absent. The
evaluator inherits the rational-cut real-number assumption. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem eval_no_eval_simulation {F : Type} (es : Option EvalState) :
    (∀ (s : State F) (env : SemEnv Value) (exps : List AstHOL.Exp)
      (s' : State F) (res : Result (List Value) Value),
      evaluate s env exps = (s', res) ∧ s.evalState = none ∧ res ≠ .err (.abort .typeError) →
      s'.evalState = none ∧ evaluate { s with evalState := es } env exps = ({ s' with evalState := es }, res)) ∧
    (∀ (s : State F) (env : SemEnv Value) (x : Value) (rows : List (Pat × AstHOL.Exp)) (err : Value)
      (s' : State F) (res : Result (List Value) Value),
      evaluateMatch s env x rows err = (s', res) ∧ s.evalState = none ∧ res ≠ .err (.abort .typeError) →
      s'.evalState = none ∧ evaluateMatch { s with evalState := es } env x rows err = ({ s' with evalState := es }, res)) ∧
    (∀ (s : State F) (env : SemEnv Value) (decs : List Dec)
      (s' : State F) (res : Result (SemEnv Value) Value),
      evaluateDecs s env decs = (s', res) ∧ s.evalState = none ∧ res ≠ .err (.abort .typeError) →
      s'.evalState = none ∧ evaluateDecs { s with evalState := es } env decs = ({ s' with evalState := es }, res)) := by
  exact ⟨fun s env exps => expsNoEvalFull es s env exps,
    fun s env x rows err => matchNoEvalFull es s env x rows err,
    fun s env decs => decsNoEvalFull es s env decs⟩
end Flapjack.EvaluateProps

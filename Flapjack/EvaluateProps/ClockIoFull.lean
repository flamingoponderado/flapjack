import Flapjack.EvaluateProps.ClockIoApp

/-! Lexicographic induction assembling the original source evaluator
clock-and-I/O invariant. Source and carrier review remains pending. -/
namespace Flapjack.EvaluateProps
open Flapjack.EvaluateHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

mutual
/-- Flapjack induction infrastructure for the expression invariant. -/
theorem clockIoEvaluateFull {σ : Type} (st : State σ) (env : SemEnv Value) (es : List AstHOL.Exp) :
    isClockIoMono (fun state => evaluate state env es) st := by
  cases es with
  | nil => exact clockIoEvaluate_nil st env
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply clockIoEvaluate_cons st env first second tail (clockIoEvaluateFull st env [first])
      intro middle values firstEq
      have bound := evaluateClockFull st middle env [first] (.val values) firstEq
      exact clockIoEvaluateFull middle env (second :: tail)
    | nil =>
      cases first with
      | lit lit => exact clockIoEvaluate_lit st env lit
      | var name => exact clockIoEvaluate_var st env name
      | fn name body => exact clockIoEvaluate_fn st env name body
      | raise expr => exact clockIoEvaluate_raise st env expr (clockIoEvaluateFull st env [expr])
      | tannot expr typ => exact clockIoEvaluate_tannot st env expr typ (clockIoEvaluateFull st env [expr])
      | lannot expr loc => exact clockIoEvaluate_lannot st env expr loc (clockIoEvaluateFull st env [expr])
      | con name args => exact clockIoEvaluate_con st env name args (clockIoEvaluateFull st env args.reverse)
      | letrec funs body =>
        exact clockIoEvaluate_letrec st env funs body (clockIoEvaluateFull st { env with v := buildRecEnv funs env env.v } [body])
      | let_ name first body =>
        apply clockIoEvaluate_let st env name first body (clockIoEvaluateFull st env [first])
        intro middle values firstEq
        have bound := evaluateClockFull st middle env [first] (.val values) firstEq
        exact clockIoEvaluateFull middle { env with v := nsOptBind name (headValue values) env.v } [body]
      | if_ test yes no =>
        apply clockIoEvaluate_if st env test yes no (clockIoEvaluateFull st env [test])
        intro middle values chosen firstEq selected
        have bound := evaluateClockFull st middle env [test] (.val values) firstEq
        rcases doIf_selected (headValue values) yes no chosen selected with equal | equal
        · subst chosen; exact clockIoEvaluateFull middle env [yes]
        · subst chosen; exact clockIoEvaluateFull middle env [no]
      | log op first second =>
        apply clockIoEvaluate_log st env op first second (clockIoEvaluateFull st env [first])
        intro middle values chosen firstEq selected
        have bound := evaluateClockFull st middle env [first] (.val values) firstEq
        have equal := doLog_selected op (headValue values) second chosen selected
        subst chosen
        exact clockIoEvaluateFull middle env [second]
      | mat expr clauses =>
        apply clockIoEvaluate_mat st env expr clauses (clockIoEvaluateFull st env [expr])
        intro middle values firstEq _
        have bound := evaluateClockFull st middle env [expr] (.val values) firstEq
        exact clockIoMatchFull middle env (headValue values) clauses bindExnV
      | handle expr clauses =>
        apply clockIoEvaluate_handle st env expr clauses (clockIoEvaluateFull st env [expr])
        intro middle value firstEq _
        have bound := evaluateClockFull st middle env [expr] (.err (.raise value)) firstEq
        exact clockIoMatchFull middle env value clauses value
      | app op args =>
        apply clockIoEvaluate_app st env op args (clockIoEvaluateFull st env args.reverse)
        · intro middle values callEnv body argsEq _ _ nonzero
          have bound := evaluateClockFull st middle env args.reverse (.val values) argsEq
          exact clockIoEvaluateFull (decClock middle) callEnv [body]
        · intro middle values thunk callEnv body argsEq _ _ _ nonzero
          have bound := evaluateClockFull st middle env args.reverse (.val values) argsEq
          exact clockIoEvaluateFull (decClock middle) callEnv [body]
        · intro middle values decoded evalEnv decs argsEq _ decodedEq nonzero
          have bound := evaluateClockFull st middle env args.reverse (.val values) argsEq
          have clockEq : decoded.clock = middle.clock := by
            have hclock := congrArg (fun pair => pair.1.clock) decodedEq
            have hc := doEvalRes_clock values.reverse middle (β := Value)
            exact hclock.symm.trans hc
          exact clockIoDecsFull (decClock decoded) evalEnv decs
termination_by (st.clock, sizeOf es)
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

/-- Flapjack induction infrastructure for the pattern-match invariant. -/
theorem clockIoMatchFull {σ : Type} (st : State σ) (env : SemEnv Value)
    (value : Value) (clauses : List (Pat × AstHOL.Exp)) (errorValue : Value) :
    isClockIoMono (fun state => evaluateMatch state env value clauses errorValue) st := by
  cases clauses with
  | nil => exact clockIoMatch_nil st env value errorValue
  | cons clause rest =>
    cases clause with
    | mk pat expr =>
      apply clockIoMatch_cons st env value errorValue pat expr rest
      · exact clockIoMatchFull st env value rest errorValue
      · intro bindings
        exact clockIoEvaluateFull st { env with v := nsAppend (alistToNs bindings) env.v } [expr]
termination_by (st.clock, sizeOf clauses)
decreasing_by
  all_goals try subst_vars
  all_goals simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals try (have := patSize_pos pat)
  all_goals try (have := listSize_pos rest)
  all_goals try simp only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega

/-- Flapjack induction infrastructure for the declaration invariant. -/
theorem clockIoDecsFull {σ : Type} (st : State σ) (env : SemEnv Value) (ds : List Dec) :
    isClockIoMono (fun state => evaluateDecs state env ds) st := by
  cases ds with
  | nil => exact clockIoDecs_nil st env
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply clockIoDecs_cons st env first second tail (clockIoDecsFull st env [first])
      intro middle inner firstEq
      have bound := evaluateDecsClockFull st middle env [first] (.val inner) firstEq
      exact clockIoDecsFull middle (extendDecEnv inner env) (second :: tail)
    | nil =>
      cases first with
      | dtabbrev loc vars name typ => exact clockIoDecs_tabbrev st env loc vars name typ
      | dexn loc name types => exact clockIoDecs_exn st env loc name types
      | dtype loc types => exact clockIoDecs_type st env loc types
      | denv name => exact clockIoDecs_env st env name
      | dletrec loc funs => exact clockIoDecs_letrec st env loc funs
      | dmod name decs => exact clockIoDecs_mod st env name decs (clockIoDecsFull st env decs)
      | dlet loc pat expr => exact clockIoDecs_let st env loc pat expr (clockIoEvaluateFull st env [expr])
      | dlocal localDecs decs =>
        apply clockIoDecs_local st env localDecs decs (clockIoDecsFull st env localDecs)
        intro middle inner firstEq
        have bound := evaluateDecsClockFull st middle env localDecs (.val inner) firstEq
        exact clockIoDecsFull middle (extendDecEnv inner env) decs
termination_by (st.clock, sizeOf ds)
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

/-- The original three-part evaluator clock-and-I/O invariant. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_evaluate"]
theorem isClockIoMono_evaluate {σ : Type} :
    (∀ (st : State σ) env es, isClockIoMono (fun state => evaluate state env es) st) ∧
    (∀ (st : State σ) env value clauses errorValue,
      isClockIoMono (fun state => evaluateMatch state env value clauses errorValue) st) ∧
    (∀ (st : State σ) env ds, isClockIoMono (fun state => evaluateDecs state env ds) st) :=
  ⟨clockIoEvaluateFull, clockIoMatchFull, clockIoDecsFull⟩

end Flapjack.EvaluateProps

import Flapjack.EvaluateProps.EvaluateFfi

/-! Lexicographic induction assembling the source evaluator FFI cases.
Source/carrier review remains pending, including the inherited rational-cut assumption. -/
namespace Flapjack.EvaluateProps
open Flapjack.EvaluateHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

mutual
/-- Flapjack induction infrastructure for expression FFI preservation. -/
theorem evaluateFfiFull {σ : Type} (st : State σ) (env : SemEnv Value) (es : List AstHOL.Exp) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env es).1.ffi := by
  cases es with
  | nil => exact evaluateFfi_nil st env
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply evaluateFfi_cons st env first second tail (evaluateFfiFull st env [first])
      intro middle values firstEq
      have bound := evaluateClockFull st middle env [first] (.val values) firstEq
      exact evaluateFfiFull middle env (second :: tail)
    | nil =>
      cases first with
      | lit lit => exact evaluateFfi_lit st env lit
      | var name => exact evaluateFfi_var st env name
      | fn name body => exact evaluateFfi_fun st env name body
      | raise expr => exact evaluateFfi_raise st env expr (evaluateFfiFull st env [expr])
      | tannot expr typ => exact evaluateFfi_tannot st env expr typ (evaluateFfiFull st env [expr])
      | lannot expr loc => exact evaluateFfi_lannot st env expr loc (evaluateFfiFull st env [expr])
      | con name args => exact evaluateFfi_con st env name args (evaluateFfiFull st env args.reverse)
      | letrec funs body =>
        exact evaluateFfi_letrec st env funs body (evaluateFfiFull st { env with v := buildRecEnv funs env env.v } [body])
      | let_ name first body =>
        apply evaluateFfi_let st env name first body (evaluateFfiFull st env [first])
        intro middle values firstEq
        have bound := evaluateClockFull st middle env [first] (.val values) firstEq
        exact evaluateFfiFull middle { env with v := nsOptBind name (headValue values) env.v } [body]
      | if_ test yes no =>
        apply evaluateFfi_if st env test yes no (evaluateFfiFull st env [test])
        intro middle values chosen firstEq selected
        have bound := evaluateClockFull st middle env [test] (.val values) firstEq
        rcases doIf_selected (headValue values) yes no chosen selected with equal | equal
        · subst chosen; exact evaluateFfiFull middle env [yes]
        · subst chosen; exact evaluateFfiFull middle env [no]
      | log op first second =>
        apply evaluateFfi_log st env op first second (evaluateFfiFull st env [first])
        intro middle values chosen firstEq selected
        have bound := evaluateClockFull st middle env [first] (.val values) firstEq
        have equal := doLog_selected op (headValue values) second chosen selected
        subst chosen
        exact evaluateFfiFull middle env [second]
      | mat expr clauses =>
        apply evaluateFfi_mat st env expr clauses (evaluateFfiFull st env [expr])
        intro middle values firstEq
        have bound := evaluateClockFull st middle env [expr] (.val values) firstEq
        exact evaluateMatchFfiFull middle env (headValue values) clauses bindExnV
      | handle expr clauses =>
        apply evaluateFfi_handle st env expr clauses (evaluateFfiFull st env [expr])
        intro middle value firstEq
        have bound := evaluateClockFull st middle env [expr] (.err (.raise value)) firstEq
        exact evaluateMatchFfiFull middle env value clauses value
      | app op args =>
        apply evaluateFfi_app st env op args (evaluateFfiFull st env args.reverse)
        · intro middle values callEnv body argsEq _ _ nonzero
          have bound := evaluateClockFull st middle env args.reverse (.val values) argsEq
          exact evaluateFfiFull (decClock middle) callEnv [body]
        · intro middle values thunk callEnv body argsEq _ _ _ nonzero
          have bound := evaluateClockFull st middle env args.reverse (.val values) argsEq
          exact evaluateFfiFull (decClock middle) callEnv [body]
        · intro middle values decoded evalEnv decs argsEq _ decodedEq nonzero
          have bound := evaluateClockFull st middle env args.reverse (.val values) argsEq
          have clockEq : decoded.clock = middle.clock := by
            have hclock := congrArg (fun pair => pair.1.clock) decodedEq
            have hc := doEvalRes_clock values.reverse middle (β := Value)
            exact hclock.symm.trans hc
          exact evaluateDecsFfiFull (decClock decoded) evalEnv decs
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

/-- Flapjack induction infrastructure for pattern-match FFI preservation. -/
theorem evaluateMatchFfiFull {σ : Type} (st : State σ) (env : SemEnv Value)
    (value : Value) (clauses : List (Pat × AstHOL.Exp)) (errorValue : Value) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateMatch st env value clauses errorValue).1.ffi := by
  cases clauses with
  | nil => exact evaluateMatchFfi_nil st env value errorValue
  | cons clause rest =>
    cases clause with
    | mk pat expr =>
      apply evaluateMatchFfi_cons st env value errorValue pat expr rest
      · exact evaluateMatchFfiFull st env value rest errorValue
      · intro bindings
        exact evaluateFfiFull st { env with v := nsAppend (alistToNs bindings) env.v } [expr]
termination_by (st.clock, sizeOf clauses)
decreasing_by
  all_goals try subst_vars
  all_goals simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals try (have := patSize_pos pat)
  all_goals try (have := listSize_pos rest)
  all_goals try simp only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega

/-- Flapjack induction infrastructure for declaration FFI preservation. -/
theorem evaluateDecsFfiFull {σ : Type} (st : State σ) (env : SemEnv Value) (ds : List Dec) :
    Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateDecs st env ds).1.ffi := by
  cases ds with
  | nil => exact evaluateDecsFfi_nil st env
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply evaluateDecsFfi_cons st env first second tail (evaluateDecsFfiFull st env [first])
      intro middle inner firstEq
      have bound := evaluateDecsClockFull st middle env [first] (.val inner) firstEq
      exact evaluateDecsFfiFull middle (extendDecEnv inner env) (second :: tail)
    | nil =>
      cases first with
      | dtabbrev loc vars name typ => exact evaluateDecsFfi_tabbrev st env loc vars name typ
      | dexn loc name types => exact evaluateDecsFfi_exn st env loc name types
      | dtype loc types => exact evaluateDecsFfi_type st env loc types
      | denv name => exact evaluateDecsFfi_env st env name
      | dletrec loc funs => exact evaluateDecsFfi_letrec st env loc funs
      | dmod name decs => exact evaluateDecsFfi_mod st env name decs (evaluateDecsFfiFull st env decs)
      | dlet loc pat expr => exact evaluateDecsFfi_let st env loc pat expr (evaluateFfiFull st env [expr])
      | dlocal localDecs decs =>
        apply evaluateDecsFfi_local st env localDecs decs (evaluateDecsFfiFull st env localDecs)
        intro middle inner firstEq
        have bound := evaluateDecsClockFull st middle env localDecs (.val inner) firstEq
        exact evaluateDecsFfiFull middle (extendDecEnv inner env) decs
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

/-- The original three-part source evaluator FFI transition theorem. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel"]
theorem evaluateCallFFIRel {σ : Type} :
    (∀ (st : State σ) env es, Relation.ReflTransGen callFFIRelHOL st.ffi (evaluate st env es).1.ffi) ∧
    (∀ (st : State σ) env value clauses errorValue,
      Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateMatch st env value clauses errorValue).1.ffi) ∧
    (∀ (st : State σ) env ds, Relation.ReflTransGen callFFIRelHOL st.ffi (evaluateDecs st env ds).1.ffi) :=
  ⟨evaluateFfiFull, evaluateMatchFfiFull, evaluateDecsFfiFull⟩

/-- The original evaluator trace-monotonicity theorem. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_io_events_mono"]
theorem evaluateIoEventsMono {σ τ : Type} :
    (∀ (st : State σ) env es, ioEventsMonoHOL st.ffi (evaluate st env es).1.ffi) ∧
    (∀ (st : State σ) env value clauses errorValue,
      ioEventsMonoHOL st.ffi (evaluateMatch st env value clauses errorValue).1.ffi) ∧
    (∀ (st : State τ) env ds, ioEventsMonoHOL st.ffi (evaluateDecs st env ds).1.ffi) := by
  refine ⟨?_, ?_, ?_⟩
  · intro st env es; exact callFFIRelHOL_rtc_ioEventsMono _ _ (evaluateFfiFull st env es)
  · intro st env value clauses errorValue
    exact callFFIRelHOL_rtc_ioEventsMono _ _ (evaluateMatchFfiFull st env value clauses errorValue)
  · intro st env ds; exact callFFIRelHOL_rtc_ioEventsMono _ _ (evaluateDecsFfiFull st env ds)

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_call_FFI_rel_imp"]
theorem evaluateCallFFIRelImp {σ τ υ : Type} :
    (∀ (st : State σ) env es st' result, evaluate st env es = (st', result) →
      Relation.ReflTransGen callFFIRelHOL st.ffi st'.ffi) ∧
    (∀ (st : State τ) env value clauses errorValue st' result,
      evaluateMatch st env value clauses errorValue = (st', result) →
      Relation.ReflTransGen callFFIRelHOL st.ffi st'.ffi) ∧
    (∀ (st : State υ) env ds st' result, evaluateDecs st env ds = (st', result) →
      Relation.ReflTransGen callFFIRelHOL st.ffi st'.ffi) := by
  refine ⟨?_, ?_, ?_⟩
  · intro st env es st' result h; simpa only [h] using evaluateFfiFull st env es
  · intro st env value clauses errorValue st' result h
    simpa only [h] using evaluateMatchFfiFull st env value clauses errorValue
  · intro st env ds st' result h; simpa only [h] using evaluateDecsFfiFull st env ds

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_decs_call_FFI_rel_imp"]
theorem evaluateDecsCallFFIRelImp {σ : Type} (st : State σ) (env : SemEnv Value)
    (ds : List Dec) (st' : State σ) (result : Result (SemEnv Value) Value)
    (h : evaluateDecs st env ds = (st', result)) :
    Relation.ReflTransGen callFFIRelHOL st.ffi st'.ffi := by
  simpa only [h] using evaluateDecsFfiFull st env ds

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_io_events_mono_imp"]
theorem evaluateIoEventsMonoImp {σ τ υ : Type} :
    (∀ (st : State σ) env es st' result, evaluate st env es = (st', result) → ioEventsMonoHOL st.ffi st'.ffi) ∧
    (∀ (st : State τ) env value clauses errorValue st' result,
      evaluateMatch st env value clauses errorValue = (st', result) → ioEventsMonoHOL st.ffi st'.ffi) ∧
    (∀ (st : State υ) env ds st' result, evaluateDecs st env ds = (st', result) → ioEventsMonoHOL st.ffi st'.ffi) := by
  refine ⟨?_, ?_, ?_⟩
  · intro st env es st' result h; simpa only [h] using (evaluateIoEventsMono (σ := σ) (τ := υ)).1 st env es
  · intro st env value clauses errorValue st' result h
    simpa only [h] using (evaluateIoEventsMono (σ := τ) (τ := υ)).2.1 st env value clauses errorValue
  · intro st env ds st' result h; simpa only [h] using (evaluateIoEventsMono (σ := σ) (τ := υ)).2.2 st env ds

end Flapjack.EvaluateProps

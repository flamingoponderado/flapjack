import Flapjack.EvaluateHOL.Clock

/-! Explicit lexicographic induction over the source evaluator's three
mutually recursive entry points. -/
namespace Flapjack.EvaluateHOL
open Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

mutual
/-- Flapjack induction infrastructure for the expression clock theorem. -/
theorem evaluateClockFull {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (es : List Flapjack.AstHOL.Exp) (result : Result (List Value) Value)
    (h : evaluate st env es = (st', result)) : st'.clock ≤ st.clock := by
  cases es with
  | nil => exact evaluateClock_nil st st' env result h
  | cons first rest =>
    cases rest with
    | cons second tail =>
      have firstIH : ∀ next outcome, evaluate st env [first] = (next, outcome) → next.clock ≤ st.clock := by
        intro next outcome eq
        exact evaluateClockFull st next env [first] outcome eq
      apply evaluateClock_cons st st' env first second tail result firstIH ?_ h
      intro middle values next outcome firstEq tailEq
      have bound := firstIH middle (.val values) firstEq
      exact evaluateClockFull middle next env (second :: tail) outcome tailEq
    | nil =>
      cases first with
      | lit lit => exact evaluateClock_lit st st' env lit result h
      | var name => exact evaluateClock_var st st' env name result h
      | fn name body => exact evaluateClock_fun st st' env name body result h
      | raise expr =>
        apply evaluateClock_raise st st' env expr result ?_ h
        intro next outcome eq
        exact evaluateClockFull st next env [expr] outcome eq
      | tannot expr typ =>
        apply evaluateClock_tannot st st' env expr typ result ?_ h
        intro next outcome eq
        exact evaluateClockFull st next env [expr] outcome eq
      | lannot expr loc =>
        apply evaluateClock_lannot st st' env expr loc result ?_ h
        intro next outcome eq
        exact evaluateClockFull st next env [expr] outcome eq
      | con name args =>
        apply evaluateClock_con st st' env name args result ?_ h
        intro _ next outcome eq
        exact evaluateClockFull st next env args.reverse outcome eq
      | letrec funs body =>
        apply evaluateClock_letrec st st' env funs body result ?_ h
        intro _ next outcome eq
        exact evaluateClockFull st next { env with v := buildRecEnv funs env env.v } [body] outcome eq
      | let_ name first body =>
        have firstIH : ∀ next outcome, evaluate st env [first] = (next, outcome) → next.clock ≤ st.clock := by
          intro next outcome eq
          exact evaluateClockFull st next env [first] outcome eq
        apply evaluateClock_let st st' env name first body result firstIH ?_ h
        intro middle values next outcome firstEq bodyEq
        have bound := firstIH middle (.val values) firstEq
        exact evaluateClockFull middle next { env with v := nsOptBind name (headValue values) env.v } [body] outcome bodyEq
      | if_ test yes no =>
        have testIH : ∀ next outcome, evaluate st env [test] = (next, outcome) → next.clock ≤ st.clock := by
          intro next outcome eq
          exact evaluateClockFull st next env [test] outcome eq
        apply evaluateClock_if st st' env test yes no result testIH ?_ h
        intro middle values chosen next outcome testEq selected bodyEq
        have bound := testIH middle (.val values) testEq
        rcases doIf_selected (headValue values) yes no chosen selected with equal | equal
        · subst chosen
          exact evaluateClockFull middle next env [yes] outcome bodyEq
        · subst chosen
          exact evaluateClockFull middle next env [no] outcome bodyEq
      | log op first second =>
        have firstIH : ∀ next outcome, evaluate st env [first] = (next, outcome) → next.clock ≤ st.clock := by
          intro next outcome eq
          exact evaluateClockFull st next env [first] outcome eq
        apply evaluateClock_log st st' env op first second result firstIH ?_ h
        intro middle values chosen next outcome firstEq selected bodyEq
        have bound := firstIH middle (.val values) firstEq
        have equal := doLog_selected op (headValue values) second chosen selected
        subst chosen
        exact evaluateClockFull middle next env [second] outcome bodyEq
      | mat expr clauses =>
        have exprIH : ∀ next outcome, evaluate st env [expr] = (next, outcome) → next.clock ≤ st.clock := by
          intro next outcome eq
          exact evaluateClockFull st next env [expr] outcome eq
        apply evaluateClock_mat st st' env expr clauses result exprIH ?_ h
        intro middle values next outcome exprEq _ matchEq
        have bound := exprIH middle (.val values) exprEq
        exact evaluateMatchClockFull middle next env (headValue values) clauses bindExnV outcome matchEq
      | handle expr clauses =>
        have exprIH : ∀ next outcome, evaluate st env [expr] = (next, outcome) → next.clock ≤ st.clock := by
          intro next outcome eq
          exact evaluateClockFull st next env [expr] outcome eq
        apply evaluateClock_handle st st' env expr clauses result exprIH ?_ h
        intro middle value next outcome exprEq _ matchEq
        have bound := exprIH middle (.err (.raise value)) exprEq
        exact evaluateMatchClockFull middle next env value clauses value outcome matchEq
      | app op args =>
        have argsIH : ∀ next outcome, evaluate st env args.reverse = (next, outcome) → next.clock ≤ st.clock := by
          intro next outcome eq
          exact evaluateClockFull st next env args.reverse outcome eq
        apply evaluateClock_app st st' env op args result argsIH ?_ ?_ ?_ h
        · intro middle values callEnv body next outcome argsEq _ _ nonzero callEq
          have bound := argsIH middle (.val values) argsEq
          exact evaluateClockFull (decClock middle) next callEnv [body] outcome callEq
        · intro middle values thunk callEnv body next outcome argsEq _ _ _ nonzero callEq
          have bound := argsIH middle (.val values) argsEq
          exact evaluateClockFull (decClock middle) next callEnv [body] outcome callEq
        · intro middle values decoded evalEnv decs next outcome argsEq _ decodedEq nonzero decsEq
          have bound := argsIH middle (.val values) argsEq
          have clockEq : decoded.clock = middle.clock := by
            have hclock := congrArg (fun pair => pair.1.clock) decodedEq
            have hc := doEvalRes_clock values.reverse middle (β := Value)
            exact hclock.symm.trans hc
          exact evaluateDecsClockFull (decClock decoded) next evalEnv decs outcome decsEq
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

/-- Flapjack induction infrastructure for the match clock theorem. -/
theorem evaluateMatchClockFull {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (value : Value) (clauses : List (Pat × Flapjack.AstHOL.Exp)) (errorValue : Value)
    (result : Result (List Value) Value) (h : evaluateMatch st env value clauses errorValue = (st', result)) :
    st'.clock ≤ st.clock := by
  cases clauses with
  | nil => exact evaluateMatchClock_nil st st' env value errorValue result h
  | cons clause rest =>
    cases hclause : clause with
    | mk pat expr =>
      rw [hclause] at h
      apply evaluateMatchClock_cons st st' env value errorValue pat expr rest result ?_ ?_ h
      · intro _ _ next outcome eq
        exact evaluateMatchClockFull st next env value rest errorValue outcome eq
      · intro _ bindings next outcome _ eq
        exact evaluateClockFull st next { env with v := nsAppend (alistToNs bindings) env.v } [expr] outcome eq
termination_by (st.clock, sizeOf clauses)
decreasing_by
  all_goals try subst_vars
  all_goals simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals try (have := patSize_pos pat)
  all_goals try (have := listSize_pos rest)
  all_goals try simp only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega

/-- Flapjack induction infrastructure for the declaration clock theorem. -/
theorem evaluateDecsClockFull {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (ds : List Dec) (result : Result (SemEnv Value) Value)
    (h : evaluateDecs st env ds = (st', result)) : st'.clock ≤ st.clock := by
  cases ds with
  | nil => exact evaluateDecsClock_nil st st' env result h
  | cons first rest =>
    cases rest with
    | cons second tail =>
      have firstIH : ∀ next outcome, evaluateDecs st env [first] = (next, outcome) → next.clock ≤ st.clock := by
        intro next outcome eq
        exact evaluateDecsClockFull st next env [first] outcome eq
      apply evaluateDecsClock_cons st st' env first second tail result firstIH ?_ h
      intro middle inner next outcome firstEq tailEq
      have bound := firstIH middle (.val inner) firstEq
      exact evaluateDecsClockFull middle next (extendDecEnv inner env) (second :: tail) outcome tailEq
    | nil =>
      cases first with
      | dtabbrev loc vars name typ => exact evaluateDecsClock_tabbrev st st' env loc vars name typ result h
      | dexn loc name types => exact evaluateDecsClock_exn st st' env loc name types result h
      | dtype loc types => exact evaluateDecsClock_type st st' env loc types result h
      | denv name => exact evaluateDecsClock_env st st' env name result h
      | dletrec loc funs => exact evaluateDecsClock_letrec st st' env loc funs result h
      | dmod name decs =>
        apply evaluateDecsClock_mod st st' env name decs result ?_ h
        intro next outcome eq
        exact evaluateDecsClockFull st next env decs outcome eq
      | dlet loc pat expr =>
        apply evaluateDecsClock_let st st' env loc pat expr result ?_ h
        intro _ _ next outcome eq
        exact evaluateClockFull st next env [expr] outcome eq
      | dlocal localDecs decs =>
        have firstIH : ∀ next outcome, evaluateDecs st env localDecs = (next, outcome) → next.clock ≤ st.clock := by
          intro next outcome eq
          exact evaluateDecsClockFull st next env localDecs outcome eq
        apply evaluateDecsClock_local st st' env localDecs decs result firstIH ?_ h
        intro middle inner next outcome firstEq tailEq
        have bound := firstIH middle (.val inner) firstEq
        exact evaluateDecsClockFull middle next (extendDecEnv inner env) decs outcome tailEq
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

/-- The original three-part evaluator clock bound. Source and imported-carrier
review remains pending; floating-point cases inherit the primitive
dispatcher's rational-cut assumption. -/
@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateClock {σ : Type} :
    (∀ (st : State σ) env es result st', evaluate st env es = (st', result) → st'.clock ≤ st.clock) ∧
    (∀ (st : State σ) env value clauses errorValue result st',
      evaluateMatch st env value clauses errorValue = (st', result) → st'.clock ≤ st.clock) ∧
    (∀ (st : State σ) env decs result st', evaluateDecs st env decs = (st', result) → st'.clock ≤ st.clock) := by
  refine ⟨?_, ?_, ?_⟩
  · intro st env es result st' h
    exact evaluateClockFull st st' env es result h
  · intro st env value clauses errorValue result st' h
    exact evaluateMatchClockFull st st' env value clauses errorValue result h
  · intro st env decs result st' h
    exact evaluateDecsClockFull st st' env decs result h

/-- The original clock-clamp identity for expression and declaration
execution, derived from the three-part clock theorem. -/
@[hol "cakeml/semantics/evaluateScript.sml" "fix_clock_evaluate"]
theorem fixClockEvaluate {σ : Type} (st : State σ) (env : SemEnv Value)
    (es : List Flapjack.AstHOL.Exp) (decs : List Dec) :
    fixClock st (evaluate st env es) = evaluate st env es ∧
      fixClock st (evaluateDecs st env decs) = evaluateDecs st env decs := by
  constructor
  · apply fixClock_eq_of_bound
    exact evaluateClockFull st (evaluate st env es).1 env es (evaluate st env es).2 (Prod.eta _).symm
  · apply fixClock_eq_of_bound
    exact evaluateDecsClockFull st (evaluateDecs st env decs).1 env decs (evaluateDecs st env decs).2 (Prod.eta _).symm

end Flapjack.EvaluateHOL

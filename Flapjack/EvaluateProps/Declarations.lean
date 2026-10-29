import Flapjack.EvaluateHOL.ClockFull

/-! Composition of the original clocked declaration evaluator. -/
namespace Flapjack.EvaluateProps
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.EvaluateHOL

private theorem extendEmpty (env : SemEnv Value) : extendDecEnv ⟨nsEmpty, nsEmpty⟩ env = env := by
  cases env with
  | mk values constructors => cases values; cases constructors; rfl

private theorem combineEmpty (env : SemEnv Value) :
    combineDecResult env (.val ⟨nsEmpty, nsEmpty⟩ : Result (SemEnv Value) Value) = .val env := by
  cases env with
  | mk values constructors => cases values; cases constructors; rfl

private theorem combineEmptyLeft (result : Result (SemEnv Value) Value) :
    combineDecResult ⟨nsEmpty, nsEmpty⟩ result = result := by
  cases result with
  | err error => rfl
  | val env =>
    cases env with
    | mk values constructors =>
      cases values
      cases constructors
      simp [combineDecResult, nsAppend, nsEmpty]

/-- Environment extension associates in the same order as namespace append.
This helper has no separate HOL declaration. -/
theorem extendDecEnv_assoc (inner middle outer : SemEnv Value) :
    extendDecEnv inner (extendDecEnv middle outer) = extendDecEnv (extendDecEnv inner middle) outer := by
  cases inner with
  | mk iv ic =>
    cases middle with
    | mk mv mc =>
      cases outer with
      | mk ov oc =>
        cases iv; cases ic; cases mv; cases mc; cases ov; cases oc
        simp [extendDecEnv, nsAppend, List.append_assoc]

private theorem combineAssoc (first second : SemEnv Value) (result : Result (SemEnv Value) Value) :
    combineDecResult first (combineDecResult second result) =
      combineDecResult (extendDecEnv second first) result := by
  cases result with
  | err error => rfl
  | val env =>
    change Result.val (extendDecEnv (extendDecEnv env second) first) =
      Result.val (extendDecEnv env (extendDecEnv second first))
    exact congrArg Result.val (extendDecEnv_assoc env second first).symm

/-- Evaluating a declaration followed by a list is equivalent to evaluating
the head, extending the environment, and combining the remaining result. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_decs_cons"]
theorem evaluateDecs_cons {F : Type} (state : State F) (env : SemEnv Value) (d : Dec) (ds : List Dec) :
    evaluateDecs state env (d :: ds) =
      (let first := evaluateDecs state env [d]
       match first.2 with
       | .err error => (first.1, .err error)
       | .val inner =>
          let rest := evaluateDecs first.1 (extendDecEnv inner env) ds
          (rest.1, combineDecResult inner rest.2)) := by
  cases ds with
  | nil =>
    cases run : evaluateDecs state env [d] with
    | mk next result =>
      cases result with
      | err error => simp
      | val inner =>
        simp only [evaluateDecs, Prod.mk.injEq, true_and]
        change (Result.val inner : Result (SemEnv Value) Value) = combineDecResult inner (.val ⟨nsEmpty, nsEmpty⟩)
        rw [combineEmpty]
  | cons second rest =>
    conv =>
      lhs
      rw [evaluateDecs, (fixClockEvaluate state env [] [d]).2]
    rfl

/-- Declaration evaluation composes over list append, including exceptional
results and the original order of environment extension. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_decs_append"]
theorem evaluateDecs_append {F : Type} (ds1 : List Dec) (state : State F)
    (env : SemEnv Value) (ds2 : List Dec) :
    evaluateDecs state env (ds1 ++ ds2) =
      (let first := evaluateDecs state env ds1
       match first.2 with
       | .err error => (first.1, .err error)
       | .val inner =>
          let second := evaluateDecs first.1 (extendDecEnv inner env) ds2
          (second.1, combineDecResult inner second.2)) := by
  induction ds1 generalizing state env with
  | nil =>
    simp only [List.nil_append, evaluateDecs]
    change evaluateDecs state env ds2 =
      (let result := evaluateDecs state (extendDecEnv ⟨nsEmpty, nsEmpty⟩ env) ds2
       (result.1, combineDecResult ⟨nsEmpty, nsEmpty⟩ result.2))
    rw [extendEmpty]
    dsimp only
    rw [combineEmptyLeft, Prod.eta]
  | cons d rest ih =>
    rw [List.cons_append, evaluateDecs_cons state env d (rest ++ ds2), evaluateDecs_cons state env d rest]
    cases first : evaluateDecs state env [d] with
    | mk middle result =>
      cases result with
      | err error => simp
      | val inner =>
        simp only
        rw [ih]
        cases second : evaluateDecs middle (extendDecEnv inner env) rest with
        | mk next result =>
          cases result with
          | err error => simp [combineDecResult]
          | val secondEnv =>
            change (let out := evaluateDecs next (extendDecEnv secondEnv (extendDecEnv inner env)) ds2;
                    (out.1, combineDecResult inner (combineDecResult secondEnv out.2))) =
              (let out := evaluateDecs next (extendDecEnv (extendDecEnv secondEnv inner) env) ds2;
                    (out.1, combineDecResult (extendDecEnv secondEnv inner) out.2))
            rw [extendDecEnv_assoc]
            dsimp only
            rw [combineAssoc]

/-- A local declaration first evaluates its private declarations, then the
body in their extension of the original environment. This is a direct
clocked-evaluator equation rather than a separate HOL declaration. -/
theorem evaluateDecs_local {F : Type} (state : State F) (env : SemEnv Value)
    (locals body : List Dec) :
    evaluateDecs state env [.dlocal locals body] =
      (let result := evaluateDecs state env locals
       match result.2 with
       | .err error => (result.1, .err error)
       | .val inner => evaluateDecs result.1 (extendDecEnv inner env) body) := by
  conv =>
    lhs
    rw [evaluateDecs, (fixClockEvaluate state env [] locals).2]
  rfl

end Flapjack.EvaluateProps

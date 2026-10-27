import Flapjack.EvaluateProps.ClockIoCases

/-! Conditional structural assembly of the declaration and pattern-match
invariants. The expression invariant is an explicit temporary dependency;
these Flapjack helpers are not the original unconditional HOL theorem. -/
namespace Flapjack.EvaluateProps
open Flapjack.EvaluateHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

/-- Flapjack induction helper: pattern matching follows once the expression
invariant is established for every expression and environment. -/
theorem clockIoMatchFromExpr {σ : Type}
    (exprIH : ∀ (st : State σ) (env : SemEnv Value) (expr : AstHOL.Exp),
      isClockIoMono (fun state => evaluate state env [expr]) st)
    (st : State σ) (env : SemEnv Value) (value : Value)
    (clauses : List (Pat × AstHOL.Exp)) (errorValue : Value) :
    isClockIoMono (fun state => evaluateMatch state env value clauses errorValue) st := by
  cases clauses with
  | nil => exact clockIoMatch_nil st env value errorValue
  | cons clause rest =>
    cases clause with
    | mk pat expr =>
      apply clockIoMatch_cons st env value errorValue pat expr rest
      · exact clockIoMatchFromExpr exprIH st env value rest errorValue
      · intro bindings
        exact exprIH st { env with v := nsAppend (alistToNs bindings) env.v } expr
termination_by sizeOf clauses
decreasing_by
  all_goals simp_wf
  all_goals try (have := patSize_pos pat)
  all_goals try omega

/-- Flapjack induction helper: declaration evaluation follows once the
expression invariant is established. The premise is an open proof dependency. -/
theorem clockIoDecsFromExpr {σ : Type}
    (exprIH : ∀ (st : State σ) (env : SemEnv Value) (expr : AstHOL.Exp),
      isClockIoMono (fun state => evaluate state env [expr]) st)
    (st : State σ) (env : SemEnv Value) (ds : List Dec) :
    isClockIoMono (fun state => evaluateDecs state env ds) st := by
  cases ds with
  | nil => exact clockIoDecs_nil st env
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply clockIoDecs_cons st env first second tail (clockIoDecsFromExpr exprIH st env [first])
      intro next inner _
      exact clockIoDecsFromExpr exprIH next (extendDecEnv inner env) (second :: tail)
    | nil =>
      cases first with
      | dtabbrev loc vars name typ => exact clockIoDecs_tabbrev st env loc vars name typ
      | dexn loc name types => exact clockIoDecs_exn st env loc name types
      | dtype loc types => exact clockIoDecs_type st env loc types
      | denv name => exact clockIoDecs_env st env name
      | dletrec loc funs => exact clockIoDecs_letrec st env loc funs
      | dmod name decs => exact clockIoDecs_mod st env name decs (clockIoDecsFromExpr exprIH st env decs)
      | dlet loc pat expr => exact clockIoDecs_let st env loc pat expr (exprIH st env expr)
      | dlocal localDecs decs =>
        apply clockIoDecs_local st env localDecs decs (clockIoDecsFromExpr exprIH st env localDecs)
        intro next inner _
        exact clockIoDecsFromExpr exprIH next (extendDecEnv inner env) decs
termination_by sizeOf ds
decreasing_by
  all_goals simp_wf
  all_goals try (have := decSize_pos second)
  all_goals try (have := listSize_pos tail)
  all_goals try omega

end Flapjack.EvaluateProps

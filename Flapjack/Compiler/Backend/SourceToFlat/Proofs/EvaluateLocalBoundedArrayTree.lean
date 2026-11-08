import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvalApp
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedApp
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedArray
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedData
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedPrimitive
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedMatch
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalCall

/-! Bounded expression composition including arrays and function calls. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

private inductive LocalEnvBoundedArrayExpression : AstHOL.Exp → Prop where
  | simpleApp (op : Op) (args : List AstHOL.Exp) : op ≠ .aallocEmpty → op ≠ .eval →
      op ≠ .envId → getOpClass op = .simple →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) → LocalEnvBoundedArrayExpression (.app op args)
  | base (expr : AstHOL.Exp) : LocalEnvExpression expr → LocalEnvBoundedArrayExpression expr
  | eval (args : List AstHOL.Exp) : (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression (.app .eval args)
  | call (left right : AstHOL.Exp) : LocalEnvBoundedArrayExpression left → LocalEnvBoundedArrayExpression right →
      LocalEnvBoundedArrayExpression (.app .opapp [left, right])
  | callBadArity (args : List AstHOL.Exp) : args.length ≠ 2 →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) → LocalEnvBoundedArrayExpression (.app .opapp args)
  | arrayEmpty (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app .aallocEmpty [body])
  | arrayEmptyBadArity (args : List AstHOL.Exp) : args.length ≠ 1 →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) → LocalEnvBoundedArrayExpression (.app .aallocEmpty args)
  | forceThunk (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app (.thunkOp .forceThunk) [body])
  | forceThunkBadArity (args : List AstHOL.Exp) : args.length ≠ 1 →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression (.app (.thunkOp .forceThunk) args)
  | envId (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.app .envId [body])
  | envIdBadArity (args : List AstHOL.Exp) : args.length ≠ 1 →
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) → LocalEnvBoundedArrayExpression (.app .envId args)
  | tuple (args : List AstHOL.Exp) : (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) →
      LocalEnvBoundedArrayExpression (.con none args)
  | constructor (id : Ident ModN ConN) (args : List AstHOL.Exp) :
      (∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) → LocalEnvBoundedArrayExpression (.con (some id) args)
  | mat (body : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp)) : LocalEnvBoundedArrayExpression body →
      (∀ pattern rowBody, (pattern, rowBody) ∈ rows → LocalEnvBoundedArrayExpression rowBody) →
      LocalEnvBoundedArrayExpression (.mat body rows)
  | handle (body : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp)) : LocalEnvBoundedArrayExpression body →
      (∀ pattern rowBody, (pattern, rowBody) ∈ rows → LocalEnvBoundedArrayExpression rowBody) →
      LocalEnvBoundedArrayExpression (.handle body rows)
  | letrec (funs : List (VarN × VarN × AstHOL.Exp)) (body : AstHOL.Exp) :
      LocalEnvBoundedArrayExpression body → LocalEnvBoundedArrayExpression (.letrec funs body)
  | letNamed (name : VarN) (first body : AstHOL.Exp) : LocalEnvBoundedArrayExpression first →
      LocalEnvBoundedArrayExpression body → LocalEnvBoundedArrayExpression (.let_ (some name) first body)
  | letAnonymous (first body : AstHOL.Exp) : LocalEnvBoundedArrayExpression first → LocalEnvBoundedArrayExpression body →
      LocalEnvBoundedArrayExpression (.let_ none first body)
  | if_ (cond yes no : AstHOL.Exp) : LocalEnvBoundedArrayExpression cond → LocalEnvBoundedArrayExpression yes →
      LocalEnvBoundedArrayExpression no → LocalEnvBoundedArrayExpression (.if_ cond yes no)
  | log (op : Lop) (left right : AstHOL.Exp) : LocalEnvBoundedArrayExpression left → LocalEnvBoundedArrayExpression right →
      LocalEnvBoundedArrayExpression (.log op left right)
  | raise_ (body : AstHOL.Exp) : LocalEnvBoundedArrayExpression body → LocalEnvBoundedArrayExpression (.raise body)
  | tannot (expr : AstHOL.Exp) (typ : AstT) : LocalEnvBoundedArrayExpression expr → LocalEnvBoundedArrayExpression (.tannot expr typ)
  | lannot (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) : LocalEnvBoundedArrayExpression expr →
      LocalEnvBoundedArrayExpression (.lannot expr loc)

/-- Function applications are covered for every operand count. -/
private theorem callExpression_covered (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app .opapp args) := by
  cases args with
  | nil => exact .callBadArity [] (by simp) each
  | cons first rest =>
    have firstCovered := each first (by simp)
    cases rest with
    | nil => exact .callBadArity [first] (by simp) each
    | cons second rest =>
      have secondCovered := each second (by simp)
      cases rest with
      | nil => exact .call first second firstCovered secondCovered
      | cons third rest => exact .callBadArity (first :: second :: third :: rest) (by simp) each

/-- Thunk forcing is covered for every operand count. -/
private theorem forceThunkExpression_covered (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app (.thunkOp .forceThunk) args) := by
  cases args with
  | nil => exact .forceThunkBadArity [] (by simp) each
  | cons first rest =>
    have firstCovered := each first (by simp)
    cases rest with
    | nil => exact .forceThunk first firstCovered
    | cons second rest => exact .forceThunkBadArity (first :: second :: rest) (by simp) each

/-- Environment-ID applications are covered for every operand count. -/
private theorem envIdExpression_covered (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app .envId args) := by
  cases args with
  | nil => exact .envIdBadArity [] (by simp) each
  | cons first rest =>
    have firstCovered := each first (by simp)
    cases rest with
    | nil => exact .envId first firstCovered
    | cons second rest => exact .envIdBadArity (first :: second :: rest) (by simp) each

/-- Empty-array allocation is covered for every operand count. -/
private theorem arrayEmptyExpression_covered (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app .aallocEmpty args) := by
  cases args with
  | nil => exact .arrayEmptyBadArity [] (by simp) each
  | cons first rest =>
    have firstCovered := each first (by simp)
    cases rest with
    | nil => exact .arrayEmpty first firstCovered
    | cons second rest => exact .arrayEmptyBadArity (first :: second :: rest) (by simp) each

/-- Every application is either a special evaluator case or a simple operation. -/
private theorem applicationExpression_covered (op : Op) (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedArrayExpression expr) :
    LocalEnvBoundedArrayExpression (.app op args) := by
  by_cases hEmpty : op = .aallocEmpty
  · subst op; exact arrayEmptyExpression_covered args each
  by_cases hEval : op = .eval
  · subst op; exact .eval args each
  by_cases hEnv : op = .envId
  · subst op; exact envIdExpression_covered args each
  by_cases hCall : op = .opapp
  · subst op; exact callExpression_covered args each
  by_cases hForce : op = .thunkOp .forceThunk
  · subst op; exact forceThunkExpression_covered args each
  have simple : getOpClass op = .simple := by
    cases op <;> simp_all [getOpClass]
  exact .simpleApp op args hEmpty hEval hEnv simple each

/-- Every source expression has a structural coverage derivation. The
simulation itself still depends on the preliminary factored relations. -/
private theorem allExpressions_covered : (expr : AstHOL.Exp) → LocalEnvBoundedArrayExpression expr
  | .raise body => .raise_ body (allExpressions_covered body)
  | .handle body rows => .handle body rows (allExpressions_covered body)
      (fun pat row _member => allExpressions_covered row)
  | .lit lit => .base _ (.literal lit)
  | .con none args => .tuple args (fun expr _member => allExpressions_covered expr)
  | .con (some id) args => .constructor id args (fun expr _member => allExpressions_covered expr)
  | .var id => .base _ (.variable_ id)
  | .fn name body => .base _ (.function_ name body)
  | .app op args => applicationExpression_covered op args (fun expr _member => allExpressions_covered expr)
  | .log op left right => .log op left right (allExpressions_covered left) (allExpressions_covered right)
  | .if_ cond yes no => .if_ cond yes no (allExpressions_covered cond)
      (allExpressions_covered yes) (allExpressions_covered no)
  | .mat body rows => .mat body rows (allExpressions_covered body)
      (fun pat row _member => allExpressions_covered row)
  | .let_ none first body => .letAnonymous first body (allExpressions_covered first) (allExpressions_covered body)
  | .let_ (some name) first body => .letNamed name first body (allExpressions_covered first) (allExpressions_covered body)
  | .letrec funs body => .letrec funs body (allExpressions_covered body)
  | .tannot body typ => .tannot body typ (allExpressions_covered body)
  | .lannot body loc => .lannot body loc (allExpressions_covered body)
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals have h := List.sizeOf_lt_of_mem _member
  all_goals try simp only [Prod.mk.sizeOf_spec] at h
  all_goals omega

/-- Covered expressions satisfy the preliminary arbitrary-local hypothesis;
the relations remain pending HOL correspondence review. -/
private theorem localEnvBounded_arrayTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (calledIH : LocalEnvClockIH (F := F) interp transform limit)
    (decsIH : FactoredDecClockIH (F := F) interp transform limit)
    (expr : AstHOL.Exp) (covered : LocalEnvBoundedArrayExpression expr) : LocalEnvBoundedIH (F := F) interp transform limit expr := by
  induction covered with
  | base expr covered =>
    cases covered with
    | literal lit => exact localEnvBounded_literal interp transform limit lit
    | variable_ id => exact localEnvBounded_variable interp transform limit id
    | function_ name body => exact localEnvBounded_function interp transform limit name body
  | simpleApp op args notEmpty notEval notEnvId simple _ ih =>
    exact localEnvBounded_simpleApp interp transform limit op notEmpty notEval notEnvId simple args ih
  | eval args _ ih => exact localEnvBounded_eval interp transform limit decsIH args ih
  | call left right _ _ leftIH rightIH =>
    exact localEnvBounded_opapp interp transform limit calledIH left right leftIH rightIH
  | callBadArity args badArity _ ih => exact localEnvBounded_opapp_badArity interp transform limit args badArity ih
  | arrayEmpty body _ ih => exact localEnvBounded_aallocEmpty interp transform limit body ih
  | arrayEmptyBadArity args badArity _ ih =>
    exact localEnvBounded_aallocEmpty_badArity interp transform limit args badArity ih
  | forceThunk body _ ih => exact localEnvBounded_forceThunk interp transform limit calledIH body ih
  | forceThunkBadArity args badArity _ ih =>
    exact localEnvBounded_forceThunk_badArity interp transform limit args badArity ih
  | envId body _ ih => exact localEnvBounded_envId interp transform limit body ih
  | envIdBadArity args badArity _ ih => exact localEnvBounded_envId_badArity interp transform limit args badArity ih
  | tuple args _ ih => exact localEnvBounded_tuple interp transform limit args ih
  | constructor id args _ ih => exact localEnvBounded_constructor interp transform limit id args ih
  | mat body rows _ _ bodyIH rowsIH => exact localEnvBounded_mat interp transform limit body rows bodyIH rowsIH
  | handle body rows _ _ bodyIH rowsIH => exact localEnvBounded_handle interp transform limit body rows bodyIH rowsIH
  | letrec funs body _ ih => exact localEnvBounded_letrec interp transform limit funs body ih
  | letNamed name first body _ _ firstIH bodyIH => exact localEnvBounded_let_named interp transform limit name first body firstIH bodyIH
  | letAnonymous first body _ _ firstIH bodyIH => exact localEnvBounded_let_anonymous interp transform limit first body firstIH bodyIH
  | if_ cond yes no _ _ _ condIH yesIH noIH => exact localEnvBounded_if interp transform limit cond yes no condIH yesIH noIH
  | log op left right _ _ leftIH rightIH => exact localEnvBounded_log interp transform limit op left right leftIH rightIH
  | raise_ body _ ih => exact localEnvBounded_raise interp transform limit body ih
  | tannot expr typ _ ih => exact localEnvBounded_tannot interp transform limit expr typ ih
  | lannot expr loc _ ih => exact localEnvBounded_lannot interp transform limit expr loc ih




/-- Every expression satisfies the bounded simulation from the expression and
declaration induction hypotheses at smaller clocks. -/
theorem localEnvBounded_arrayTree_of_smaller {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (smallerExprs : ∀ n, n < limit → ∀ expr, LocalEnvBoundedIH (F := F) interp transform n expr)
    (smallerDecs : ∀ n, n < limit → ∀ decs, FactoredDecBoundedIH (F := F) interp transform n decs)
    (expr : AstHOL.Exp) :
    LocalEnvBoundedIH (F := F) interp transform limit expr :=
  localEnvBounded_arrayTree interp transform limit
    (localEnvClockIH_of_smaller interp transform limit smallerExprs)
    (factoredDecClockIH_of_smaller interp transform limit smallerDecs) expr (allExpressions_covered expr)

end Flapjack.Compiler.Backend.SourceToFlat

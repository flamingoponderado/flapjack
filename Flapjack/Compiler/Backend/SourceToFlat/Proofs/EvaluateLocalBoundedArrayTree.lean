module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvalApp
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedApp
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedArray
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedData
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedPrimitive
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedMatch
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalCall

@[expose] public section

/-! A total expression induction tree for bounded simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Dispatch unary operations using their actual singleton and bad-arity cases. -/
private theorem unaryExpression_bounded {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat)
    (op : Op)
    (single : ∀ body, LocalEnvBoundedIH (F := F) interp transform limit body → LocalEnvBoundedIH (F := F) interp transform limit (.app op [body]))
    (other : ∀ args : List AstHOL.Exp, args.length ≠ 1 →
      (∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) → LocalEnvBoundedIH (F := F) interp transform limit (.app op args))
    (args : List AstHOL.Exp) (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app op args) := by
  by_cases one : args.length = 1
  · obtain ⟨body, rfl⟩ := List.length_eq_one_iff.mp one
    exact single body (each body (by simp))
  · exact other args one each

/-- Dispatch the source application's evaluator cases directly. -/
private theorem applicationExpression_bounded {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat)
    (calledIH : LocalEnvClockIH (F := F) interp transform limit)
    (decsIH : FactoredDecClockIH (F := F) interp transform limit)
    (op : Op) (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app op args) := by
  by_cases hEmpty : op = .aallocEmpty
  · subst op
    exact unaryExpression_bounded interp transform limit _
      (localEnvBounded_aallocEmpty interp transform limit)
      (localEnvBounded_aallocEmpty_badArity interp transform limit) args each
  by_cases hEval : op = .eval
  · subst op; exact localEnvBounded_eval interp transform limit decsIH args each
  by_cases hEnv : op = .envId
  · subst op
    exact unaryExpression_bounded interp transform limit _
      (localEnvBounded_envId interp transform limit)
      (localEnvBounded_envId_badArity interp transform limit) args each
  by_cases hCall : op = .opapp
  · subst op
    cases args with
    | nil => exact localEnvBounded_opapp_badArity interp transform limit [] (by simp) each
    | cons first rest =>
      have firstIH := each first (by simp)
      cases rest with
      | nil => exact localEnvBounded_opapp_badArity interp transform limit [first] (by simp) each
      | cons second rest =>
        have secondIH := each second (by simp)
        cases rest with
        | nil => exact localEnvStep_opapp interp transform limit calledIH first second firstIH secondIH
        | cons third rest =>
          exact localEnvBounded_opapp_badArity interp transform limit
            (first :: second :: third :: rest) (by simp) each
  by_cases hForce : op = .thunkOp .forceThunk
  · subst op
    exact unaryExpression_bounded interp transform limit _
      (localEnvBounded_forceThunk interp transform limit calledIH)
      (localEnvBounded_forceThunk_badArity interp transform limit) args each
  have simple : getOpClass op = .simple := by
    cases op <;> simp_all [getOpClass]
  exact localEnvBounded_simpleApp interp transform limit op hEmpty hEval hEnv simple args each

/-- Structural source-expression induction using the existing bounded cases.
The factored simulation relations retain their pending HOL correspondence status. -/
private theorem localEnvBounded_arrayTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat)
    (calledIH : LocalEnvClockIH (F := F) interp transform limit)
    (decsIH : FactoredDecClockIH (F := F) interp transform limit)
    (expr : AstHOL.Exp) : LocalEnvBoundedIH (F := F) interp transform limit expr := go expr
where
  go : (expr : AstHOL.Exp) → LocalEnvBoundedIH (F := F) interp transform limit expr
  | .raise body => localEnvBounded_raise interp transform limit body (go body)
  | .handle body rows => localEnvBounded_handle interp transform limit body rows (go body)
      (fun pat row _member => go row)
  | .lit lit => localEnvBounded_literal interp transform limit lit
  | .con none args => localEnvBounded_tuple interp transform limit args (fun expr _member => go expr)
  | .con (some id) args => localEnvBounded_constructor interp transform limit id args (fun expr _member => go expr)
  | .var id => localEnvBounded_variable interp transform limit id
  | .fn name body => localEnvBounded_function interp transform limit name body
  | .app op args => applicationExpression_bounded interp transform limit calledIH decsIH op args
      (fun expr _member => go expr)
  | .log op left right => localEnvBounded_log interp transform limit op left right (go left) (go right)
  | .if_ cond yes no => localEnvBounded_if interp transform limit cond yes no (go cond) (go yes) (go no)
  | .mat body rows => localEnvBounded_mat interp transform limit body rows (go body)
      (fun pat row _member => go row)
  | .let_ none first body => localEnvBounded_let_anonymous interp transform limit first body (go first) (go body)
  | .let_ (some name) first body => localEnvBounded_let_named interp transform limit name first body (go first) (go body)
  | .letrec funs body => localEnvBounded_letrec interp transform limit funs body (go body)
  | .tannot body typ => localEnvBounded_tannot interp transform limit body typ (go body)
  | .lannot body loc => localEnvBounded_lannot interp transform limit body loc (go body)
  termination_by expr => sizeOf expr
  decreasing_by
    all_goals simp_wf
    all_goals try omega
    all_goals have h := List.sizeOf_lt_of_mem _member
    all_goals try simp only [Prod.mk.sizeOf_spec] at h
    all_goals omega

/-- Every expression satisfies the bounded simulation from the expression and
declaration induction hypotheses at smaller clocks. -/
theorem localEnvBounded_arrayTree_of_smaller {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (smallerExprs : ∀ n, n < limit → ∀ expr, LocalEnvBoundedIH (F := F) interp transform n expr)
    (smallerDecs : ∀ n, n < limit → ∀ decs, FactoredDecBoundedIH (F := F) interp transform n decs)
    (expr : AstHOL.Exp) :
    LocalEnvBoundedIH (F := F) interp transform limit expr :=
  localEnvBounded_arrayTree interp transform limit
    smallerExprs
    smallerDecs expr

end Flapjack.Compiler.Backend.SourceToFlat

module

public import Flapjack.EvaluateProps.NoEvalApp
public import Flapjack.EvaluateHOL.Induction

@[expose] public section

/-! Complete mutual simulation from an absent Eval state for the source evaluator. -/
namespace Flapjack.EvaluateProps
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL



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
  apply fullEvaluateInd (NoEvalExpsAt es) (NoEvalMatchAt es) (NoEvalDecsAt es)
  exact ⟨evalNoEval_ExpsNil es, evalNoEval_ExpsCons es, evalNoEval_Lit es,
    evalNoEval_Raise es, evalNoEval_Handle es, evalNoEval_Con es,
    evalNoEval_Var es, evalNoEval_Fn es, evalNoEval_App es,
    evalNoEval_Log es, evalNoEval_If es, evalNoEval_Mat es,
    evalNoEval_Let es, evalNoEval_Letrec es, evalNoEval_Tannot es,
    evalNoEval_Lannot es, evalNoEval_MatchNil es, evalNoEval_MatchCons es,
    evalNoEval_DecsNil es, evalNoEval_DecsCons es, evalNoEval_Dlet es,
    evalNoEval_Dletrec es, evalNoEval_Dtype es, evalNoEval_Dtabbrev es,
    evalNoEval_Denv es, evalNoEval_Dexn es, evalNoEval_Dmod es,
    evalNoEval_Dlocal es⟩

end Flapjack.EvaluateProps

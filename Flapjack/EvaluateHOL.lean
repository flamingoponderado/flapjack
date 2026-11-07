import Flapjack.SemanticPrimitivesHOL.Eval
import Flapjack.SemanticPrimitivesHOL.ApplyNumeric

/-! Initial definitions from the CakeML source evaluator. Its mutually recursive
definition is in `EvaluateHOL.Definition` and remains pending source review;
the compiler correctness theorem is not yet ported. -/
namespace Flapjack.EvaluateHOL
open Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

@[hol "cakeml/semantics/evaluateScript.sml" "fix_clock_def"]
def fixClock {σ τ α : Type} (initial : State σ) (output : State τ × α) : State τ × α :=
  ({ output.1 with clock := min output.1.clock initial.clock }, output.2)

@[hol "cakeml/semantics/evaluateScript.sml" "dec_clock_def"]
def decClock {σ : Type} (state : State σ) : State σ :=
  { state with clock := state.clock - 1 }

/-- Proof-side Eval dispatch; source value equality currently uses classical
decidability and is therefore not an executable compiler implementation. -/
@[hol "cakeml/semantics/evaluateScript.sml" "do_eval_res_def"]
noncomputable def doEvalRes {σ β : Type} (values : List Value) (state : State σ) :
    State σ × Result (SemEnv Value × List AstHOL.Dec) β :=
  match doEval values state.evalState with
  | none => (state, .err (.abort .typeError))
  | some (env, decs, evalState) => ({ state with evalState := evalState }, .val (env, decs))

@[hol "cakeml/semantics/evaluateScript.sml" "list_result_def"]
def listResult {α β : Type} : Result α β → Result (List α) β
  | .val value => .val [value]
  | .err error => .err error

@[hol "cakeml/semantics/evaluateScript.sml" "sing_env_def"]
def singleEnv (name : VarN) (value : Value) : SemEnv Value :=
  { v := nsBind name value nsEmpty, c := nsEmpty }

@[hol "cakeml/semantics/evaluateScript.sml" "fix_clock_IMP"]
theorem fixClockImp {σ τ α : Type} (state : State σ) (state' : State τ) (result : α) (output : State τ × α)
    (h : fixClock state output = (state', result)) : state'.clock ≤ state.clock := by
  rcases output with ⟨other, value⟩
  simp only [fixClock, Prod.mk.injEq] at h
  rcases h with ⟨h, _⟩
  subst state'
  exact Nat.min_le_right _ _

@[hol "cakeml/semantics/evaluateScript.sml" "fix_clock_do_eval_res"]
theorem fixClockDoEvalRes {σ β : Type} (values : List Value) (state : State σ) :
    fixClock state (doEvalRes (β := β) values state) = doEvalRes values state := by
  cases h : doEval values state.evalState with
  | none => simp [doEvalRes, h, fixClock]
  | some result =>
    rcases result with ⟨env, decs, evalState⟩
    simp [doEvalRes, h, fixClock]

end Flapjack.EvaluateHOL

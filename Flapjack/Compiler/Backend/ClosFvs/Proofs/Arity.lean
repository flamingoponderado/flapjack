module

public import Flapjack.Compiler.Backend.ClosFvs.Source
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity
@[expose] public section

/-! Application-arity preservation by free-variable removal. -/
namespace Flapjack.Compiler.Backend.ClosFvs
open ClosLang ClosProps
mutual
/-- Flapjack induction infrastructure for the HOL list theorem. -/
private theorem sing (expression : Exp) (bound limit : Nat) :
    obeysMaxApp limit (removeSing bound expression) ↔ obeysMaxApp limit expression := by
  cases expression with
  | var trace n => simp [removeSing, obeysMaxApp]; split <;> simp [obeysMaxApp, obeysMaxAppList]
  | ifThenElse trace condition yes no =>
    simp [removeSing, obeysMaxApp, sing condition, sing yes, sing no]
  | «let» trace bindings body => simp [removeSing, obeysMaxApp, many bindings, sing body]
  | raise trace body => simp [removeSing, obeysMaxApp, sing body]
  | handle trace body handler => simp [removeSing, obeysMaxApp, sing body, sing handler]
  | tick trace body => simp [removeSing, obeysMaxApp, sing body]
  | call trace ticks location args => simp [removeSing, obeysMaxApp, many args]
  | app trace location function args =>
    simp [removeSing, obeysMaxApp, removeList_length, sing function, many args]
  | fn name location vars arity body => simp [removeSing, obeysMaxApp, sing body]
  | letrec names location vars functions body =>
    simp [removeSing, obeysMaxApp, funs functions, sing body]
  | op trace op args => simp [removeSing, obeysMaxApp, many args]
termination_by sizeOf expression
/-- Flapjack list induction infrastructure for the HOL theorem. -/
private theorem many (expressions : List Exp) (bound limit : Nat) :
    obeysMaxAppList limit (removeList bound expressions) ↔ obeysMaxAppList limit expressions := by
  cases expressions with
  | nil => simp [removeList, obeysMaxAppList]
  | cons first rest => simp [removeList, obeysMaxAppList, sing first, many rest]
termination_by sizeOf expressions
/-- Flapjack recursive-function induction infrastructure for the HOL theorem. -/
private theorem funs (functions : List (Nat × Exp)) (count captured limit : Nat) :
    obeysMaxAppFuns limit (removeFuns count captured functions) ↔ obeysMaxAppFuns limit functions := by
  cases functions with
  | nil => simp [removeFuns, obeysMaxAppFuns]
  | cons first rest =>
    cases first with
    | mk arity body => simp [removeFuns, obeysMaxAppFuns, sing body, funs rest]
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

/-- Free-variable removal preserves the full application-arity predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "remove_fvs_obeys_max_app"]
theorem removeSource_obeysMaxApp (limit bound : Nat) (expressions : List Exp) :
    (∀ e ∈ removeSource bound expressions, obeysMaxApp limit e) ↔
      ∀ e ∈ expressions, obeysMaxApp limit e := by
  simpa only [removeSource_eq_list, ← obeysMaxAppList_iff] using many expressions bound limit

end Flapjack.Compiler.Backend.ClosFvs

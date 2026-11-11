module

public import Flapjack.Compiler.Backend.ClosFvs.Source
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity
@[expose] public section

/-! Label preservation by free-variable removal. -/
namespace Flapjack.Compiler.Backend.ClosFvs
open ClosLang ClosProps
mutual
/-- Flapjack induction infrastructure for the HOL list theorem. -/
private theorem sing (expression : Exp) (bound : Nat) :
    noLabels (removeSing bound expression) ↔ noLabels expression := by
  cases expression with
  | var trace n => simp [removeSing, noLabels]; split <;> simp [noLabels, noLabelsList]
  | ifThenElse trace condition yes no =>
    simp [removeSing, noLabels, sing condition, sing yes, sing no]
  | «let» trace bindings body => simp [removeSing, noLabels, many bindings, sing body]
  | raise trace body => simp [removeSing, noLabels, sing body]
  | handle trace body handler => simp [removeSing, noLabels, sing body, sing handler]
  | tick trace body => simp [removeSing, noLabels, sing body]
  | call trace ticks location args => simp [removeSing, noLabels, many args]
  | app trace location function args =>
    simp [removeSing, noLabels, sing function, many args]
  | fn name location vars arity body => simp [removeSing, noLabels, sing body]
  | letrec names location vars functions body =>
    simp [removeSing, noLabels, funs functions, sing body]
  | op trace op args => simp [removeSing, noLabels, many args]
termination_by sizeOf expression
/-- Flapjack list induction infrastructure for the HOL theorem. -/
private theorem many (expressions : List Exp) (bound : Nat) :
    noLabelsList (removeList bound expressions) ↔ noLabelsList expressions := by
  cases expressions with
  | nil => simp [removeList, noLabelsList]
  | cons first rest => simp [removeList, noLabelsList, sing first, many rest]
termination_by sizeOf expressions
/-- Flapjack recursive-function induction infrastructure for the HOL theorem. -/
private theorem funs (functions : List (Nat × Exp)) (count captured : Nat) :
    noLabelsFuns (removeFuns count captured functions) ↔ noLabelsFuns functions := by
  cases functions with
  | nil => simp [removeFuns, noLabelsFuns]
  | cons first rest =>
    cases first with
    | mk arity body => simp [removeFuns, noLabelsFuns, sing body, funs rest]
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

/-- Free-variable removal preserves the full label-free predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "remove_fvs_no_Labels"]
theorem removeSource_noLabels (bound : Nat) (expressions : List Exp) :
    (∀ e ∈ removeSource bound expressions, noLabels e) ↔
      ∀ e ∈ expressions, noLabels e := by
  simpa only [removeSource_eq_list, ← noLabelsList_iff] using many expressions bound

end Flapjack.Compiler.Backend.ClosFvs

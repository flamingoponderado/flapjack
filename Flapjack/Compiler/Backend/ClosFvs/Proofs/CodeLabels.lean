module

public import Flapjack.Compiler.Backend.ClosFvs.Source
public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLabels

@[expose] public section

/-! Code-label preservation by closure free-variable removal. -/
namespace Flapjack.Compiler.Backend.ClosFvs
open ClosLang ClosProps

mutual
private theorem removeSing_codeLabels (e : Exp) (bound : Nat) :
    getCodeLabels (removeSing bound e) = getCodeLabels e := by
  cases e with
  | var t n => by_cases inside : n < bound <;> simp [removeSing, inside, getCodeLabels, getCodeLabelsList, assignGetCodeLabel]
  | ifThenElse t x y z => simp [removeSing, getCodeLabels, removeSing_codeLabels x, removeSing_codeLabels y, removeSing_codeLabels z]
  | «let» t xs body => simp [removeSing, getCodeLabels, removeList_codeLabels xs, removeSing_codeLabels body]
  | raise t x => simp [removeSing, getCodeLabels, removeSing_codeLabels x]
  | handle t x y => simp [removeSing, getCodeLabels, removeSing_codeLabels x, removeSing_codeLabels y]
  | tick t x => simp [removeSing, getCodeLabels, removeSing_codeLabels x]
  | call t ticks dest xs => simp [removeSing, getCodeLabels, removeList_codeLabels xs]
  | app t loc x xs => cases loc <;> simp [removeSing, getCodeLabels, removeSing_codeLabels x, removeList_codeLabels xs]
  | fn name loc vs arity body => cases loc <;> simp [removeSing, getCodeLabels, removeSing_codeLabels body]
  | letrec names loc vs fns body =>
    cases loc <;> simp [removeSing, getCodeLabels, removeFuns_codeLabels fns,
      removeSing_codeLabels body, removeFuns_length]
  | op t op xs => simp [removeSing, getCodeLabels, removeList_codeLabels xs]
termination_by sizeOf e

private theorem removeList_codeLabels (xs : List Exp) (bound : Nat) :
    getCodeLabelsList (removeList bound xs) = getCodeLabelsList xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [removeList, getCodeLabelsList, removeSing_codeLabels x, removeList_codeLabels xs]
termination_by sizeOf xs

private theorem removeFuns_codeLabels (fns : List (Nat × Exp)) (count captured : Nat) :
    getCodeLabelsFuns (removeFuns count captured fns) = getCodeLabelsFuns fns := by
  cases fns with
  | nil => rfl
  | cons pair fns => cases pair with
    | mk arity body => simp [removeFuns, getCodeLabelsFuns, removeSing_codeLabels body, removeFuns_codeLabels fns]
termination_by sizeOf fns
decreasing_by all_goals subst_vars; simp_wf; omega
end

/-- Free-variable removal preserves each expression's code-label set. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "get_code_labels_remove_fvs"]
theorem get_code_labels_remove_fvs (n : Nat) (es : List Exp) :
    (removeSource n es).map getCodeLabels = es.map getCodeLabels := by
  rw [removeSource_eq_list]
  induction es with
  | nil => rfl
  | cons e es ih => simp [removeList, removeSing_codeLabels, ih]

end Flapjack.Compiler.Backend.ClosFvs

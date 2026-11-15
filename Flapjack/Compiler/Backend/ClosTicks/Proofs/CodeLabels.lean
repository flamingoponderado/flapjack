import Flapjack.Compiler.Backend.ClosTicks.Source
import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLabels

/-! Code-label preservation by the source tick-removal pass. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open ClosLang ClosProps

mutual
/-- Structural induction helper; HOL proves the list theorem directly. -/
private theorem removeSing_codeLabels (e : Exp) :
    getCodeLabels (removeSing e) = getCodeLabels e := by
  cases e with
  | var t n => simp [removeSing, getCodeLabels]
  | ifThenElse t x y z => simp [removeSing, getCodeLabels, removeSing_codeLabels x, removeSing_codeLabels y, removeSing_codeLabels z]
  | «let» t xs body => simp [removeSing, getCodeLabels, removeList_codeLabels xs, removeSing_codeLabels body]
  | raise t x => simp [removeSing, getCodeLabels, removeSing_codeLabels x]
  | handle t x y => simp [removeSing, getCodeLabels, removeSing_codeLabels x, removeSing_codeLabels y]
  | tick t x => simp [removeSing, getCodeLabels, removeSing_codeLabels x]
  | call t ticks dest xs => simp [removeSing, getCodeLabels, removeList_codeLabels xs]
  | app t loc x xs => cases loc <;> simp [removeSing, getCodeLabels, removeSing_codeLabels x, removeList_codeLabels xs]
  | fn name loc vs arity body => cases loc <;> simp [removeSing, getCodeLabels, removeSing_codeLabels body]
  | letrec names loc vs fns body =>
    have length : (removeFuns fns).length = fns.length := by simp [removeFuns_eq_map]
    cases loc <;> simp [removeSing, getCodeLabels, removeFuns_codeLabels fns,
      removeSing_codeLabels body, length]
  | op t op xs => simp [removeSing, getCodeLabels, removeList_codeLabels xs]
termination_by sizeOf e

/-- List case of the structural induction; no separate HOL declaration. -/
private theorem removeList_codeLabels (xs : List Exp) :
    getCodeLabelsList (removeList xs) = getCodeLabelsList xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [removeList, getCodeLabelsList, removeSing_codeLabels x, removeList_codeLabels xs]
termination_by sizeOf xs

/-- Recursive-function case of the structural induction; no separate HOL declaration. -/
private theorem removeFuns_codeLabels (fns : List (Nat × Exp)) :
    getCodeLabelsFuns (removeFuns fns) = getCodeLabelsFuns fns := by
  cases fns with
  | nil => rfl
  | cons pair fns => cases pair with
    | mk arity body => simp [removeFuns, getCodeLabelsFuns, removeSing_codeLabels body, removeFuns_codeLabels fns]
termination_by sizeOf fns
decreasing_by all_goals (subst_vars; simp_wf; omega)
end

/-- Tick removal preserves each expression's code-label set. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_code_labels"]
theorem removeSource_codeLabels (xs : List Exp) :
    (removeSource xs).map getCodeLabels = xs.map getCodeLabels := by
  rw [removeSource_eq_list]
  induction xs with
  | nil => rfl
  | cons e es ih => simp [removeList, removeSing_codeLabels, ih]

end Flapjack.Compiler.Backend.ClosTicks

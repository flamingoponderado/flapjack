module

public import Flapjack.Compiler.Backend.ClosTicks.Source
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity
@[expose] public section

/-! Label preservation by closure tick removal. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open ClosLang ClosProps
mutual
/-- Flapjack singleton induction infrastructure for the HOL list theorem. -/
private theorem sing (e : Exp) :
    noLabels (removeSing e) ↔ noLabels e := by
  cases e with
  | var t n => simp [removeSing, noLabels]
  | ifThenElse t x y z => simp [removeSing, noLabels, sing x, sing y, sing z]
  | «let» t xs body => simp [removeSing, noLabels, many xs, sing body]
  | raise t x => simp [removeSing, noLabels, sing x]
  | handle t x y => simp [removeSing, noLabels, sing x, sing y]
  | tick t x => simp [removeSing, noLabels, sing x]
  | call t ticks dest xs => simp [removeSing, noLabels, many xs]
  | app t loc x xs => simp [removeSing, noLabels, sing x, many xs]
  | fn name loc vs arity body => simp [removeSing, noLabels, sing body]
  | letrec names loc vs fns body => simp [removeSing, noLabels, funs fns, sing body]
  | op t op xs => simp [removeSing, noLabels, many xs]
termination_by sizeOf e
/-- Flapjack list induction infrastructure for the HOL theorem. -/
private theorem many (xs : List Exp) :
    noLabelsList (removeList xs) ↔ noLabelsList xs := by
  cases xs with
  | nil => simp [removeList, noLabelsList]
  | cons x xs => simp [removeList, noLabelsList, sing x, many xs]
termination_by sizeOf xs
/-- Flapjack recursive-function induction infrastructure for the HOL theorem. -/
private theorem funs (fns : List (Nat × Exp)) :
    noLabelsFuns (removeFuns fns) ↔ noLabelsFuns fns := by
  cases fns with
  | nil => simp [removeFuns, noLabelsFuns]
  | cons pair fns =>
    cases pair with
    | mk arity body => simp [removeFuns, noLabelsFuns, sing body, funs fns]
termination_by sizeOf fns
decreasing_by all_goals subst_vars; simp_wf <;> omega
end
/-- Tick removal preserves the absence of labels. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_no_Labels"]
theorem removeSource_noLabels (xs : List Exp)
    (h : ∀ e ∈ xs, noLabels e) : ∀ e ∈ removeSource xs, noLabels e := by
  rw [removeSource_eq_list]
  apply (noLabelsList_iff _).mp
  apply (many xs).mpr
  exact (noLabelsList_iff _).mpr h
end Flapjack.Compiler.Backend.ClosTicks

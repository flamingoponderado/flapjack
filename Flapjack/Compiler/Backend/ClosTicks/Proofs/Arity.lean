module

public import Flapjack.Compiler.Backend.ClosTicks.Source
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity
@[expose] public section

/-! Application-arity preservation by closure tick removal. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open ClosLang ClosProps
mutual
/-- Flapjack singleton induction infrastructure for the HOL list theorem. -/
private theorem sing (e : Exp) (limit : Nat) :
    obeysMaxApp limit (removeSing e) ↔ obeysMaxApp limit e := by
  cases e with
  | var t n => simp [removeSing, obeysMaxApp]
  | ifThenElse t x y z => simp [removeSing, obeysMaxApp, sing x, sing y, sing z]
  | «let» t xs body => simp [removeSing, obeysMaxApp, many xs, sing body]
  | raise t x => simp [removeSing, obeysMaxApp, sing x]
  | handle t x y => simp [removeSing, obeysMaxApp, sing x, sing y]
  | tick t x => simp [removeSing, obeysMaxApp, sing x]
  | call t ticks dest xs => simp [removeSing, obeysMaxApp, many xs]
  | app t loc x xs => simp [removeSing, obeysMaxApp, removeList_length, sing x, many xs]
  | fn name loc vs arity body => simp [removeSing, obeysMaxApp, sing body]
  | letrec names loc vs fns body => simp [removeSing, obeysMaxApp, funs fns, sing body]
  | op t op xs => simp [removeSing, obeysMaxApp, many xs]
termination_by sizeOf e
/-- Flapjack list induction infrastructure for the HOL theorem. -/
private theorem many (xs : List Exp) (limit : Nat) :
    obeysMaxAppList limit (removeList xs) ↔ obeysMaxAppList limit xs := by
  cases xs with
  | nil => simp [removeList, obeysMaxAppList]
  | cons x xs => simp [removeList, obeysMaxAppList, sing x, many xs]
termination_by sizeOf xs
/-- Flapjack recursive-function induction infrastructure for the HOL theorem. -/
private theorem funs (fns : List (Nat × Exp)) (limit : Nat) :
    obeysMaxAppFuns limit (removeFuns fns) ↔ obeysMaxAppFuns limit fns := by
  cases fns with
  | nil => simp [removeFuns, obeysMaxAppFuns]
  | cons pair fns =>
    cases pair with
    | mk arity body => simp [removeFuns, obeysMaxAppFuns, sing body, funs fns]
termination_by sizeOf fns
decreasing_by all_goals subst_vars; simp_wf <;> omega
end
/-- Tick removal preserves the input application-arity bound. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_obeys_max_app"]
theorem removeSource_obeysMaxApp (limit : Nat) (xs : List Exp)
    (h : ∀ e ∈ xs, obeysMaxApp limit e) : ∀ e ∈ removeSource xs, obeysMaxApp limit e := by
  rw [removeSource_eq_list]
  apply (obeysMaxAppList_iff limit _).mp
  apply (many xs limit).mpr
  exact (obeysMaxAppList_iff limit _).mpr h
end Flapjack.Compiler.Backend.ClosTicks

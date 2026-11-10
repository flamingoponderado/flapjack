module

public import Flapjack.Compiler.Backend.ClosTicks.Source
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations

@[expose] public section

/-! Closure annotation invariance for tick removal. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open ClosLang ClosProps

mutual
/-- Tick removal preserves the annotation condition on one expression. -/
theorem removeSing_varsNone (e : Exp) : fnVarsNoneExp (removeSing e) ↔ fnVarsNoneExp e := by
  cases e with
  | var t n => simp [removeSing, fnVarsNoneExp]
  | ifThenElse t x y z => simp [removeSing, fnVarsNoneExp, removeSing_varsNone x, removeSing_varsNone y, removeSing_varsNone z]
  | «let» t xs body => simp [removeSing, fnVarsNoneExp, removeList_varsNone xs, removeSing_varsNone body]
  | raise t x => simp [removeSing, fnVarsNoneExp, removeSing_varsNone x]
  | handle t x y => simp [removeSing, fnVarsNoneExp, removeSing_varsNone x, removeSing_varsNone y]
  | tick t x => simp [removeSing, fnVarsNoneExp, removeSing_varsNone x]
  | call t ticks dest xs => simp [removeSing, fnVarsNoneExp, removeList_varsNone xs]
  | app t loc x xs => simp [removeSing, fnVarsNoneExp, removeSing_varsNone x, removeList_varsNone xs]
  | fn name loc vs arity body => simp [removeSing, fnVarsNoneExp, removeSing_varsNone body]
  | letrec names loc vs fns body => simp [removeSing, fnVarsNoneExp, removeFuns_varsNone fns, removeSing_varsNone body]
  | op t op xs => simp [removeSing, fnVarsNoneExp, removeList_varsNone xs]
termination_by sizeOf e

/-- Tick removal preserves absent closure-capture annotations. -/
theorem removeList_varsNone (xs : List Exp) : everyFnVarsNone (removeList xs) ↔ everyFnVarsNone xs := by
  cases xs with
  | nil => simp [removeList, everyFnVarsNone]
  | cons x xs => simp [removeList, everyFnVarsNone, removeSing_varsNone x, removeList_varsNone xs]
termination_by sizeOf xs

/-- The same annotation invariant for recursive function bundles. -/
theorem removeFuns_varsNone (fns : List (Nat × Exp)) : fnVarsNoneFuns (removeFuns fns) ↔ fnVarsNoneFuns fns := by
  cases fns with
  | nil => simp [removeFuns, fnVarsNoneFuns]
  | cons pair fns =>
    cases pair with
    | mk arity body => simp [removeFuns, fnVarsNoneFuns, removeSing_varsNone body, removeFuns_varsNone fns]
termination_by sizeOf fns
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

mutual
/-- Tick removal preserves the location condition on one expression. -/
theorem removeSing_locations (e : Exp) : fnLocationSomeExp (removeSing e) ↔ fnLocationSomeExp e := by
  cases e with
  | var t n => simp [removeSing, fnLocationSomeExp]
  | ifThenElse t x y z => simp [removeSing, fnLocationSomeExp, removeSing_locations x, removeSing_locations y, removeSing_locations z]
  | «let» t xs body => simp [removeSing, fnLocationSomeExp, removeList_locations xs, removeSing_locations body]
  | raise t x => simp [removeSing, fnLocationSomeExp, removeSing_locations x]
  | handle t x y => simp [removeSing, fnLocationSomeExp, removeSing_locations x, removeSing_locations y]
  | tick t x => simp [removeSing, fnLocationSomeExp, removeSing_locations x]
  | call t ticks dest xs => simp [removeSing, fnLocationSomeExp, removeList_locations xs]
  | app t loc x xs => simp [removeSing, fnLocationSomeExp, removeSing_locations x, removeList_locations xs]
  | fn name loc vs arity body => simp [removeSing, fnLocationSomeExp, removeSing_locations body]
  | letrec names loc vs fns body => simp [removeSing, fnLocationSomeExp, removeFuns_locations fns, removeSing_locations body]
  | op t op xs => simp [removeSing, fnLocationSomeExp, removeList_locations xs]
termination_by sizeOf e

/-- Tick removal preserves present function locations. -/
theorem removeList_locations (xs : List Exp) : everyFnLocationSome (removeList xs) ↔ everyFnLocationSome xs := by
  cases xs with
  | nil => simp [removeList, everyFnLocationSome]
  | cons x xs => simp [removeList, everyFnLocationSome, removeSing_locations x, removeList_locations xs]
termination_by sizeOf xs

/-- The same location invariant for recursive function bundles. -/
theorem removeFuns_locations (fns : List (Nat × Exp)) : fnLocationSomeFuns (removeFuns fns) ↔ fnLocationSomeFuns fns := by
  cases fns with
  | nil => simp [removeFuns, fnLocationSomeFuns]
  | cons pair fns =>
    cases pair with
    | mk arity body => simp [removeFuns, fnLocationSomeFuns, removeSing_locations body, removeFuns_locations fns]
termination_by sizeOf fns
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

/-- The original list-shaped pass has the HOL invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_every_Fn_vs_NONE"]
theorem removeSource_varsNone (xs : List Exp) : everyFnVarsNone (removeSource xs) ↔ everyFnVarsNone xs := by
  simpa using removeList_varsNone xs

/-- The original list-shaped pass has the HOL invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_every_Fn_SOME"]
theorem removeSource_locations (xs : List Exp) : everyFnLocationSome (removeSource xs) ↔ everyFnLocationSome xs := by
  simpa using removeList_locations xs

end Flapjack.Compiler.Backend.ClosTicks

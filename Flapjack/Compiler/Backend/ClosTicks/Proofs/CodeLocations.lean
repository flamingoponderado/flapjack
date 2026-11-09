module

public import Flapjack.Compiler.Backend.ClosTicks.Source
public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations

@[expose] public section

/-! Code-location preservation by tick removal. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open ClosLang ClosProps

private theorem removeFuns_length (fns : List (Nat × Exp)) : (removeFuns fns).length = fns.length := by
  induction fns with
  | nil => rfl
  | cons first rest ih => cases first; simp [removeFuns, ih]

mutual
/-- Tick removal preserves the locations of an expression. This structural helper has no standalone HOL declaration. -/
theorem removeSing_codeLocations (e : Exp) : codeLocationsExp (removeSing e) = codeLocationsExp e := by
  cases e with
  | var t n => simp [removeSing, codeLocationsExp]
  | ifThenElse t x y z => simp [removeSing, codeLocationsExp, removeSing_codeLocations x, removeSing_codeLocations y, removeSing_codeLocations z]
  | «let» t xs body => simp [removeSing, codeLocationsExp, removeList_codeLocations xs, removeSing_codeLocations body]
  | raise t x => simp [removeSing, codeLocationsExp, removeSing_codeLocations x]
  | handle t x y => simp [removeSing, codeLocationsExp, removeSing_codeLocations x, removeSing_codeLocations y]
  | tick t x => simp [removeSing, codeLocationsExp, removeSing_codeLocations x]
  | call t ticks dest xs => simp [removeSing, codeLocationsExp, removeList_codeLocations xs]
  | app t loc x xs => simp [removeSing, codeLocationsExp, removeSing_codeLocations x, removeList_codeLocations xs]
  | fn name loc vs arity body => simp [removeSing, codeLocationsExp, removeSing_codeLocations body]
  | letrec names loc vs fns body => simp [removeSing, codeLocationsExp, removeFuns_codeLocations fns, removeSing_codeLocations body, removeFuns_length]
  | op t op xs => simp [removeSing, codeLocationsExp, removeList_codeLocations xs]
termination_by sizeOf e

/-- Tick removal preserves the original list of closure-code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "code_locs_remove_ticks"]
theorem removeList_codeLocations (xs : List Exp) : codeLocations (removeList xs) = codeLocations xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [removeList, codeLocations, removeSing_codeLocations x, removeList_codeLocations xs]
termination_by sizeOf xs

/-- The same location equality for recursive function bundles. This structural helper has no standalone HOL declaration. -/
theorem removeFuns_codeLocations (fns : List (Nat × Exp)) :
    codeLocationsFuns (removeFuns fns) = codeLocationsFuns fns := by
  cases fns with
  | nil => rfl
  | cons pair fns => cases pair with
    | mk arity body => simp [removeFuns, codeLocationsFuns, removeSing_codeLocations body, removeFuns_codeLocations fns]
termination_by sizeOf fns
decreasing_by all_goals subst_vars; simp_wf <;> omega
end
end Flapjack.Compiler.Backend.ClosTicks

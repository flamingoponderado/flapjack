module

public import Flapjack.Compiler.Backend.ClosFvs.Source
public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations

@[expose] public section

/-! Code-location preservation by free-variable cleanup. -/
namespace Flapjack.Compiler.Backend.ClosFvs
open ClosLang ClosProps

mutual
/-- Cleanup preserves the closure-code locations of an expression. This structural helper has no standalone HOL declaration. -/
theorem removeSing_codeLocations (e : Exp) (bound : Nat) :
    codeLocationsExp (removeSing bound e) = codeLocationsExp e := by
  cases e with
  | var t n => by_cases inside : n < bound <;> simp [removeSing, inside, codeLocationsExp, codeLocations]
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

/-- Cleanup preserves the original list of closure-code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "code_locs_remove_fvs"]
theorem removeList_codeLocations (xs : List Exp) (bound : Nat) :
    codeLocations (removeList bound xs) = codeLocations xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [removeList, codeLocations, removeSing_codeLocations x, removeList_codeLocations xs]
termination_by sizeOf xs

/-- The same location equality for recursive function bundles. This structural helper has no standalone HOL declaration. -/
theorem removeFuns_codeLocations (fns : List (Nat × Exp)) (count captured : Nat) :
    codeLocationsFuns (removeFuns count captured fns) = codeLocationsFuns fns := by
  cases fns with
  | nil => rfl
  | cons pair fns => cases pair with
    | mk arity body => simp [removeFuns, codeLocationsFuns, removeSing_codeLocations body, removeFuns_codeLocations fns]
termination_by sizeOf fns
decreasing_by all_goals subst_vars; simp_wf <;> omega
end
end Flapjack.Compiler.Backend.ClosFvs

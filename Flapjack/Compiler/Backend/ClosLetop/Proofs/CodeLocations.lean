module

public import Flapjack.Compiler.Backend.ClosLetop.Source
public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations

@[expose] public section

/-! Code-location preservation by let-operation cleanup. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosLang ClosProps

private theorem compileFuns_length (fns : List (Nat × Exp)) : (compileFuns fns).length = fns.length := by
  induction fns with
  | nil => rfl
  | cons first rest ih => cases first; simp [compileFuns, ih]


private theorem varList_codeLocations {α : Type} (n : Nat) (xs : List Exp) (ys : List α)
    (h : varList n xs ys = true) : codeLocations xs = [] := by
  induction xs generalizing n ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp [varList] at h
    | cons y ys =>
      cases x <;> simp [varList] at h
      case var t index =>
        simpa [codeLocations, codeLocationsExp] using ih (n + 1) ys h.2

private theorem destOp_codeLocations {α : Type} (body : Exp) (args : List α) (op : Op)
    (h : destOp body args = some op) : codeLocationsExp body = [] := by
  cases body <;> simp [destOp] at h
  case op trace opn xs =>
    simpa [codeLocationsExp] using varList_codeLocations 0 xs args h.1

mutual
/-- Let-operation cleanup preserves the locations of an expression. This structural helper has no standalone HOL declaration. -/
theorem compileSing_codeLocations (e : Exp) : codeLocationsExp (compileSing e) = codeLocationsExp e := by
  cases e with
  | var t n => simp [compileSing, codeLocationsExp]
  | ifThenElse t x y z => simp [compileSing, codeLocationsExp, compileSing_codeLocations x, compileSing_codeLocations y, compileSing_codeLocations z]
  | «let» t xs body =>
    simp only [compileSing]
    cases h : destOp (compileSing body) (compileList xs) with
    | none => simp [codeLocationsExp, compileList_codeLocations xs, compileSing_codeLocations body]
    | some op =>
      have bodyEmpty := destOp_codeLocations _ _ _ h
      have original : codeLocationsExp body = [] := (compileSing_codeLocations body).symm.trans bodyEmpty
      simp [codeLocationsExp, compileList_codeLocations xs, original]
  | raise t x => simp [compileSing, codeLocationsExp, compileSing_codeLocations x]
  | handle t x y => simp [compileSing, codeLocationsExp, compileSing_codeLocations x, compileSing_codeLocations y]
  | tick t x => simp [compileSing, codeLocationsExp, compileSing_codeLocations x]
  | call t ticks dest xs => simp [compileSing, codeLocationsExp, compileList_codeLocations xs]
  | app t loc x xs => simp [compileSing, codeLocationsExp, compileSing_codeLocations x, compileList_codeLocations xs]
  | fn name loc vs arity body => simp [compileSing, codeLocationsExp, compileSing_codeLocations body]
  | letrec names loc vs fns body => simp [compileSing, codeLocationsExp, compileFuns_codeLocations fns, compileSing_codeLocations body, compileFuns_length]
  | op t op xs => simp [compileSing, codeLocationsExp, compileList_codeLocations xs]
termination_by sizeOf e

/-- Let-operation cleanup preserves the original list of closure-code locations. -/
theorem compileList_codeLocations (xs : List Exp) : codeLocations (compileList xs) = codeLocations xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [compileList, codeLocations, compileSing_codeLocations x, compileList_codeLocations xs]
termination_by sizeOf xs

/-- The same location equality for recursive function bundles. This structural helper has no standalone HOL declaration. -/
theorem compileFuns_codeLocations (fns : List (Nat × Exp)) :
    codeLocationsFuns (compileFuns fns) = codeLocationsFuns fns := by
  cases fns with
  | nil => rfl
  | cons pair fns => cases pair with
    | mk arity body => simp [compileFuns, codeLocationsFuns, compileSing_codeLocations body, compileFuns_codeLocations fns]
termination_by sizeOf fns
decreasing_by all_goals subst_vars; simp_wf <;> omega
end
/-- The original list-shaped pass has the HOL invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "code_locs_let_op"]
theorem compileSource_codeLocations (xs : List Exp) : codeLocations (compileSource xs) = codeLocations xs := by
  simpa using compileList_codeLocations xs

end Flapjack.Compiler.Backend.ClosLetop

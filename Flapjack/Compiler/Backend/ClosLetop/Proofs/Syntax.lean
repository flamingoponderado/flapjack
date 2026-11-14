module

public import Flapjack.Compiler.Backend.ClosLetop.Source
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity

@[expose] public section

/-! Closure annotation invariance for let-operation cleanup. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosLang ClosProps

/-- Compiling a singleton produces a singleton. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "let_op_SING"]
theorem compileSource_singleton (expression : Exp) :
    ∃ result, compileSource [expression] = [result] := by
  exact ⟨compileSing expression, by simp [compileSource_eq_list, compileList]⟩

/-- The head reconstructs a compiled singleton, whose length is one. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "HD_let_op_SING"]
theorem compileSource_singleton_head (expression : Exp) :
    [@Flapjack.holHd Exp ⟨.var .none 0⟩ (compileSource [expression])] =
        compileSource [expression] ∧ (compileSource [expression]).length = 1 := by
  simp [compileSource_eq_list, compileList, Flapjack.holHd]

/-- A recognized variable list contains neither labels nor excessive applications. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "var_list_no_Labels"]
theorem varList_noLabels {α : Type} (n : Nat) (xs : List Exp) (ys : List α)
    (limit : Nat) (h : varList n xs ys = true) :
    (∀ e ∈ xs, noLabels e) ∧ (∀ e ∈ xs, obeysMaxApp limit e) := by
  have aux : noLabelsList xs ∧ obeysMaxAppList limit xs := by
    induction xs generalizing n ys with
    | nil => simp [noLabelsList, obeysMaxAppList]
    | cons x xs ih =>
      cases ys with
      | nil => simp [varList] at h
      | cons y ys =>
        cases x <;> simp [varList] at h
        case var t index =>
          have tail := ih (n + 1) ys h.2
          simpa [noLabelsList, noLabels, obeysMaxAppList, obeysMaxApp] using tail
  exact ⟨(noLabelsList_iff xs).mp aux.1, (obeysMaxAppList_iff limit xs).mp aux.2⟩

/-- Recognized variable lists contain no annotated function nodes. -/
theorem varList_varsNone {α : Type} (n : Nat) (xs : List Exp) (ys : List α)
    (h : varList n xs ys = true) : everyFnVarsNone xs := by
  induction xs generalizing n ys with
  | nil => simp [everyFnVarsNone]
  | cons x xs ih =>
    cases ys with
    | nil => simp [varList] at h
    | cons y ys =>
      cases x <;> simp [varList] at h
      case var t index =>
        simp only [everyFnVarsNone, fnVarsNoneExp, true_and]
        exact ih (n + 1) ys h.2

/-- A recognized operation body has no function annotations. -/
theorem destOp_varsNone {α : Type} (body : Exp) (args : List α) (op : Op)
    (h : destOp body args = some op) : fnVarsNoneExp body := by
  cases body <;> simp [destOp] at h
  case op trace opn xs =>
    simpa [fnVarsNoneExp] using varList_varsNone 0 xs args h.1

mutual
/-- Let-operation cleanup preserves the condition on one expression. -/
theorem compileSing_varsNone (e : Exp) : fnVarsNoneExp (compileSing e) ↔ fnVarsNoneExp e := by
  cases e with
  | var t n => simp [compileSing, fnVarsNoneExp]
  | ifThenElse t x y z => simp [compileSing, fnVarsNoneExp, compileSing_varsNone x, compileSing_varsNone y, compileSing_varsNone z]
  | «let» t xs body =>
    simp only [compileSing]
    cases h : destOp (compileSing body) (compileList xs) with
    | none => simp [fnVarsNoneExp, compileList_varsNone xs, compileSing_varsNone body]
    | some op =>
      have bodySafe := destOp_varsNone _ _ _ h
      have original := (compileSing_varsNone body).mp bodySafe
      simp [fnVarsNoneExp, compileList_varsNone xs, original]
  | raise t x => simp [compileSing, fnVarsNoneExp, compileSing_varsNone x]
  | handle t x y => simp [compileSing, fnVarsNoneExp, compileSing_varsNone x, compileSing_varsNone y]
  | tick t x => simp [compileSing, fnVarsNoneExp, compileSing_varsNone x]
  | call t ticks dest xs => simp [compileSing, fnVarsNoneExp, compileList_varsNone xs]
  | app t loc x xs => simp [compileSing, fnVarsNoneExp, compileSing_varsNone x, compileList_varsNone xs]
  | fn name loc vs arity body => simp [compileSing, fnVarsNoneExp, compileSing_varsNone body]
  | letrec names loc vs fns body => simp [compileSing, fnVarsNoneExp, compileFuns_varsNone fns, compileSing_varsNone body]
  | op t op xs => simp [compileSing, fnVarsNoneExp, compileList_varsNone xs]
termination_by sizeOf e

/-- Let-operation cleanup preserves absent closure-capture annotations. -/
theorem compileList_varsNone (xs : List Exp) : everyFnVarsNone (compileList xs) ↔ everyFnVarsNone xs := by
  cases xs with
  | nil => simp [compileList, everyFnVarsNone]
  | cons x xs => simp [compileList, everyFnVarsNone, compileSing_varsNone x, compileList_varsNone xs]
termination_by sizeOf xs

/-- The same annotation invariant for recursive function bundles. -/
theorem compileFuns_varsNone (fns : List (Nat × Exp)) : fnVarsNoneFuns (compileFuns fns) ↔ fnVarsNoneFuns fns := by
  cases fns with
  | nil => simp [compileFuns, fnVarsNoneFuns]
  | cons pair fns =>
    cases pair with
    | mk arity body => simp [compileFuns, fnVarsNoneFuns, compileSing_varsNone body, compileFuns_varsNone fns]
termination_by sizeOf fns
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

/-- Recognized variable lists contain no annotated function nodes. -/
theorem varList_locations {α : Type} (n : Nat) (xs : List Exp) (ys : List α)
    (h : varList n xs ys = true) : everyFnLocationSome xs := by
  induction xs generalizing n ys with
  | nil => simp [everyFnLocationSome]
  | cons x xs ih =>
    cases ys with
    | nil => simp [varList] at h
    | cons y ys =>
      cases x <;> simp [varList] at h
      case var t index =>
        simp only [everyFnLocationSome, fnLocationSomeExp, true_and]
        exact ih (n + 1) ys h.2

/-- A recognized operation body has no function locations. -/
theorem destOp_locations {α : Type} (body : Exp) (args : List α) (op : Op)
    (h : destOp body args = some op) : fnLocationSomeExp body := by
  cases body <;> simp [destOp] at h
  case op trace opn xs =>
    simpa [fnLocationSomeExp] using varList_locations 0 xs args h.1

mutual
/-- Let-operation cleanup preserves the condition on one expression. -/
theorem compileSing_locations (e : Exp) : fnLocationSomeExp (compileSing e) ↔ fnLocationSomeExp e := by
  cases e with
  | var t n => simp [compileSing, fnLocationSomeExp]
  | ifThenElse t x y z => simp [compileSing, fnLocationSomeExp, compileSing_locations x, compileSing_locations y, compileSing_locations z]
  | «let» t xs body =>
    simp only [compileSing]
    cases h : destOp (compileSing body) (compileList xs) with
    | none => simp [fnLocationSomeExp, compileList_locations xs, compileSing_locations body]
    | some op =>
      have bodySafe := destOp_locations _ _ _ h
      have original := (compileSing_locations body).mp bodySafe
      simp [fnLocationSomeExp, compileList_locations xs, original]
  | raise t x => simp [compileSing, fnLocationSomeExp, compileSing_locations x]
  | handle t x y => simp [compileSing, fnLocationSomeExp, compileSing_locations x, compileSing_locations y]
  | tick t x => simp [compileSing, fnLocationSomeExp, compileSing_locations x]
  | call t ticks dest xs => simp [compileSing, fnLocationSomeExp, compileList_locations xs]
  | app t loc x xs => simp [compileSing, fnLocationSomeExp, compileSing_locations x, compileList_locations xs]
  | fn name loc vs arity body => simp [compileSing, fnLocationSomeExp, compileSing_locations body]
  | letrec names loc vs fns body => simp [compileSing, fnLocationSomeExp, compileFuns_locations fns, compileSing_locations body]
  | op t op xs => simp [compileSing, fnLocationSomeExp, compileList_locations xs]
termination_by sizeOf e

/-- Let-operation cleanup preserves present function locations. -/
theorem compileList_locations (xs : List Exp) : everyFnLocationSome (compileList xs) ↔ everyFnLocationSome xs := by
  cases xs with
  | nil => simp [compileList, everyFnLocationSome]
  | cons x xs => simp [compileList, everyFnLocationSome, compileSing_locations x, compileList_locations xs]
termination_by sizeOf xs

/-- The same location invariant for recursive function bundles. -/
theorem compileFuns_locations (fns : List (Nat × Exp)) : fnLocationSomeFuns (compileFuns fns) ↔ fnLocationSomeFuns fns := by
  cases fns with
  | nil => simp [compileFuns, fnLocationSomeFuns]
  | cons pair fns =>
    cases pair with
    | mk arity body => simp [compileFuns, fnLocationSomeFuns, compileSing_locations body, compileFuns_locations fns]
termination_by sizeOf fns
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

/-- The original list-shaped pass has the HOL invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "let_op_every_Fn_vs_NONE"]
theorem compileSource_varsNone (xs : List Exp) : everyFnVarsNone (compileSource xs) ↔ everyFnVarsNone xs := by
  simpa using compileList_varsNone xs

/-- The original list-shaped pass has the HOL invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "let_op_every_Fn_SOME"]
theorem compileSource_locations (xs : List Exp) : everyFnLocationSome (compileSource xs) ↔ everyFnLocationSome xs := by
  simpa using compileList_locations xs

end Flapjack.Compiler.Backend.ClosLetop

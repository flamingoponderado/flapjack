import Flapjack.Compiler.Backend.ClosLetop.Proofs.Syntax
import Flapjack.Compiler.Backend.Semantics.ClosProps.AppCallDests

/-! Call-destination properties of let-operation cleanup. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosLang ClosProps

/-- A recognized variable list has no application or call destinations. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "var_list_app_call_dests"]
theorem varList_appCallDests {α : Type} (n : Nat) (xs : List Exp) (ys : List α)
    (selection : Option Bool) (h : varList n xs ys = true) : appCallDests selection xs = ∅ := by
  induction xs generalizing n ys with
  | nil => simp [appCallDests]
  | cons x xs ih =>
    cases ys with
    | nil => simp [varList] at h
    | cons y ys =>
      cases x <;> simp [varList] at h
      case var trace index =>
        rw [show Exp.var trace index :: xs = [Exp.var trace index] ++ xs from rfl,
          appCallDests_append]
        simp [appCallDests, ih (n + 1) ys h.2]

mutual
/-- Structural induction helper for the source theorem, with no separate HOL declaration. -/
theorem compileSing_appCallDests (selection : Option Bool) (e : Exp) :
    appCallDests selection [compileSing e] = appCallDests selection [e] := by
  cases e with
  | var t n => simp [compileSing, appCallDests]
  | ifThenElse t x y z => simp [compileSing, appCallDests, compileSing_appCallDests selection x, compileSing_appCallDests selection y, compileSing_appCallDests selection z]
  | «let» t xs body =>
    simp only [compileSing]
    cases h : destOp (compileSing body) (compileList xs) with
    | none => simp [appCallDests, compileList_appCallDests selection xs, compileSing_appCallDests selection body]
    | some op =>
      obtain ⟨trace, expressions, eq, vars⟩ := destOp_some_imp (compileSing body) (compileList xs) op h
      have empty : appCallDests selection [compileSing body] = ∅ := by
        rw [eq]
        simpa [appCallDests] using varList_appCallDests 0 expressions (compileList xs) selection vars
      have original : appCallDests selection [body] = ∅ := (compileSing_appCallDests selection body).symm.trans empty
      simp [appCallDests, compileList_appCallDests selection xs, original]
  | raise t x => simp [compileSing, appCallDests, compileSing_appCallDests selection x]
  | handle t x y => simp [compileSing, appCallDests, compileSing_appCallDests selection x, compileSing_appCallDests selection y]
  | tick t x => simp [compileSing, appCallDests, compileSing_appCallDests selection x]
  | call t ticks dest xs => simp [compileSing, appCallDests, compileList_appCallDests selection xs]
  | app t loc x xs =>
    cases loc <;> simp [compileSing, appCallDests, compileSing_appCallDests selection x, compileList_appCallDests selection xs]
  | fn name loc vs arity body => simp [compileSing, appCallDests, compileSing_appCallDests selection body]
  | letrec names loc vs fns body => simp [compileSing, appCallDests, compileFuns_appCallDests selection fns, compileSing_appCallDests selection body]
  | op t op xs => simp [compileSing, appCallDests, compileList_appCallDests selection xs]
termination_by sizeOf e

/-- List case of the structural induction; it has no separate HOL declaration. -/
theorem compileList_appCallDests (selection : Option Bool) (xs : List Exp) :
    appCallDests selection (compileList xs) = appCallDests selection xs := by
  cases xs with
  | nil => simp [compileList, appCallDests]
  | cons x xs =>
    simp only [compileList]
    rw [show compileSing x :: compileList xs = [compileSing x] ++ compileList xs from rfl,
      show x :: xs = [x] ++ xs from rfl, appCallDests_append, appCallDests_append,
      compileSing_appCallDests selection x, compileList_appCallDests selection xs]
termination_by sizeOf xs

/-- Recursive-function case of the structural induction, with no separate HOL declaration. -/
theorem compileFuns_appCallDests (selection : Option Bool) (fns : List (Nat × Exp)) :
    appCallDests selection ((compileFuns fns).map Prod.snd) = appCallDests selection (fns.map Prod.snd) := by
  cases fns with
  | nil => simp [compileFuns, appCallDests]
  | cons pair fns =>
    cases pair with
    | mk arity body =>
      simp only [compileFuns, List.map_cons]
      rw [show compileSing body :: (compileFuns fns).map Prod.snd = [compileSing body] ++ (compileFuns fns).map Prod.snd from rfl,
        show body :: fns.map Prod.snd = [body] ++ fns.map Prod.snd from rfl,
        appCallDests_append, appCallDests_append, compileSing_appCallDests selection body,
        compileFuns_appCallDests selection fns]
termination_by sizeOf fns
decreasing_by all_goals (subst_vars; simp_wf; omega)
end

/-- Let-operation cleanup preserves application and call destinations. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "let_op_app_call_dests"]
theorem compileSource_appCallDests (selection : Option Bool) (xs : List Exp) :
    appCallDests selection (compileSource xs) = appCallDests selection xs := by
  simpa using compileList_appCallDests selection xs

end Flapjack.Compiler.Backend.ClosLetop

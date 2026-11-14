module

public import Flapjack.Compiler.Backend.ClosLetop.Proofs.Syntax
public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLabels

@[expose] public section

/-! Code-label preservation by let-operation cleanup. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosLang ClosProps

/-- A recognized variable list contains no code labels. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "var_list_code_labels_imp"]
theorem varList_codeLabels {α : Type} (n : Nat) (xs : List Exp) (ys : List α)
    (valid : varList n xs ys = true) : (⋃₀ (getCodeLabels '' {e | e ∈ xs})) = ∅ := by
  rw [← getCodeLabelsList_eq]
  induction xs generalizing n ys with
  | nil => simp [getCodeLabelsList]
  | cons e es ih =>
    cases ys with
    | nil => simp [varList] at valid
    | cons y ys =>
      cases e <;> simp [varList] at valid
      case var trace index =>
        simpa [getCodeLabelsList, getCodeLabels] using ih (n + 1) ys valid.2

mutual
private theorem compileSing_codeLabels (e : Exp) : getCodeLabels (compileSing e) = getCodeLabels e := by
  cases e with
  | var t n => simp [compileSing, getCodeLabels]
  | ifThenElse t x y z => simp [compileSing, getCodeLabels, compileSing_codeLabels x, compileSing_codeLabels y, compileSing_codeLabels z]
  | «let» t xs body =>
    simp only [compileSing]
    cases h : destOp (compileSing body) (compileList xs) with
    | none => simp [getCodeLabels, compileList_codeLabels xs, compileSing_codeLabels body]
    | some op =>
      obtain ⟨trace, expressions, eq, vars⟩ := destOp_some_imp (compileSing body) (compileList xs) op h
      have empty : getCodeLabelsList expressions = ∅ := by
        rw [getCodeLabelsList_eq]
        exact varList_codeLabels 0 expressions (compileList xs) vars
      have bodyLabels : getCodeLabels (compileSing body) = assignGetCodeLabel op := by
        rw [eq]
        simp [getCodeLabels, empty]
      have original : getCodeLabels body = assignGetCodeLabel op := (compileSing_codeLabels body).symm.trans bodyLabels
      simp [getCodeLabels, compileList_codeLabels xs, original]
  | raise t x => simp [compileSing, getCodeLabels, compileSing_codeLabels x]
  | handle t x y => simp [compileSing, getCodeLabels, compileSing_codeLabels x, compileSing_codeLabels y]
  | tick t x => simp [compileSing, getCodeLabels, compileSing_codeLabels x]
  | call t ticks dest xs => simp [compileSing, getCodeLabels, compileList_codeLabels xs]
  | app t loc x xs => cases loc <;> simp [compileSing, getCodeLabels, compileSing_codeLabels x, compileList_codeLabels xs]
  | fn name loc vs arity body => cases loc <;> simp [compileSing, getCodeLabels, compileSing_codeLabels body]
  | letrec names loc vs fns body =>
    have length : (compileFuns fns).length = fns.length := by simp [compileFuns_eq_map]
    cases loc <;> simp [compileSing, getCodeLabels, compileFuns_codeLabels fns,
      compileSing_codeLabels body, length]
  | op t op xs => simp [compileSing, getCodeLabels, compileList_codeLabels xs]
termination_by sizeOf e

private theorem compileList_codeLabels (xs : List Exp) :
    getCodeLabelsList (compileList xs) = getCodeLabelsList xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [compileList, getCodeLabelsList, compileSing_codeLabels x, compileList_codeLabels xs]
termination_by sizeOf xs

private theorem compileFuns_codeLabels (fns : List (Nat × Exp)) :
    getCodeLabelsFuns (compileFuns fns) = getCodeLabelsFuns fns := by
  cases fns with
  | nil => rfl
  | cons pair fns => cases pair with
    | mk arity body => simp [compileFuns, getCodeLabelsFuns, compileSing_codeLabels body, compileFuns_codeLabels fns]
termination_by sizeOf fns
decreasing_by all_goals (subst_vars; simp_wf; omega)
end

/-- Let-operation cleanup preserves each expression's code-label set. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "let_op_get_code_labels"]
theorem compileSource_codeLabels (xs : List Exp) :
    (compileSource xs).map getCodeLabels = xs.map getCodeLabels := by
  rw [compileSource_eq_list]
  induction xs with
  | nil => rfl
  | cons e es ih => simp [compileList, compileSing_codeLabels, ih]

end Flapjack.Compiler.Backend.ClosLetop

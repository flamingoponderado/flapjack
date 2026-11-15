module

public import Flapjack.Compiler.Backend.ClosNumber
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity

@[expose] public section

/-! Preservation of the source-language label-operation restriction. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open ClosLang ClosProps

mutual
private theorem renumber_noLabels (expression : Exp) (start : Nat) :
    noLabels (renumber start expression).2 ↔ noLabels expression := by
  cases expression with
  | var t n => simp [renumber, noLabels]
  | ifThenElse t a b c =>
    simp [renumber, noLabels, renumber_noLabels a, renumber_noLabels b, renumber_noLabels c]
  | «let» t bindings body =>
    simp [renumber, noLabels, renumberList_noLabels bindings, renumber_noLabels body]
  | raise t body => simp [renumber, noLabels, renumber_noLabels body]
  | handle t a b => simp [renumber, noLabels, renumber_noLabels a, renumber_noLabels b]
  | tick t body => simp [renumber, noLabels, renumber_noLabels body]
  | call t ticks loc args => simp [renumber, noLabels, renumberList_noLabels args]
  | app t loc fn args => simp [renumber, noLabels, renumber_noLabels fn, renumberList_noLabels args]
  | fn name loc vars arity body => simp [renumber, noLabels, renumber_noLabels body]
  | letrec names loc vars functions body =>
    simp [renumber, noLabels, renumberFuns_noLabels functions, renumber_noLabels body]
  | op t op args => simp [renumber, noLabels, renumberList_noLabels args]
termination_by sizeOf expression

private theorem renumberList_noLabels (expressions : List Exp) (start : Nat) :
    noLabelsList (renumberList start expressions).2 ↔ noLabelsList expressions := by
  cases expressions with
  | nil => simp [renumberList, noLabelsList]
  | cons first rest => simp [renumberList, noLabelsList, renumber_noLabels first, renumberList_noLabels rest]
termination_by sizeOf expressions

private theorem renumberFuns_noLabels (functions : List (Nat × Exp)) (start : Nat) :
    noLabelsFuns (renumberFuns start functions).2 ↔ noLabelsFuns functions := by
  cases functions with
  | nil => simp [renumberFuns, noLabelsFuns]
  | cons first rest =>
    cases first with
    | mk arity body => simp [renumberFuns, noLabelsFuns, renumber_noLabels body, renumberFuns_noLabels rest]
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

/-- Numbering preserves the absence of label operations in lists and expressions. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "renumber_code_locs_no_Labels"]
theorem renumberCodeLocs_noLabels :
    (∀ loc es n es', renumberList loc es = (n, es') ∧ (∀ e ∈ es, noLabels e) →
      ∀ e ∈ es', noLabels e) ∧
    (∀ loc e n e', renumber loc e = (n, e') ∧ noLabels e → noLabels e') := by
  constructor
  · intro loc es n es' ⟨run, input⟩
    have h := renumberList_noLabels es loc
    rw [run] at h
    exact noLabelsList_iff es' |>.mp (h.mpr (noLabelsList_iff es |>.mpr input))
  · intro loc e n e' ⟨run, input⟩
    have h := renumber_noLabels e loc
    rw [run] at h
    exact h.mpr input

end Flapjack.Compiler.Backend.ClosNumber

module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationInvariants
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity

@[expose] public section

/-! Preservation of the source-language application arity bounds. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open ClosLang ClosProps

mutual
private theorem renumber_obeysMaxApp (expression : Exp) (start m : Nat) :
    obeysMaxApp m (renumber start expression).2 ↔ obeysMaxApp m expression := by
  cases expression with
  | var t n => simp [renumber, obeysMaxApp]
  | ifThenElse t a b c =>
    simp [renumber, obeysMaxApp, renumber_obeysMaxApp a, renumber_obeysMaxApp b, renumber_obeysMaxApp c]
  | «let» t bindings body =>
    simp [renumber, obeysMaxApp, renumberList_obeysMaxApp bindings, renumber_obeysMaxApp body]
  | raise t body => simp [renumber, obeysMaxApp, renumber_obeysMaxApp body]
  | handle t a b => simp [renumber, obeysMaxApp, renumber_obeysMaxApp a, renumber_obeysMaxApp b]
  | tick t body => simp [renumber, obeysMaxApp, renumber_obeysMaxApp body]
  | call t ticks loc args => simp [renumber, obeysMaxApp, renumberList_obeysMaxApp args]
  | app t loc fn args => simp [renumber, obeysMaxApp, renumber_obeysMaxApp fn, renumberList_obeysMaxApp args, renumberList_length]
  | fn name loc vars arity body => simp [renumber, obeysMaxApp, renumber_obeysMaxApp body]
  | letrec names loc vars functions body =>
    simp [renumber, obeysMaxApp, renumberFuns_obeysMaxApp functions, renumber_obeysMaxApp body]
  | op t op args => simp [renumber, obeysMaxApp, renumberList_obeysMaxApp args]
termination_by sizeOf expression

private theorem renumberList_obeysMaxApp (expressions : List Exp) (start m : Nat) :
    obeysMaxAppList m (renumberList start expressions).2 ↔ obeysMaxAppList m expressions := by
  cases expressions with
  | nil => simp [renumberList, obeysMaxAppList]
  | cons first rest => simp [renumberList, obeysMaxAppList, renumber_obeysMaxApp first, renumberList_obeysMaxApp rest]
termination_by sizeOf expressions

private theorem renumberFuns_obeysMaxApp (functions : List (Nat × Exp)) (start m : Nat) :
    obeysMaxAppFuns m (renumberFuns start functions).2 ↔ obeysMaxAppFuns m functions := by
  cases functions with
  | nil => simp [renumberFuns, obeysMaxAppFuns]
  | cons first rest =>
    cases first with
    | mk arity body => simp [renumberFuns, obeysMaxAppFuns, renumber_obeysMaxApp body, renumberFuns_obeysMaxApp rest]
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

/-- Numbering preserves the application arity bounds in lists and expressions. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "renumber_code_locs_obeys_max_app"]
theorem renumberCodeLocs_obeysMaxApp (m : Nat) :
    (∀ loc es n es', renumberList loc es = (n, es') ∧ (∀ e ∈ es, obeysMaxApp m e) →
      ∀ e ∈ es', obeysMaxApp m e) ∧
    (∀ loc e n e', renumber loc e = (n, e') ∧ obeysMaxApp m e → obeysMaxApp m e') := by
  constructor
  · intro loc es n es' ⟨run, input⟩
    have h := renumberList_obeysMaxApp es loc m
    rw [run] at h
    exact obeysMaxAppList_iff m es' |>.mp (h.mpr (obeysMaxAppList_iff m es |>.mpr input))
  · intro loc e n e' ⟨run, input⟩
    have h := renumber_obeysMaxApp e loc m
    rw [run] at h
    exact h.mpr input

end Flapjack.Compiler.Backend.ClosNumber

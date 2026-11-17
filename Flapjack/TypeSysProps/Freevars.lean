module

public import Flapjack.TypeSystemHOL.Environments

@[expose] public section

/-! Free-variable bounds for declarative types. -/
namespace Flapjack.TypeSysProps
open Flapjack.TypeSystemHOL Flapjack.Basis.Pure.MlString

mutual
/-- Increasing the de Bruijn bound preserves a free-variable check. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "check_freevars_add"]
theorem checkFreevarsAdd (tvs : Nat) (names : List MlString) (t : SemanticT) :
    checkFreevars tvs names t = true → ∀ tvs', tvs ≤ tvs' → checkFreevars tvs' names t = true := by
  intro checked tvs' bound
  cases t with
  | var name => simpa [checkFreevars] using checked
  | varDb index =>
    simp only [checkFreevars, decide_eq_true_eq] at checked ⊢
    omega
  | app args id =>
    simp only [checkFreevars] at checked ⊢
    exact checkFreevarsListAdd tvs names args checked tvs' bound
termination_by sizeOf t

/-- List traversal for the source free-variable induction, which HOL proves
within the same theorem rather than as a separate declaration. -/
private theorem checkFreevarsListAdd (tvs : Nat) (names : List MlString) (ts : List SemanticT) :
    checkFreevarsList tvs names ts = true → ∀ tvs', tvs ≤ tvs' →
      checkFreevarsList tvs' names ts = true := by
  intro checked tvs' bound
  cases ts with
  | nil => simp [checkFreevarsList]
  | cons t rest =>
    simp only [checkFreevarsList, Bool.and_eq_true] at checked ⊢
    exact ⟨checkFreevarsAdd tvs names t checked.1 tvs' bound,
      checkFreevarsListAdd tvs names rest checked.2 tvs' bound⟩
termination_by sizeOf ts
end

end Flapjack.TypeSysProps

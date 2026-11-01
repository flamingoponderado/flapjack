import Flapjack.Compiler.Backend.Semantics.DataSem.State
import Batteries.Data.List.Basic

/-! Variable correspondence for the data-language semantics. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack

/-- The listed names resolve, in order, to the listed values. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "var_corr_def"]
def varCorr {α : Type} (values : List α) (names : List Nat) (env : Spt α) : Prop :=
  List.Forall₂ (fun name value => DataSem.getVar name env = some value) names values

/-- Corresponding names can be read together from the data environment. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "get_vars_thm"]
theorem getVars_thm {α : Type} (names : List Nat) (values : List α) (env : Spt α)
    (related : varCorr values names env) : DataSem.getVars names env = some values := by
  induction related with
  | nil => rfl
  | cons lookup rest ih => simp [DataSem.getVars, lookup, ih]

/-- Any indexed corresponding value has a name which resolves to that value.
This is Flapjack infrastructure for the variable compiler case. -/
theorem varCorr_lookup {α : Type} (values : List α) (names : List Nat) (env : Spt α)
    (related : varCorr values names env) (index : Nat) (value : α)
    (atIndex : values[index]? = some value) :
    ∃ name, names[index]? = some name ∧ DataSem.getVar name env = some value := by
  induction related generalizing index with
  | nil => simp at atIndex
  | @cons name first names values lookup rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at atIndex
      subst value
      exact ⟨name, rfl, lookup⟩
    | succ index =>
      simp only [List.getElem?_cons_succ] at atIndex ⊢
      exact ih index atIndex

end Flapjack.Compiler.Backend.DataProps

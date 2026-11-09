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

/-- Reading concatenated name lists concatenates their successful reads. -/
private theorem getVars_append_of_reads {α : Type} (first second : List Nat) (env : Spt α)
    (left right : List α) (firstRead : DataSem.getVars first env = some left)
    (secondRead : DataSem.getVars second env = some right) :
    DataSem.getVars (first ++ second) env = some (left ++ right) := by
  induction first generalizing left with
  | nil => simp [DataSem.getVars] at firstRead; subst left; exact secondRead
  | cons name names ih =>
    simp only [DataSem.getVars] at firstRead
    cases found : DataSem.getVar name env with
    | none => simp [found] at firstRead
    | some value =>
      simp only [found] at firstRead
      cases rest : DataSem.getVars names env with
      | none => simp [rest] at firstRead
      | some tail =>
        simp [rest] at firstRead
        subst left
        simp [DataSem.getVars, found, ih tail rest]

/-- Reversing a successful list of variable names reverses its values. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "get_vars_reverse"]
theorem getVars_reverse {α : Type} (names : List Nat) (env : Spt α) (values : List α)
    (read : DataSem.getVars names env = some values) :
    DataSem.getVars names.reverse env = some values.reverse := by
  induction names generalizing values with
  | nil => simpa [DataSem.getVars] using read
  | cons name names ih =>
    simp only [DataSem.getVars] at read
    cases found : DataSem.getVar name env with
    | none => simp [found] at read
    | some value =>
      simp only [found] at read
      cases rest : DataSem.getVars names env with
      | none => simp [rest] at read
      | some tail =>
        simp [rest] at read
        subst values
        simpa only [List.reverse_cons] using
          getVars_append_of_reads names.reverse [name] env tail.reverse [value] (ih tail rest) (by simp [DataSem.getVars, found])

end Flapjack.Compiler.Backend.DataProps

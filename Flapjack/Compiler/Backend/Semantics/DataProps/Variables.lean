module

public import Flapjack.Compiler.Backend.Semantics.DataSem.State
public import Batteries.Data.List.Basic

@[expose] public section

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

/-- Reading concatenated name lists sequences both reads and concatenates their results. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "get_vars_append"]
theorem getVars_append {α : Type} (first second : List Nat) (env : Spt α) :
    DataSem.getVars (first ++ second) env =
      (DataSem.getVars first env).bind (fun left =>
        (DataSem.getVars second env).bind (fun right => some (left ++ right))) := by
  induction first with
  | nil => simp [DataSem.getVars]
  | cons name names ih =>
    simp only [List.cons_append, DataSem.getVars, ih]
    cases DataSem.getVar name env <;> simp
    cases DataSem.getVars names env <;> simp
    cases DataSem.getVars second env <;> simp

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
        simp [List.reverse_cons, getVars_append, ih tail rest, DataSem.getVars, found]

/-- Every name read successfully belongs to the sparse environment domain. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "get_vars_IMP_domain"]
theorem getVars_imp_domain {α : Type} (names : List Nat) (x : Nat) (env : Spt α) (values : List α)
    (premise : x ∈ names ∧ DataSem.getVars names env = some values) :
    sptDomain env x := by
  obtain ⟨member, read⟩ := premise
  induction names generalizing values with
  | nil => simp at member
  | cons name names ih =>
    simp only [DataSem.getVars] at read
    cases found : DataSem.getVar name env with
    | none => simp [found] at read
    | some value =>
      simp only [found] at read
      cases rest : DataSem.getVars names env with
      | none => simp [rest] at read
      | some tail =>
        rcases List.mem_cons.mp member with rfl | member
        · have lookup : sptLookup x env = some value := found
          simp [sptDomain, lookup]
        · exact ih tail member rest

/-- Reads agree when every requested lookup agrees. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "EVERY_get_vars"]
theorem every_getVars {α : Type} (names : List Nat) (first second : Spt α)
    (agree : ∀ name ∈ names, sptLookup name first = sptLookup name second) :
    DataSem.getVars names first = DataSem.getVars names second := by
  induction names with
  | nil => rfl
  | cons name names ih =>
    have head := agree name (by simp)
    have tail : ∀ key ∈ names, sptLookup key first = sptLookup key second :=
      fun key member => agree key (by simp [member])
    simp [DataSem.getVars, DataSem.getVar, head, ih tail]

end Flapjack.Compiler.Backend.DataProps

module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
public import Flapjack.Misc.Sptree.Subspt
public import Flapjack.Misc.Sptree.Wf

@[expose] public section

/-! Local-environment extension properties for data-language evaluation. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- The local-environment relation preserves every successful lookup. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "locals_ok_def"]
def localsOk {α : Type} (source target : Spt α) : Prop :=
  ∀ key value, sptLookup key source = some value → sptLookup key target = some value

/-- Every local environment extends itself. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "locals_ok_refl"]
theorem localsOk_refl {α : Type} (locals : Spt α) : localsOk locals locals := by
  exact fun _ _ found => found

/-- Extending locals preserves every successful variable-list read. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "locals_ok_get_vars"]
theorem getVars_of_subspt {α : Type} (names : List Nat) (source target : Spt α)
    (values : List α) (included : localsOk source target)
    (read : DataSem.getVars names source = some values) : DataSem.getVars names target = some values := by
  induction names generalizing values with
  | nil => simpa [DataSem.getVars] using read
  | cons name names ih =>
    cases first : DataSem.getVar name source with
    | none => simp [DataSem.getVars, first] at read
    | some value =>
      cases rest : DataSem.getVars names source with
      | none => simp [DataSem.getVars, first, rest] at read
      | some tail =>
        have targetFirst : DataSem.getVar name target = some value :=
          included name value first
        have targetRest := ih tail rest
        simp [DataSem.getVars, first, rest] at read
        subst values
        simp [DataSem.getVars, targetFirst, targetRest]

/-- Restricting a larger environment to names present in the smaller one
produces the same sparse tree, including its canonical shape. -/
theorem inter_eq_of_subspt {α : Type} (source target : Spt α) (names : NumSet)
    (included : sptSubspt source target)
    (present : ∀ key, sptMem key names → sptMem key source) :
    sptInter source names = sptInter target names := by
  apply (sptEqThm _ _ ⟨sptWfInter _ _, sptWfInter _ _⟩).2
  intro key
  rw [sptLookup_sptInterCases, sptLookup_sptInterCases]
  cases found : sptLookup key names with
  | none => simp
  | some value =>
    have member : sptMem key names := by simp [sptMem, sptDomain, found]
    have lookupEq := (included key (present key member)).2
    simp [lookupEq]

/-- A successful cut of the smaller environment succeeds with the exact
same result when the input environment included it. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "locals_ok_cut_env"]
theorem cutEnv_of_subspt {α : Type} (names : NumSet) (source target result : Spt α)
    (included : localsOk source target) (cut : DataSem.cutEnv names source = some result) :
    DataSem.cutEnv names target = some result := by
  classical
  have subspt : sptSubspt source target := (sptSubsptLookup source target).2 included
  have present : ∀ key, sptMem key names → sptMem key source := by
    unfold DataSem.cutEnv at cut
    split at cut
    · assumption
    · simp at cut
  have targetPresent : ∀ key, sptMem key names → sptMem key target :=
    fun key member => (subspt key (present key member)).1
  have interEq := inter_eq_of_subspt source target names subspt present
  unfold DataSem.cutEnv at cut ⊢
  rw [if_pos present] at cut
  rw [if_pos targetPresent, ← interEq]
  exact cut

/-- Inclusion of local environments preserves domain membership. HOL writes the
conclusion as `domain l1 SUBSET domain l2`, i.e. set inclusion on the domain
predicate. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "locals_ok_IMP"]
theorem domain_of_localsOk {α : Type} (source target : Spt α)
    (included : localsOk source target) :
    ∀ key, sptDomain source key → sptDomain target key := by
  intro key member
  rw [sptDomain_iff_lookup] at member ⊢
  obtain ⟨value, found⟩ := member
  exact ⟨value, included key value found⟩

/-- A successful single-variable read transports along the relation. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "locals_ok_get_var"]
theorem getVar_of_localsOk {α : Type} (source target : Spt α) (name : Nat)
    (value : α) (included : localsOk source target)
    (read : DataSem.getVar name source = some value) :
    DataSem.getVar name target = some value := by
  exact included name value read

/-- Inserting the same binding into both environments preserves the relation. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "locals_ok_insert"]
theorem sptInsert_of_localsOk {α : Type} (source target : Spt α) (key : Nat)
    (value : α) (included : localsOk source target) :
    localsOk (sptInsert key value source) (sptInsert key value target) := by
  intro other found_value found
  by_cases hkey : other = key
  · subst hkey
    rw [sptLookup_sptInsert_same] at found ⊢
    exact found
  · rw [sptLookup_sptInsert_ne key other value source hkey] at found
    rw [sptLookup_sptInsert_ne key other value target hkey]
    exact included other found_value found

end Flapjack.Compiler.Backend.DataProps

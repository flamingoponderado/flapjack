module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
public import Flapjack.Misc.Sptree.Subspt
public import Flapjack.Misc.Sptree.Wf

@[expose] public section

/-! Local-environment extension properties for data-language evaluation. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- The HOL locals relation uses the existing sparse-tree extension relation. -/
abbrev localsOk {α : Type} (source target : Spt α) : Prop := sptSubspt source target

/-- The complete pointwise defining equation for the local-environment relation. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "locals_ok_def"]
theorem localsOk_def {α : Type} (source target : Spt α) :
    localsOk source target ↔
      ∀ key value, sptLookup key source = some value → sptLookup key target = some value :=
  sptSubsptLookup source target

/-- Every local environment extends itself. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "locals_ok_refl"]
theorem localsOk_refl {α : Type} (locals : Spt α) : localsOk locals locals := by
  exact (localsOk_def locals locals).2 (fun _ _ found => found)

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
          (sptSubsptLookup source target).1 included name value first
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
  have present : ∀ key, sptMem key names → sptMem key source := by
    unfold DataSem.cutEnv at cut
    split at cut
    · assumption
    · simp at cut
  have targetPresent : ∀ key, sptMem key names → sptMem key target :=
    fun key member => (included key (present key member)).1
  have interEq := inter_eq_of_subspt source target names included present
  unfold DataSem.cutEnv at cut ⊢
  rw [if_pos present] at cut
  rw [if_pos targetPresent, ← interEq]
  exact cut

end Flapjack.Compiler.Backend.DataProps

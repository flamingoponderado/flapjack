module

public import Flapjack.Compiler.Backend.DataSpace.Compile
public import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
public import Flapjack.Misc.Sptree.Subspt
public import Flapjack.Misc.Sptree.Wf

@[expose] public section

/-! State and variable lemmas for data-space reservation. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- A successful variable read returns one value per requested name. This
is untagged until its source and carrier correspondence are reviewed. -/
theorem getVars_length {α : Type} (names : List Nat) (env : Spt α) (values : List α)
    (read : DataSem.getVars names env = some values) : values.length = names.length := by
  induction names generalizing values with
  | nil => simpa [DataSem.getVars] using read
  | cons name names ih =>
    cases first : DataSem.getVar name env with
    | none => simp [DataSem.getVars, first] at read
    | some value =>
      cases rest : DataSem.getVars names env with
      | none => simp [DataSem.getVars, first, rest] at read
      | some tail =>
        simp [DataSem.getVars, first, rest] at read
        subst values
        simp [ih tail rest]

/-- Stack accounting commutes with changing the available space field. -/
theorem doStack_with_space {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state : State C F) (space : Nat) :
    doStack op values { state with space := space } = { doStack op values state with space := space } := by
  rfl

/-- Stack accounting commutes with changing the local environment. -/
theorem doStack_with_locals {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state : State C F) (locals : Spt Value) :
    doStack op values { state with locals := locals } = { doStack op values state with locals := locals } := by
  rfl

/-- A larger sparse local environment preserves every successful read from
the smaller environment. This uses the existing `sptSubspt` relation as
Flapjack proof infrastructure. -/
theorem getVars_of_subspt {α : Type} (names : List Nat) (source target : Spt α)
    (values : List α) (included : sptSubspt source target)
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
theorem cutEnv_of_subspt {α : Type} (names : NumSet) (source target result : Spt α)
    (included : sptSubspt source target) (cut : DataSem.cutEnv names source = some result) :
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
  rw [ite_eq_left present] at cut
  rw [ite_eq_left targetPresent, ← interEq]
  exact cut

/-- Writing the same binding to extended environments preserves extension. -/
theorem insert_subspt {α : Type} (source target : Spt α) (key : Nat) (value : α)
    (included : sptSubspt source target) : sptSubspt (sptInsert key value source) (sptInsert key value target) := by
  rw [sptSubsptLookup] at included ⊢
  intro candidate found lookup
  by_cases same : candidate = key
  · subst candidate
    simpa [sptLookup_sptInsert_same] using lookup
  · rw [sptLookup_sptInsert_ne key candidate value source same] at lookup
    rw [sptLookup_sptInsert_ne key candidate value target same]
    exact included candidate found lookup

end Flapjack.Compiler.Backend.DataSpace

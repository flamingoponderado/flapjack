module

public import Flapjack.Compiler.Backend.Semantics.DataProps.Variables
public import Flapjack.Compiler.Backend.BviToData.Proofs.Value
public import Flapjack.Misc.Sptree.Map
public import Flapjack.Misc.Sptree.MkWf
public import Flapjack.Compiler.Backend.BviToData.Proofs.State
public import Flapjack.Compiler.Backend.Semantics.BviSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate

@[expose] public section

/-! Variable correspondence under BVI-to-data value projection. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack

/-- A correspondence in an intersection also holds in its left tree. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "var_corr_inter"]
theorem varCorr_inter {α β : Type} (right : Spt β) (left : Spt α) (names : List Nat) (values : List α)
    (related : DataProps.varCorr values names (sptInter left right)) :
    DataProps.varCorr values names left := by
  induction related with
  | nil => constructor
  | @cons name value names values lookup rest ih =>
    constructor
    · simp only [DataSem.getVar, sptLookup_sptInterCases] at lookup
      cases leftLookup : sptLookup name left <;> cases rightLookup : sptLookup name right <;>
        simp_all [DataSem.getVar]
    · exact ih

/-- Normalizing a local tree preserves successful variable-list reads. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "get_vars_mk_wf"]
theorem getVars_mkWf {α : Type} (names : List Nat) (env : Spt α) (values : List α) :
    DataSem.getVars names (sptMkWf env) = some values ↔ DataSem.getVars names env = some values := by
  induction names generalizing values with
  | nil => simp [DataSem.getVars]
  | cons name names ih =>
    simp only [DataSem.getVars, DataSem.getVar, sptLookup_mkWf]
    cases lookup : sptLookup name env with
    | none => simp
    | some value =>
      cases first : DataSem.getVars names (sptMkWf env) <;>
        cases second : DataSem.getVars names env <;> simp_all

/-- A successful read from an intersection is the same read from its left
tree; the right tree's payload type is independent. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "get_vars_inter"]
theorem getVars_inter {α β : Type} (names : List Nat) (left : Spt α) (right : Spt β) (values : List α)
    (read : DataSem.getVars names (sptInter left right) = some values) :
    DataSem.getVars names left = some values := by
  induction names generalizing values with
  | nil => simpa [DataSem.getVars] using read
  | cons name names ih =>
    simp only [DataSem.getVars, DataSem.getVar, sptLookup_sptInterCases] at read ⊢
    cases leftLookup : sptLookup name left <;> cases rightLookup : sptLookup name right <;> simp_all
    case some.some value _ =>
      cases rest : DataSem.getVars names (sptInter left right) with
      | none => simp [rest] at read
      | some tail =>
        simp [rest] at read
        subst values
        simp [ih tail rest]

/-- Mapping the environment and its corresponding values preserves the
variable correspondence. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "var_corr_map"]
theorem varCorr_map {α β : Type} (env : Spt α) (f : α → β) (names : List Nat) (values : List α)
    (related : DataProps.varCorr values names env) :
    DataProps.varCorr (values.map f) names (sptMap f env) := by
  induction related with
  | nil => constructor
  | cons lookup rest ih =>
    constructor
    · simpa [DataSem.getVar, sptLookup_sptMap] using congrArg (Option.map f) lookup
    · exact ih

/-- A variable correspondence in the projected environment lifts to the
actual data values read from the unprojected environment. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "get_vars_lift_thm"]
theorem getVars_lift (names : List Nat) (values : List BvlSem.Value)
    (env : Spt DataSem.Value) (related : DataProps.varCorr values names (sptMap dataToBviValue env)) :
    ∃ dataValues, DataSem.getVars names env = some dataValues ∧ values = dataValues.map dataToBviValue := by
  induction related with
  | nil => exact ⟨[], rfl, rfl⟩
  | @cons name value names values lookup rest ih =>
    simp only [DataSem.getVar, sptLookup_sptMap] at lookup
    cases found : sptLookup name env with
    | none => simp [found] at lookup
    | some dataValue =>
      simp only [found, Option.map_some, Option.some.injEq] at lookup
      obtain ⟨dataValues, read, projected⟩ := ih
      refine ⟨dataValue :: dataValues, ?_, ?_⟩
      · simp [DataSem.getVars, DataSem.getVar, found, read]
      · simp [← lookup, projected]

end Flapjack.Compiler.Backend.BviToData

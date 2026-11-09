module

public import Flapjack.Compiler.Backend.Semantics.DataProps.Variables
public import Flapjack.Compiler.Backend.BviToData.Proofs.Value
public import Flapjack.Misc.Sptree.Map
public import Flapjack.Misc.Sptree.MkWf
public import Flapjack.Compiler.Backend.BviToData.Proofs.State
public import Flapjack.Compiler.Backend.Semantics.BviSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate

-- Proofs below unfold the private error helpers of `BviSem.evaluate`.
import all Flapjack.Compiler.Backend.Semantics.BviSem.Evaluate
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

/-- The successful non-tail variable case reads the corresponding data local
and compiles to `skip`. This factored case is untagged: the full source case
also covers tail position and the complete compiler invariant. -/
theorem evaluateVar_nonTail {C F : Type} (index n : Nat) (names live : List Nat)
    (env : List BvlSem.Value) (source : BviSem.BviState C F) (target : DataSem.State C F)
    (value : BvlSem.Value) (related : stateRel source target)
    (varRel : DataProps.varCorr env names (sptMap dataToBviValue target.locals))
    (run : BviSem.evaluate [.var index] env source = (.val [value], source)) :
    ∃ name dataValue,
      names[index]? = some name ∧ DataSem.getVar name target.locals = some dataValue ∧
      dataToBviValue dataValue = value ∧
      compileSing n names false live (.var index) = (.skip, name, max n (name + 1)) ∧
      DataSem.evaluate .skip target = (none, target) ∧ stateRel source target := by
  cases found : env[index]? with
  | none => simp [BviSem.evaluate, found] at run
  | some foundValue =>
    simp [BviSem.evaluate, found] at run
    subst value
    obtain ⟨name, nameAt, valueAt⟩ := DataProps.varCorr_lookup env names
      (sptMap dataToBviValue target.locals) varRel index foundValue found
    simp only [DataSem.getVar, sptLookup_sptMap] at valueAt
    cases localFound : sptLookup name target.locals with
    | none => simp [localFound] at valueAt
    | some dataValue =>
      simp only [localFound, Option.map_some, Option.some.injEq] at valueAt
      refine ⟨name, dataValue, nameAt, ?_, valueAt, ?_, ?_, related⟩
      · simpa [DataSem.getVar] using localFound
      · simp [compileSing, nameAt]
      · simp [DataSem.evaluate]

/-- The successful tail variable case returns the corresponding data value,
preserving the state relation, stack, and handler after local-state flushing.
This factored case is untagged pending assembly with the full source invariant. -/
theorem evaluateVar_tail {C F : Type} (index n : Nat) (names live : List Nat)
    (env : List BvlSem.Value) (source : BviSem.BviState C F) (target : DataSem.State C F)
    (value : BvlSem.Value) (related : stateRel source target)
    (varRel : DataProps.varCorr env names (sptMap dataToBviValue target.locals))
    (run : BviSem.evaluate [.var index] env source = (.val [value], source)) :
    ∃ name dataValue,
      compileSing n names true live (.var index) = (.return [name], n, n + 1) ∧
      DataSem.evaluate (.return [name]) target =
        (some (.val [dataValue]), DataSem.flushState false target) ∧
      dataToBviValue dataValue = value ∧ stateRel source (DataSem.flushState false target) ∧
      (DataSem.flushState false target).stack = target.stack ∧
      (DataSem.flushState false target).handler = target.handler := by
  obtain ⟨name, dataValue, nameAt, read, projected, _, _, _⟩ :=
    evaluateVar_nonTail index n names live env source target value related varRel run
  refine ⟨name, dataValue, ?_, ?_, projected, ?_, ?_, ?_⟩
  · simp [compileSing, nameAt]
  · simp [DataSem.evaluate, DataSem.getVars, read]
  · simpa [stateRel, DataSem.flushState] using related
  · simp [DataSem.flushState]
  · simp [DataSem.flushState]

end Flapjack.Compiler.Backend.BviToData

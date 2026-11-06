import Flapjack.Compiler.Backend.FlatPattern.Proofs.DynamicEvaluation

/-! Empty-environment and unit-value relation helpers. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- The empty flat environments are related at every name bound. -/
theorem envRel_empty (n : Nat) : EnvRel n ⟨[]⟩ ⟨[]⟩ := by
  apply (envRel_iff_lookup n _ _).2
  exact aLookupRel_empty _ _

/-- A value related to unit is itself unit. -/
theorem valueRel_unit (value : FlatSem.Value) (related : ValueRel FlatSem.unitValue value) :
    value = FlatSem.unitValue := by
  obtain ⟨values, equal, fields⟩ := (valueRel_conv none [] value).1 related
  cases fields
  exact equal

end Flapjack.Compiler.Backend.FlatPattern

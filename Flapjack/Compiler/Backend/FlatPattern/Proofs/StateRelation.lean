import Flapjack.Compiler.Backend.FlatPattern.Proofs.ValueRelation
import Flapjack.Compiler.Backend.Semantics.FlatSem.Semantics
import Flapjack.SemanticPrimitivesProps.StoreRelation

/-! State relation for flat pattern compilation. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- The flat-pattern state relation, including installation configurations. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "state_rel_def"]
def StateRel {C F : Type} (cfg : Config) (source target : FlatSem.State C F) : Prop :=
  target.clock = source.clock ∧
  List.Forall₂ (storeValueRel ValueRel) source.refs target.refs ∧
  target.ffi = source.ffi ∧
  List.Forall₂ (optionRel ValueRel) source.globals target.globals ∧
  installConfRel cfg source.evalConfig target.evalConfig

/-- Initial flat states satisfy the relation when their installation
configurations are related. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "state_rel_initial_state"]
theorem stateRel_initial {C F : Type} (cfg : Config) (ffi : HolFfiState F) (clock : Nat)
    (source target : FlatSem.InstallConfig C) (related : installConfRel cfg source target) :
    StateRel cfg (FlatSem.initialState ffi clock source) (FlatSem.initialState ffi clock target) := by
  simp [StateRel, FlatSem.initialState, related]

end Flapjack.Compiler.Backend.FlatPattern

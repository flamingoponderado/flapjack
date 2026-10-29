import Flapjack.Compiler.Backend.FlatPattern.Proofs.ValueRelation
import Flapjack.Compiler.Backend.Semantics.FlatSem.Semantics
import Flapjack.SemanticPrimitivesProps.StoreRelation

/-! State relation for flat pattern compilation. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- Proof-side flat state relation. Its value relation uses the explicit
positivity rendering documented in `ValueRelation.lean`; correspondence to
the HOL `state_rel` declaration remains pending. -/
def StateRel {C F : Type} (cfg : Config) (source target : FlatSem.State C F) : Prop :=
  target.clock = source.clock ∧
  List.Forall₂ (storeValueRel ValueRel) source.refs target.refs ∧
  target.ffi = source.ffi ∧
  List.Forall₂ (optionRel ValueRel) source.globals target.globals ∧
  installConfRel cfg source.evalConfig target.evalConfig

/-- Initial flat states satisfy the proof-side state relation whenever their
installation configurations are related. This helper is not yet a reviewed
port of the corresponding HOL theorem. -/
theorem stateRel_initial {C F : Type} (cfg : Config) (ffi : HolFfiState F) (clock : Nat)
    (source target : FlatSem.InstallConfig C) (related : installConfRel cfg source target) :
    StateRel cfg (FlatSem.initialState ffi clock source) (FlatSem.initialState ffi clock target) := by
  simp [StateRel, FlatSem.initialState, related]

end Flapjack.Compiler.Backend.FlatPattern

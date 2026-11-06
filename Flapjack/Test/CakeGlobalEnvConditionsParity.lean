import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalEnvConditions

/-! Empty-map observations from `source_to_flat_global_env_probe.out`. -/
namespace Flapjack.Test.CakeGlobalEnvConditionsParity
open Flapjack Flapjack.Compiler.Backend.SourceToFlat

example : ¬ hasBools HolFiniteMapExact.empty := by simp [hasBools, HolFiniteMapExact.empty]
example : ¬ hasLists HolFiniteMapExact.empty := by simp [hasLists, HolFiniteMapExact.empty]
example : ¬ hasExns (HolFiniteMapExact.empty : HolFiniteMapExact ((Nat × Option Bool) × Nat)
    SemanticPrimitivesHOL.Stamp) := by simp [hasExns, HolFiniteMapExact.empty]
example : genvCTysOk (HolFiniteMapExact.empty : HolFiniteMapExact ((Nat × Option Bool) × Nat)
    SemanticPrimitivesHOL.Stamp) (HolFiniteMapExact.empty : HolFiniteMapExact Bool (List (Nat × Nat))) := by
  simp [genvCTysOk, HolFiniteMapExact.empty]

end Flapjack.Test.CakeGlobalEnvConditionsParity

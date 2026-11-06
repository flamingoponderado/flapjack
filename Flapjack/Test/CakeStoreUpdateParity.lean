import Flapjack.Compiler.Backend.SourceToFlat.Proofs.StoreUpdate

/-! Matched original HOL observations from `source_to_flat_state_pattern_probe.out`. -/
namespace Flapjack.Test.CakeStoreUpdateParity
open Flapjack.SemanticPrimitivesHOL

private def initial : Store Value := [.refv (.litv (.intLit 5))]
example : storeAlloc (.refv (.litv (.intLit 5)) : StoreValue Value) [] = (initial, 0) := by rfl
example : storeAssign 0 (.refv (.litv (.intLit 9))) initial = some [.refv (.litv (.intLit 9))] := by rfl
example : storeAssign 0 (.w8array [3]) initial = none := by rfl
example : storeAssign 1 (.refv (.litv (.intLit 9))) initial = none := by rfl
end Flapjack.Test.CakeStoreUpdateParity

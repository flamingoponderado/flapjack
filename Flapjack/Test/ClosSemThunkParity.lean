import Flapjack.Compiler.Backend.Semantics.ClosSem.Thunk

/-! Replay closure thunk observations from the pinned HOL probe. -/
namespace Flapjack.Test.ClosSemThunkParity
open Flapjack Flapjack.Compiler.Backend.ClosSem

private def unforced : HolFiniteMapExact Nat (Ref Value) :=
  HolFiniteMapExact.empty.updateEq (0, .thunk .notEvaluated (.number 5))
private def forced : HolFiniteMapExact Nat (Ref Value) :=
  HolFiniteMapExact.empty.updateEq (0, .thunk .evaluated (.number 5))
private def array : HolFiniteMapExact Nat (Ref Value) :=
  HolFiniteMapExact.empty.updateEq (0, .valueArray [.number 5])

example : destThunk [.refPtr false 0] HolFiniteMapExact.empty = .badRef := rfl
example : destThunk [.refPtr true 0] unforced = .badRef := rfl
example : destThunk [.refPtr false 0] unforced = .isThunk .notEvaluated (.number 5) := rfl
example : destThunk [.refPtr true 0] array = .notThunk := rfl
example : (updateThunk [.refPtr false 0] unforced [.number 7]).map (fun refs => refs.lookup 0) =
    some (some (.thunk .evaluated (.number 7))) := rfl
example : updateThunk [.refPtr false 0] forced [.number 7] = none := rfl
example : updateThunk [.refPtr false 0] unforced [.refPtr false 0] = none := rfl

end Flapjack.Test.ClosSemThunkParity

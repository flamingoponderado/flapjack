module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Safety

@[expose] public section

/-! Control-flow cases of the proof-side annotation simulation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Related values have the same Boolean observation. -/
theorem valueRel_asBool {left right : Value} (related : ValueRel left right) : asBool left = asBool right := by
  cases related with
  | block tag left right entries =>
    cases entries with
    | nil => rfl
    | cons head tail => cases tag <;> simp [asBool]
  | number _ | word64 _ | byteVector _ | refPtr _ _ => rfl
  | closure => rfl
  | recclosure => rfl

end Flapjack.Compiler.Backend.ClosAnnotate

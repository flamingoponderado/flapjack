module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Heap

@[expose] public section

/-! Space consumption commutes with independent state-field updates. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Reserving then consuming the same amount leaves zero reserved space. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "consume_space_add_space"]
theorem consumeSpace_addSpace {C F : Type} (amount : Nat) (state : State C F)
    (env : Spt DataSem.Value) :
    ∃ safe peak, consumeSpace amount (addSpace { state with locals := env } amount) =
      some { state with locals := env, space := 0, safeForSpace := safe, peakHeapLength := peak } := by
  refine ⟨(addSpace { state with locals := env } amount).safeForSpace,
    (addSpace { state with locals := env } amount).peakHeapLength, ?_⟩
  simp [consumeSpace, addSpace]

/-- Stack updates commute with space consumption. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "consume_space_with_stack"]
theorem consumeSpace_withStack {C F : Type} (amount : Nat) (state : State C F) (stack : List Stack) :
    consumeSpace amount { state with stack := stack } =
      (consumeSpace amount state).map (fun s => { s with stack := stack }) := by
  simp [consumeSpace]
  split <;> rfl

/-- Local-variable updates commute with space consumption. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "consume_space_with_locals"]
theorem consumeSpace_withLocals {C F : Type} (amount : Nat) (state : State C F)
    (locals : Spt DataSem.Value) :
    consumeSpace amount { state with locals := locals } =
      (consumeSpace amount state).map (fun s => { s with locals := locals }) := by
  simp [consumeSpace]
  split <;> rfl

end Flapjack.Compiler.Backend.DataProps

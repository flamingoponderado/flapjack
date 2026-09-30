import Flapjack.Compiler.Backend.Semantics.StackSem.LeafTransfers

/-! All sixteen original HOL leaf-transfer observations, over any base state.
Every field read by these cases is overridden, and the observer checks result,
clock, stack length and a register lookup after cleanup. -/
namespace Flapjack.Test.StackSemLeafTransfersParity
open StackSemLeafTransfers
private def fixture {C F : Type} (s : StackSemStateFiniteExact 8 C F) (clock : Nat) :=
  { s with
    clock := clock
    stack := [.word 9]
    regs := ((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 8)).updateEq
      (1, .word 7)).updateEq (2, .loc 4 5) }
private def observe {C F : Type} :
    Option (Option (StackSemResult 8) × StackSemStateFiniteExact 8 C F) →
    Option (Option (StackSemResult 8) × Nat × Nat × Option (WordLocW 8))
  | none => none
  | some (r, s) => some (r, s.clock, s.stack.length, s.regs.lookup 1)
variable {C F : Type} (s : StackSemStateFiniteExact 8 C F)
-- skip
example : observe (evaluateLeaf (.skip) (fixture s 1)) =
    some (none, 1, 1, some (.word 7)) := by cbv
-- halt_word
example : observe (evaluateLeaf (.halt 1) (fixture s 1)) =
    some (some (.halt (.word 7)), 1, 0, none) := by cbv
-- halt_loc
example : observe (evaluateLeaf (.halt 2) (fixture s 1)) =
    some (some (.halt (.loc 4 5)), 1, 0, none) := by cbv
-- halt_missing
example : observe (evaluateLeaf (.halt 3) (fixture s 1)) =
    some (some .error, 1, 1, some (.word 7)) := by cbv
-- tick_zero
example : observe (evaluateLeaf (.tick) (fixture s 0)) =
    some (some .timeOut, 0, 0, none) := by cbv
-- tick_one
example : observe (evaluateLeaf (.tick) (fixture s 1)) =
    some (none, 0, 1, some (.word 7)) := by cbv
-- return_loc
example : observe (evaluateLeaf (.ret 2) (fixture s 1)) =
    some (some (.result (.loc 4 5)), 1, 1, some (.word 7)) := by cbv
-- return_word
example : observe (evaluateLeaf (.ret 1) (fixture s 1)) =
    some (some .error, 1, 1, some (.word 7)) := by cbv
-- return_missing
example : observe (evaluateLeaf (.ret 3) (fixture s 1)) =
    some (some .error, 1, 1, some (.word 7)) := by cbv
-- raise_loc
example : observe (evaluateLeaf (.raise 2) (fixture s 1)) =
    some (some (.exception (.loc 4 5)), 1, 1, some (.word 7)) := by cbv
-- raise_word
example : observe (evaluateLeaf (.raise 1) (fixture s 1)) =
    some (some .error, 1, 1, some (.word 7)) := by cbv
-- raise_missing
example : observe (evaluateLeaf (.raise 3) (fixture s 1)) =
    some (some .error, 1, 1, some (.word 7)) := by cbv
-- break_zero
example : observe (evaluateLeaf (.break 0) (fixture s 1)) =
    some (some (.break 0), 1, 1, some (.word 7)) := by cbv
-- break_three
example : observe (evaluateLeaf (.break 3) (fixture s 1)) =
    some (some (.break 3), 1, 1, some (.word 7)) := by cbv
-- continue_zero
example : observe (evaluateLeaf (.continue 0) (fixture s 1)) =
    some (some (.continue 0), 1, 1, some (.word 7)) := by cbv
-- continue_three
example : observe (evaluateLeaf (.continue 3) (fixture s 1)) =
    some (some (.continue 3), 1, 1, some (.word 7)) := by cbv

-- The outer NONE records missing dispatch, not a successful empty result or Error.
example : evaluateLeaf (.seq .skip .skip) (fixture s 1) = none := rfl
end Flapjack.Test.StackSemLeafTransfersParity

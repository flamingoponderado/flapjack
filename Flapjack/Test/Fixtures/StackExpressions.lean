import Flapjack.Compiler.Backend.Semantics.StackSem.Expressions

/-!
# Shared stackSem expression fixtures

The `fixture` and the two `assign` rows shared by
`Flapjack/Test/StackSemExpressionParity.lean` and
`Flapjack/Test/StackPropsExpressionClockParity.lean`. The arbitrary base state
has every expression-observable field overridden; `assign` does not read the
clock, so the same rows hold for both probes.
-/

namespace Flapjack.Test.Fixtures.StackExpressions

open Flapjack Flapjack.StackSemExpressions

/-- The arbitrary base state with every expression-observable field overridden. -/
def fixture {C F : Type} (s : StackSemStateFiniteExact 8 C F) :=
  {s with regs := ((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 8)).updateEq (1,.word 7)).updateEq (2,.loc 4 5), store := ((HolFiniteMapExact.empty : HolFiniteMapExact WordStoreHOL (WordLocW 8)).updateEq (.allocSize,.word 9)).updateEq (.nextFree,.loc 2 3), memory := fun a => if a = 0 then .word 11 else .loc 8 9, mdomain := fun a => a = 0 ∨ a = 1}

theorem assignSuccess {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    (assign 1 (.const 12) (fixture s)).map
      (fun t => (t.regs.lookup 1, t.regs.lookup 2)) =
      some (some (.word 12), some (.loc 4 5)) := by cbv

theorem assignFailure {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    (assign 1 (.var 2) (fixture s)).map
      (fun t => (t.regs.lookup 1, t.regs.lookup 2)) = none := by cbv

end Flapjack.Test.Fixtures.StackExpressions

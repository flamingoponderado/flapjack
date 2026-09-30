import Flapjack.Compiler.Backend.Semantics.StackSem.RegisterTransfers

/-! Kernel replay of all thirteen original StackSem register-transfer probe rows.
The fixture overrides every observed field over an arbitrary base state. -/
namespace Flapjack.Test.StackSemRegisterTransfersParity
open StackSemRegisterTransfers
private def fixture {C F : Type} (s : StackSemStateFiniteExact 8 C F) (enabled : Bool) :=
  { s with
    clock := 6
    useStore := enabled
    regs := ((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 8)).updateEq
      (1, .word 7)).updateEq (2, .loc 4 5)
    store := ((HolFiniteMapExact.empty : HolFiniteMapExact WordStoreHOL (WordLocW 8)).updateEq
      (.currHeap, .word 10)).updateEq (.handler, .loc 8 9) }
private def observe {C F : Type} :
    Option (Option (StackSemResult 8) × StackSemStateFiniteExact 8 C F) →
    Option (Option (StackSemResult 8) × Nat × Option (WordLocW 8) × Option (WordLocW 8))
  | none => none
  | some (r, s) => some (r, s.clock, s.regs.lookup 3, s.store.lookup .currHeap)
variable {C F : Type} (s : StackSemStateFiniteExact 8 C F)
-- get_word
example : observe (evaluateRegister (.get 3 .currHeap) (fixture s true)) =
    some (none, 6, some (.word 10), some (.word 10)) := by cbv
-- get_loc
example : observe (evaluateRegister (.get 3 .handler) (fixture s true)) =
    some (none, 6, some (.loc 8 9), some (.word 10)) := by cbv
-- get_missing
example : observe (evaluateRegister (.get 3 .globals) (fixture s true)) =
    some (some .error, 6, none, some (.word 10)) := by cbv
-- get_disabled
example : observe (evaluateRegister (.get 3 .currHeap) (fixture s false)) =
    some (some .error, 6, none, some (.word 10)) := by cbv
-- set_word
example : observe (evaluateRegister (.set .currHeap 1) (fixture s true)) =
    some (none, 6, none, some (.word 7)) := by cbv
-- set_loc
example : observe (evaluateRegister (.set .currHeap 2) (fixture s true)) =
    some (none, 6, none, some (.loc 4 5)) := by cbv
-- set_missing
example : observe (evaluateRegister (.set .currHeap 4) (fixture s true)) =
    some (some .error, 6, none, some (.word 10)) := by cbv
-- set_disabled
example : observe (evaluateRegister (.set .currHeap 1) (fixture s false)) =
    some (some .error, 6, none, some (.word 10)) := by cbv
-- op_add
example : observe (evaluateRegister (.opCurrHeap .add 3 1) (fixture s true)) =
    some (none, 6, some (.word 17), some (.word 10)) := by cbv
-- op_sub
example : observe (evaluateRegister (.opCurrHeap .sub 3 1) (fixture s true)) =
    some (none, 6, some (.word 253), some (.word 10)) := by cbv
-- op_loc
example : observe (evaluateRegister (.opCurrHeap .add 3 2) (fixture s true)) =
    some (some .error, 6, none, some (.word 10)) := by cbv
-- op_missing
example : observe (evaluateRegister (.opCurrHeap .add 3 4) (fixture s true)) =
    some (some .error, 6, none, some (.word 10)) := by cbv
-- op_disabled
example : observe (evaluateRegister (.opCurrHeap .add 3 1) (fixture s false)) =
    some (some .error, 6, none, some (.word 10)) := by cbv
end Flapjack.Test.StackSemRegisterTransfersParity

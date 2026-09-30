import Flapjack.Compiler.Backend.Semantics.StackSem.Expressions

open Flapjack Flapjack.StackSemExpressions

/- Kernel replay of scripts/hol-probes/stacksem_expression_probe.out.
The arbitrary base state has every expression-observable field overridden. -/
private def fixture {C F : Type} (s : StackSemStateFiniteExact 8 C F) :=
  {s with regs := ((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 8)).updateEq (1,.word 7)).updateEq (2,.loc 4 5), store := ((HolFiniteMapExact.empty : HolFiniteMapExact WordStoreHOL (WordLocW 8)).updateEq (.allocSize,.word 9)).updateEq (.nextFree,.loc 2 3), memory := fun a => if a = 0 then .word 11 else .loc 8 9, mdomain := fun a => a = 0 ∨ a = 1}

variable {C F : Type} (s : StackSemStateFiniteExact 8 C F)
-- const
example : wordExp (fixture s) (.const 255) = some 255 := by cbv
-- var_word
example : wordExp (fixture s) (.var 1) = some 7 := by cbv
-- var_loc
example : wordExp (fixture s) (.var 2) = none := by cbv
-- var_missing
example : wordExp (fixture s) (.var 3) = none := by cbv
-- lookup_word
example : wordExp (fixture s) (.lookup .allocSize) = some 9 := by cbv
-- lookup_loc
example : wordExp (fixture s) (.lookup .nextFree) = none := by cbv
-- lookup_missing
example : wordExp (fixture s) (.lookup .triggerGC) = none := by cbv
-- load_word
example : wordExp (fixture s) (.load (.const 0)) = some 11 := by cbv
-- load_loc
example : wordExp (fixture s) (.load (.const 1)) = none := by cbv
-- load_oob
example : wordExp (fixture s) (.load (.const 2)) = none := by cbv
-- load_bad_address
example : wordExp (fixture s) (.load (.var 2)) = none := by cbv
-- op_empty_and
example : wordExp (fixture s) (.op .and []) = some 255 := by cbv
-- op_add_wrap
example : wordExp (fixture s) (.op .add [.const 255,.const 2]) = some 1 := by cbv
-- op_sub_bad_arity
example : wordExp (fixture s) (.op .sub [.const 1]) = none := by cbv
-- op_bad_operand
example : wordExp (fixture s) (.op .add [.const 1,.var 2]) = none := by cbv
-- shift_valid
example : wordExp (fixture s) (.shift .lsl (.const 3) (.const 2)) = some 12 := by cbv
-- shift_oob
example : wordExp (fixture s) (.shift .lsl (.const 3) (.const 8)) = none := by cbv
-- shift_bad_right
example : wordExp (fixture s) (.shift .lsr (.const 3) (.var 2)) = none := by cbv
-- assign_success
example : (assign 1 (.const 12) (fixture s)).map
    (fun t => (t.regs.lookup 1,t.regs.lookup 2)) =
    some (some (.word 12),some (.loc 4 5)) := by cbv
-- assign_failure
example : (assign 1 (.var 2) (fixture s)).map
    (fun t => (t.regs.lookup 1,t.regs.lookup 2)) = none := by cbv

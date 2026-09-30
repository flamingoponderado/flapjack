import Flapjack.Compiler.Backend.Semantics.StackSem.FixedStackCases
open Flapjack Flapjack.StackSemFixedStackCases

/- Original observations: scripts/hol-probes/stacksem_fixed_stack_probe.out.
HOL Word 260w at width8 represents the same modular word as Lean ofNat8 260. -/
private def fixture {C F : Type} (s : StackSemStateFiniteExact 8 C F)
    (useStack : Bool) (space : Nat) (regs : HolFiniteMapExact Nat (WordLocW 8)) :=
  { s with
    useStack := useStack
    stackSpace := space
    regs := regs
    stack := [.word 11, .loc 3 4]
    clock := 17
    memory := fun _ => .word 23 }
private def observe {C F : Type}
    (result : Option (StackSemResult 8) × StackSemStateFiniteExact 8 C F) :=
  (result.1, result.2.regs.lookup 7, result.2.stack, result.2.stackSpace,
    result.2.clock, result.2.memory 0)
variable {C F : Type} (s : StackSemStateFiniteExact 8 C F)

-- stack_alloc_disabled
example : observe (stackAlloc 1 (fixture s false 1 (HolFiniteMapExact.empty.updateEq (7, .word 9)))) =
    (some .error,some (.word 9),[.word 11, .loc 3 4],1,17,.word 23) := by cbv

-- stack_alloc_success
example : observe (stackAlloc 1 (fixture s true 2 (HolFiniteMapExact.empty.updateEq (7, .word 9)))) =
    (none,some (.word 9),[.word 11, .loc 3 4],1,17,.word 23) := by cbv

-- stack_alloc_boundary
example : observe (stackAlloc 2 (fixture s true 2 (HolFiniteMapExact.empty.updateEq (7, .word 9)))) =
    (none,some (.word 9),[.word 11, .loc 3 4],0,17,.word 23) := by cbv

-- stack_alloc_exhausted
example : observe (stackAlloc 3 (fixture s true 2 (HolFiniteMapExact.empty.updateEq (7, .word 9)))) =
    (some (.halt (.word 2)),none,[],2,17,.word 23) := by cbv

-- stack_free_boundary
example : observe (stackFree 2 (fixture s true 0 (HolFiniteMapExact.empty.updateEq (7, .word 9)))) =
    (none,some (.word 9),[.word 11, .loc 3 4],2,17,.word 23) := by cbv

-- stack_free_excess
example : observe (stackFree 3 (fixture s true 0 (HolFiniteMapExact.empty.updateEq (7, .word 9)))) =
    (some .error,none,[],0,17,.word 23) := by cbv

-- stack_free_disabled
example : observe (stackFree 1 (fixture s false 0 (HolFiniteMapExact.empty.updateEq (7, .word 9)))) =
    (some .error,some (.word 9),[.word 11, .loc 3 4],0,17,.word 23) := by cbv

-- stack_load_loc
example : observe (stackLoad 7 1 (fixture s true 0 (HolFiniteMapExact.empty.updateEq (7, .word 9)))) =
    (none,some (.loc 3 4),[.word 11, .loc 3 4],0,17,.word 23) := by cbv

-- stack_load_boundary
example : observe (stackLoad 7 2 (fixture s true 0 (HolFiniteMapExact.empty.updateEq (7, .word 9)))) =
    (some .error,none,[],0,17,.word 23) := by cbv

-- stack_load_disabled
example : observe (stackLoad 7 1 (fixture s false 0 (HolFiniteMapExact.empty.updateEq (7, .word 9)))) =
    (some .error,some (.word 9),[.word 11, .loc 3 4],0,17,.word 23) := by cbv

-- stack_store_loc
example : observe (stackStore 7 0 (fixture s true 0 (HolFiniteMapExact.empty.updateEq (7, .loc 5 6)))) =
    (none,some (.loc 5 6),[.loc 5 6, .loc 3 4],0,17,.word 23) := by cbv

-- stack_store_missing
example : observe (stackStore 7 0 (fixture s true 0 HolFiniteMapExact.empty)) =
    (some .error,none,[],0,17,.word 23) := by cbv

-- stack_store_boundary
example : observe (stackStore 7 2 (fixture s true 0 (HolFiniteMapExact.empty.updateEq (7, .word 9)))) =
    (some .error,none,[],0,17,.word 23) := by cbv

-- stack_store_disabled
example : observe (stackStore 7 0 (fixture s false 0 (HolFiniteMapExact.empty.updateEq (7, .word 9)))) =
    (some .error,some (.word 9),[.word 11, .loc 3 4],0,17,.word 23) := by cbv

-- stack_size_modular
example : observe (stackGetSize 7 (fixture s true 260 (HolFiniteMapExact.empty.updateEq (7, .word 9)))) =
    (none,some (.word 260),[.word 11, .loc 3 4],260,17,.word 23) := by cbv

-- stack_size_disabled
example : observe (stackGetSize 7 (fixture s false 260 (HolFiniteMapExact.empty.updateEq (7, .word 9)))) =
    (some .error,some (.word 9),[.word 11, .loc 3 4],260,17,.word 23) := by cbv

-- stack_size_unsigned: explicit w2n confirms width8 modular truncation.
example : let result := stackGetSize 7 (fixture s true 260 HolFiniteMapExact.empty)
    (result.1, (result.2.regs.lookup 7).map (fun value => match value with
      | .word w => w.toNat | .loc _ _ => 999)) = (none, some 4) := by cbv

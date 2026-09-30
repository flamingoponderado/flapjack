import Flapjack.Compiler.Backend.Semantics.StackSem.DynamicStackCases
open Flapjack Flapjack.StackSemDynamicStackCases

/- Kernel replay of scripts/hol-probes/stacksem_dynamic_stack_probe.out.
Expected outcomes below are the independently captured original HOL results. -/
private def fixture {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (useStack : Bool) (space : Nat)
    (regs : HolFiniteMapExact Nat (WordLocW width)) :=
  { s with
    useStack := useStack
    stackSpace := space
    regs := regs
    stack := [.word 11, .loc 3 4]
    clock := 17
    memory := fun _ => .word 23 }
private def observe {width : Nat} [NeZero width] {C F : Type}
    (result : Option (StackSemResult width) × StackSemStateFiniteExact width C F) :=
  (result.1, result.2.regs.lookup 7, result.2.stack, result.2.stackSpace,
    result.2.clock, result.2.memory 0)

-- any_load_disabled
example {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    observe (stackLoadAny 7 8 (fixture s false 0 ((HolFiniteMapExact.empty.updateEq (7, .word 9)).updateEq (8, .word 8)))) =
    (some .error,some (.word 9),[.word 11, .loc 3 4],0,17,(.word 23)) := by cbv

-- any_load_loc
example {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    observe (stackLoadAny 7 8 (fixture s true 0 (HolFiniteMapExact.empty.updateEq (8, .word 8)))) =
    (none,some (.loc 3 4),[.word 11, .loc 3 4],0,17,(.word 23)) := by cbv

-- any_load_alias
example {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    observe (stackLoadAny 7 7 (fixture s true 0 (HolFiniteMapExact.empty.updateEq (7, .word 8)))) =
    (none,some (.loc 3 4),[.word 11, .loc 3 4],0,17,(.word 23)) := by cbv

-- any_load_missing
example {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    observe (stackLoadAny 7 8 (fixture s true 0 HolFiniteMapExact.empty)) =
    (some .error,none,[],0,17,(.word 23)) := by cbv

-- any_load_offset_loc
example {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    observe (stackLoadAny 7 8 (fixture s true 0 (HolFiniteMapExact.empty.updateEq (8, .loc 3 4)))) =
    (some .error,none,[],0,17,(.word 23)) := by cbv

-- any_load_unaligned
example {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    observe (stackLoadAny 7 8 (fixture s true 0 (HolFiniteMapExact.empty.updateEq (8, .word 1)))) =
    (some .error,none,[],0,17,(.word 23)) := by cbv

-- any_load_boundary
example {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    observe (stackLoadAny 7 8 (fixture s true 0 (HolFiniteMapExact.empty.updateEq (8, .word 16)))) =
    (some .error,none,[],0,17,(.word 23)) := by cbv

-- any_load_space
example {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    observe (stackLoadAny 7 8 (fixture s true 1 (HolFiniteMapExact.empty.updateEq (8, .word 0)))) =
    (none,some (.loc 3 4),[.word 11, .loc 3 4],1,17,(.word 23)) := by cbv

-- any_store_loc
example {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    observe (stackStoreAny 7 8 (fixture s true 0 ((HolFiniteMapExact.empty.updateEq (7, .loc 5 6)).updateEq (8, .word 8)))) =
    (none,some (.loc 5 6),[.word 11, .loc 5 6],0,17,(.word 23)) := by cbv

-- any_store_alias
example {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    observe (stackStoreAny 7 7 (fixture s true 0 (HolFiniteMapExact.empty.updateEq (7, .word 8)))) =
    (none,some (.word 8),[.word 11, .word 8],0,17,(.word 23)) := by cbv

-- any_store_missing
example {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    observe (stackStoreAny 7 8 (fixture s true 0 (HolFiniteMapExact.empty.updateEq (8, .word 8)))) =
    (some .error,none,[],0,17,(.word 23)) := by cbv

-- any_store_offset_missing
example {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    observe (stackStoreAny 7 8 (fixture s true 0 (HolFiniteMapExact.empty.updateEq (7, .word 9)))) =
    (some .error,none,[],0,17,(.word 23)) := by cbv

-- any_store_offset_loc
example {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    observe (stackStoreAny 7 8 (fixture s true 0 ((HolFiniteMapExact.empty.updateEq (7, .word 9)).updateEq (8, .loc 3 4)))) =
    (some .error,none,[],0,17,(.word 23)) := by cbv

-- any_store_unaligned
example {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    observe (stackStoreAny 7 8 (fixture s true 0 ((HolFiniteMapExact.empty.updateEq (7, .word 9)).updateEq (8, .word 9)))) =
    (some .error,none,[],0,17,(.word 23)) := by cbv

-- any_store_boundary
example {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    observe (stackStoreAny 7 8 (fixture s true 0 ((HolFiniteMapExact.empty.updateEq (7, .word 9)).updateEq (8, .word 16)))) =
    (some .error,none,[],0,17,(.word 23)) := by cbv

-- any_store_disabled
example {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    observe (stackStoreAny 7 8 (fixture s false 0 ((HolFiniteMapExact.empty.updateEq (7, .word 9)).updateEq (8, .word 8)))) =
    (some .error,some (.word 9),[.word 11, .loc 3 4],0,17,(.word 23)) := by cbv

-- any_load_width32
example {C F : Type} (s : StackSemStateFiniteExact 32 C F) :
    observe (stackLoadAny 7 8 (fixture s true 0 (HolFiniteMapExact.empty.updateEq (8, .word 4)))) =
    (none,some (.loc 3 4),[.word 11, .loc 3 4],0,17,(.word 23)) := by cbv

-- any_load_width64
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (stackLoadAny 7 8 (fixture s true 0 (HolFiniteMapExact.empty.updateEq (8, .word 8)))) =
    (none,some (.loc 3 4),[.word 11, .loc 3 4],0,17,(.word 23)) := by cbv

-- any_load_width1_zero
example {C F : Type} (s : StackSemStateFiniteExact 1 C F) :
    observe (stackLoadAny 7 8 (fixture s true 0 (HolFiniteMapExact.empty.updateEq (8, .word 0)))) =
    (none,some (.word 11),[.word 11, .loc 3 4],0,17,(.word 23)) := by cbv

-- any_load_width1_nonzero
example {C F : Type} (s : StackSemStateFiniteExact 1 C F) :
    observe (stackLoadAny 7 8 (fixture s true 0 (HolFiniteMapExact.empty.updateEq (8, .word 1)))) =
    (some .error,none,[],0,17,(.word 23)) := by cbv

import Flapjack.Compiler.Backend.Semantics.StackSem.SizeBitmapCases
open Flapjack Flapjack.StackSemSizeBitmapCases
/- Original observations: scripts/hol-probes/stacksem_size_bitmap_probe.out.
RHS assembly replay, not a total evaluator theorem. -/
private def fixture {C F : Type} (s : StackSemStateFiniteExact 8 C F)
    (useStack : Bool) (regs : HolFiniteMapExact Nat (WordLocW 8)) :=
  { s with
    useStack := useStack
    regs := regs
    stack := [.word 11, .loc 3 4]
    bitmaps := [13, 29]
    stackSpace := 5
    clock := 17
    memory := fun _ => .word 23 }
private def observe {C F : Type}
    (result : Option (StackSemResult 8) × StackSemStateFiniteExact 8 C F) :=
  (result.1, result.2.regs.lookup 7, result.2.regs.lookup 8, result.2.stack,
    result.2.stackSpace, result.2.clock, result.2.memory 0, result.2.bitmaps)
variable {C F : Type} (s : StackSemStateFiniteExact 8 C F)

-- size_disabled
example : observe (stackSetSize 7 (fixture s false (HolFiniteMapExact.empty.updateEq (7, .word 1)))) =
    (some .error, some (.word 1), none, [.word 11, .loc 3 4], 5, 17, .word 23, [13, 29]) := by cbv

-- size_success
example : observe (stackSetSize 7 (fixture s true (HolFiniteMapExact.empty.updateEq (7, .word 1)))) =
    (none, some (.word 8), none, [.word 11, .loc 3 4], 1, 17, .word 23, [13, 29]) := by cbv

-- size_boundary
example : observe (stackSetSize 7 (fixture s true (HolFiniteMapExact.empty.updateEq (7, .word 2)))) =
    (some .error, none, none, [], 5, 17, .word 23, [13, 29]) := by cbv

-- size_loc
example : observe (stackSetSize 7 (fixture s true (HolFiniteMapExact.empty.updateEq (7, .loc 3 4)))) =
    (some .error, some (.loc 3 4), none, [.word 11, .loc 3 4], 5, 17, .word 23, [13, 29]) := by cbv

-- size_missing
example : observe (stackSetSize 7 (fixture s true (HolFiniteMapExact.empty))) =
    (some .error, none, none, [.word 11, .loc 3 4], 5, 17, .word 23, [13, 29]) := by cbv

-- bitmap_disabled
example : observe (bitmapLoad 7 8 (fixture s false (HolFiniteMapExact.empty.updateEq (8, .word 1)))) =
    (some .error, none, some (.word 1), [.word 11, .loc 3 4], 5, 17, .word 23, [13, 29]) := by cbv

-- bitmap_success
example : observe (bitmapLoad 7 8 (fixture s true (HolFiniteMapExact.empty.updateEq (8, .word 1)))) =
    (none, some (.word 29), some (.word 1), [.word 11, .loc 3 4], 5, 17, .word 23, [13, 29]) := by cbv

-- bitmap_boundary
example : observe (bitmapLoad 7 8 (fixture s true (HolFiniteMapExact.empty.updateEq (8, .word 2)))) =
    (some .error, none, some (.word 2), [.word 11, .loc 3 4], 5, 17, .word 23, [13, 29]) := by cbv

-- bitmap_loc
example : observe (bitmapLoad 7 8 (fixture s true (HolFiniteMapExact.empty.updateEq (8, .loc 3 4)))) =
    (some .error, none, some (.loc 3 4), [.word 11, .loc 3 4], 5, 17, .word 23, [13, 29]) := by cbv

-- bitmap_missing
example : observe (bitmapLoad 7 8 (fixture s true (HolFiniteMapExact.empty))) =
    (some .error, none, none, [.word 11, .loc 3 4], 5, 17, .word 23, [13, 29]) := by cbv

-- bitmap_alias
example : observe (bitmapLoad 8 8 (fixture s true (HolFiniteMapExact.empty.updateEq (8, .word 1)))) =
    (some .error, none, some (.word 1), [.word 11, .loc 3 4], 5, 17, .word 23, [13, 29]) := by cbv

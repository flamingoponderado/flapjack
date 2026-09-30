import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateAllocCase

open Flapjack Flapjack.StackSemEvaluateAlloc

private def allocCaseFixture {C F : Type} (state : StackSemStateFiniteExact 8 C F)
    (useAlloc : Bool) (registers : HolFiniteMapExact Nat (WordLocW 8)) :
    StackSemStateFiniteExact 8 C F :=
  { state with
    regs := registers
    stack := [.word 0]
    stackSpace := 0
    memory := fun _ => .word 0
    mdomain := fun _ => true
    bitmaps := []
    store := ((HolFiniteMapExact.empty.updateEq (.allocSize, .word 4)).updateEq
      (.nextFree, .word 5)).updateEq (.triggerGC, .word 20)
    gcFun := fun (roots, memory, _, store) => some (roots, memory, store)
    useAlloc := useAlloc }

private def allocCaseObservation {C F : Type}
    (result : Option (StackSemResult 8) × StackSemStateFiniteExact 8 C F) :=
  (result.1, result.2.regs.lookup 9, result.2.stack, result.2.store.lookup .allocSize)

/- Original HOL observations: scripts/hol-probes/stacksem_evaluate_alloc_probe.out.
The fixtures inspect the result and fields touched by the evaluator branch. -/
variable {C F : Type} (state : StackSemStateFiniteExact 8 C F)

-- evaluate_alloc_disabled: use_alloc=false preserves the original state.
example : allocCaseObservation (evaluateAllocCase 9
    (allocCaseFixture state false (HolFiniteMapExact.empty.updateEq (9, .word 10)))) =
    (some .error, some (.word 10), [.word 0], some (.word 4)) := by
  simp [allocCaseObservation, evaluateAllocCase, allocCaseFixture,
    FUPDATE_HOL]

-- evaluate_alloc_missing: enabled allocation with a missing register is Error.
example : allocCaseObservation (evaluateAllocCase 9
    (allocCaseFixture state true HolFiniteMapExact.empty)) =
    (some .error, none, [.word 0], some (.word 4)) := by
  simp [allocCaseObservation, evaluateAllocCase, allocCaseFixture,
    StackSemStateOps.getVar, FUPDATE_HOL]

-- evaluate_alloc_location: a Loc operand is not an allocation size.
example : allocCaseObservation (evaluateAllocCase 9
    (allocCaseFixture state true (HolFiniteMapExact.empty.updateEq (9, .loc 3 4)))) =
    (some .error, some (.loc 3 4), [.word 0], some (.word 4)) := by
  simp [allocCaseObservation, evaluateAllocCase, allocCaseFixture,
    StackSemStateOps.getVar, FUPDATE_HOL]

-- evaluate_alloc_word: successful input dispatch reaches the exact alloc helper.
example : allocCaseObservation (evaluateAllocCase 9
    (allocCaseFixture state true (HolFiniteMapExact.empty.updateEq (9, .word 10)))) =
    (none, none, [.word 0], some (.word 10)) := by
  simp [allocCaseObservation, evaluateAllocCase, allocCaseFixture,
    StackSemStateOps.getVar, FUPDATE_HOL, StackSemAllocation.alloc,
    StackSemAllocation.gc, StackSemAllocation.hasSpace, StackSemStateOps.setStore,
    StackSem.encStack, StackSem.decStack]

private def gcCaseFixture {C F : Type} (state : StackSemStateFiniteExact 8 C F)
    (mode : Nat) : StackSemStateFiniteExact 8 C F :=
  { allocCaseFixture state true (HolFiniteMapExact.empty.updateEq (9, .word 10)) with
    gcFun := fun (roots, memory, _, _) =>
      match mode with
      | 0 => none
      | 1 => some (roots, memory, HolFiniteMapExact.empty)
      | 2 => some (roots, memory,
          ((HolFiniteMapExact.empty.updateEq (.allocSize, .word 10)).updateEq
            (.nextFree, .loc 1 2)).updateEq (.triggerGC, .word 20))
      | _ => some (roots, memory,
          ((HolFiniteMapExact.empty.updateEq (.allocSize, .word 30)).updateEq
            (.nextFree, .word 5)).updateEq (.triggerGC, .word 20)) }

-- GC failure restores the original register and allocation-size field.
example : allocCaseObservation (evaluateAllocCase 9 (gcCaseFixture state 0)) =
    (some .error, some (.word 10), [.word 0], some (.word 4)) := by cbv

-- Successful GC with no AllocSize retains the collected, cleared-register state.
example : allocCaseObservation (evaluateAllocCase 9 (gcCaseFixture state 1)) =
    (some .error, none, [.word 0], none) := by cbv

-- A location-valued NextFree is an error after GC, with the GC store retained.
example : allocCaseObservation (evaluateAllocCase 9 (gcCaseFixture state 2)) =
    (some .error, none, [.word 0], some (.word 10)) := by cbv

-- Exhaustion halts with Word 1 and empties the collected environment.
example : allocCaseObservation (evaluateAllocCase 9 (gcCaseFixture state 3)) =
    (some (.halt (.word 1)), none, [], some (.word 30)) := by cbv

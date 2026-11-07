import Flapjack.RiscV.CakeAllocatorCore

/-!
# Executable checks for the CakeML IRC allocator core

These checks pin the frame-relevant decisions of `Flapjack.RiscV.CakeAlloc`
(`Flapjack/RiscV/CakeAllocatorCore.lean`), the ported core of CakeML's
`compiler/backend/reg_alloc/reg_allocScript.sml` and
`compiler/backend/word_allocScript.sml`.  They are the executable half of bead
`flapjack-pxn.8.5.14.1.3.1`; the pinned constants are taken directly from the
original HOL definitions.
-/

namespace Flapjack.Test.CakeAllocatorCore

open Flapjack.RiscV.CakeAlloc

/-- CakeML's fixed spill-cost magic numbers, including the tail factor 5. -/
def spillCostExact : Bool :=
  getSpillCost 0 0 0 0 0 false == 0 &&
    getSpillCost 1 0 0 0 0 false == 1 &&
    getSpillCost 0 1 0 0 0 false == 2 &&
    getSpillCost 0 0 1 0 0 false == 4 &&
    getSpillCost 0 0 0 1 0 false == 2 &&
    getSpillCost 0 0 0 0 1 false == 4 &&
    getSpillCost 1 1 1 1 1 false == 13 &&
    getSpillCost 1 1 1 1 1 true == 65

#guard spillCostExact

/-- Coalescing cost weights frequency, priority and endpoint spill costs. -/
def coalesceCostExact : Bool :=
  getCoalesceCost (fun _ => none) 3 0 1 2 == (30, (1, 2)) &&
    getCoalesceCost (fun _ => some 1) 3 0 1 2 == (36, (1, 2))

#guard coalesceCostExact

/-- `limit_var` is the smallest multiple of four above the variable, plus one. -/
def limitVarExact : Bool :=
  limitVar 0 == 5 &&
    limitVar 3 == 5 &&
    limitVar 4 == 9 &&
    limitVar 7 == 9 &&
    limitVar 8 == 13

#guard limitVarExact

/-- Branch merge (`merge_stack_sets`) keeps the intersection and the
per-branch differences, and unions the forced sets. -/
def mergeStackSetsExact : Bool :=
  mergeStackSets [1, 2] [] [1, 3] [9] [1, 4] [8] == ([1, 3, 4], [9, 8])

#guard mergeStackSetsExact

/-- Temporary names are removed before slot assignment (`remove_temp_stack`). -/
def removeTempStackExact : Bool :=
  removeTempStack [1, 2] [1, 2, 3] [7] == ([3], [7])

#guard removeTempStackExact

/-- More branch-merge and temporary-removal cases. -/
def mergeStackSetsExtendedExact : Bool :=
  mergeStackSets [1, 2] [9] [1, 2, 3] [8] [1, 2, 4] [7] == ([1, 2, 3, 4], [8, 7]) &&
    mergeStackSets [1] [] [1, 2] [3] [1, 2] [4] == ([1, 2], [3, 4])

#guard mergeStackSetsExtendedExact

/-- `remove_temp_stack` deletes every named temporary and leaves the forced
stack set untouched. -/
def removeTempStackExtendedExact : Bool :=
  removeTempStack [1, 3] [1, 2, 3, 4] [7] == ([2, 4], [7]) &&
    removeTempStack [] [1, 2] [7] == ([1, 2], [7]) &&
    removeTempStack [5] [1, 5] [7] == ([1], [7])

#guard removeTempStackExtendedExact

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [
      ("CakeML spill costs use the original magic numbers and tail factor",
        spillCostExact),
      ("CakeML coalescing costs use the original weights", coalesceCostExact),
      ("the SSA temporary numbering base matches limit_var", limitVarExact),
      ("branch merging matches merge_stack_sets", mergeStackSetsExact),
      ("temporary names are removed before slot assignment", removeTempStackExact),
      ("merge_stack_sets and remove_temp_stack agree on further oracle cases",
        mergeStackSetsExtendedExact),
      ("remove_temp_stack deletes only the named temporaries",
        removeTempStackExtendedExact)]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeAllocatorCore

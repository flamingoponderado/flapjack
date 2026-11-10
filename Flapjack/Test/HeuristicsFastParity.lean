module

public import Flapjack.RiscV.SpillCosts

-- Checks below run compiled code from these modules.
public meta import Flapjack.NatDedup
@[expose] public section

/-!
Parity regressions for the hashed heuristic state.

`wordHeuristicSpillCostsFast` replaces the association-list counter map of
`wordHeuristic` with a `Std.TreeMap` plus an update stamp.  The reference
definition makes the *order* of its result observable through the Patricia
tree traversal, so these checks compare the two implementations as lists,
not as sets, across every constructor that touches the counter state,
including both merge paths (`ite` and a handled call).
-/

namespace Flapjack

/-! `natEraseDups` must agree with `List.eraseDups`; the source map merge uses
    Patricia order separately. -/
def heuristicEraseDupsCases : List (List Nat) :=
  [[], [7], [7, 7], [3, 1, 3, 4, 1, 5, 4], [1, 2, 3, 4, 5],
   [5, 4, 3, 2, 1], [9, 9, 9, 9], [0, 1, 0, 2, 0, 3, 1, 2, 3],
   List.range 40 ++ List.range 40, (List.range 40).reverse ++ List.range 20]

#guard heuristicEraseDupsCases.all
  (fun names => names.eraseDups == natEraseDups names)

def heuristicEraseDupsAppendCases : List (List Nat × List Nat) :=
  [([], []), ([7, 1, 7], [2, 1, 4]),
   (List.range 40, List.range 20),
   ((List.range 40).reverse, List.range 20)]

#guard heuristicEraseDupsAppendCases.all
  (fun names => natEraseDupsAppend names.1 names.2 ==
    natEraseDups (names.1 ++ names.2))

/- The fast call-set merge must preserve Cake's Patricia traversal, not merely
   the duplicate-free key set. -/
def heuristicMergeCallsFastCases : List (List Nat × List Nat) :=
  [([], []), ([1, 4, 6], [7, 4, 12]),
   ([7, 1, 4, 12, 6], [3, 1, 9, 3]),
   (List.range 40, (List.range 20).reverse ++ List.range 20),
   ((List.range 40).reverse, List.range 80)]

end Flapjack

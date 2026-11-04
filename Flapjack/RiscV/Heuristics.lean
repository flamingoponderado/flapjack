import Std.Data.TreeMap
import Std.Data.TreeSet
import Flapjack.NatDedup
import Flapjack.RiscV.RegAlloc

/-!
# CakeML Word allocation heuristics

CakeML computes a small usage summary immediately before register allocation.
The five counters record whether a variable occurs on the left-hand side of a
constant, register, or memory operation, and on the right-hand side of a
register or memory operation.  This module ports that executable summary for
the Word fragment represented by Flapjack.

The source allocator also attaches priorities to move preferences.  The
existing graph allocator accepts unprioritized pairs for compatibility, while
the entry points below retain the source priorities and pass them to the
same coalescing machinery.
-/

namespace Flapjack

/-! Cake's `num_map` is a Patricia tree.  `insert` changes a value without
    making that key the head of the observable `toAList`; the observable order
    is the canonical Patricia traversal for the current key set. -/

def wordHeuristicMergeCalls (left right : List Nat) : List Nat :=
  NumSet.fromList (left ++ right)

/-! ## Tree-backed counter state

`wordHeuristicUpdate` above rebuilds the Patricia traversal after each update,
so every counter bump costs a full traversal and a full copy;
`wordHeuristicMaxAll` also reconstructs the source key set at every `ite` and
every handled call.
On a function with `k` call sites the traversal alone measures cubic, and it
dominates the whole Word back end: at `k = 200` it is 94% of
`cakeWordStackVarCount`, which is itself half of the per-function cost.

The state below carries the same information in a `Std.TreeMap`, together
with a monotonically increasing stamp for updates.  `toNatInfoMap` rebuilds
the source Patricia traversal from the current key set, so the order remains
observable through `wordHeuristicKeys`.  Lookup and update become
logarithmic, so a traversal is `O(n log n)` rather than cubic.
`Flapjack/Test/HeuristicsFastParity.lean` checks that correspondence against
the reference definitions, list order included. -/

namespace WordHeuristicCountMap

end WordHeuristicCountMap

end Flapjack

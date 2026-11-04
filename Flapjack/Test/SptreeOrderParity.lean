import Flapjack.NumSet
import Flapjack.RiscV.Allocator

/-! Direct HOL parity for CakeML's `sptree$toAList` enumeration order, which
    the word allocator uses at its three SSA boundaries (`fix_inconsistencies`,
    `ssa_reconcile`, `loop_setup`).  The expected values come from evaluating
    `MAP FST (toAList (fromAList ...))` in HOL:
    `[0,4,6,12] -> [0,4,12,6]`, `[0,4,8,12,16] -> [0,16,8,4,12]`,
    `[1,2,3,4,5] -> [3,1,5,4,2]`, `List.range 13 ->
    [7,3,11,1,9,5,0,8,4,12,2,10,6]`. -/

namespace Flapjack.Test.SptreeOrderParity

open Flapjack

def sptreeOrderGuard : Bool :=
    NumSet.fromList [0, 4, 6, 12] == [0, 4, 12, 6] &&
    NumSet.fromList [0, 4, 8, 12, 16] == [0, 16, 8, 4, 12] &&
    NumSet.fromList [1, 2, 3, 4, 5] == [3, 1, 5, 4, 2] &&
    NumSet.fromList (List.range 13) ==
      [7, 3, 11, 1, 9, 5, 0, 8, 4, 12, 2, 10, 6]

#guard sptreeOrderGuard

/- This is the live set emitted by Cake's `apply_nummap_key` for the
   collapse_branch loop after SSA renaming.  Keeping the concrete case here
   prevents the allocator boundary from silently reverting to source-list
   order, which changes the subsequent clash-tree numbering. -/
def collapseBranchLoopOrderGuard : Bool :=
  NumSet.fromList [57, 61, 65, 69, 73] == [65, 73, 57, 69, 61]

#guard collapseBranchLoopOrderGuard

/-- Empty, singleton, internal, and structurally non-wf Spt constructor
fixtures for the unrestricted `fromAList (toAList tree)` lookup bridge. -/
def sptLookupFromToAListGuard : Bool :=
  sptLookup 0 (sptFromAList (sptToAList (.ln : Spt Nat))) ==
      sptLookup 0 (.ln : Spt Nat) &&
    sptLookup 0 (sptFromAList (sptToAList (.ls 7 : Spt Nat))) ==
      sptLookup 0 (.ls 7 : Spt Nat) &&
    sptLookup 2 (sptFromAList (sptToAList (.bs (.ls 11) 13 (.ls 17) : Spt Nat))) ==
      sptLookup 2 (.bs (.ls 11) 13 (.ls 17) : Spt Nat) &&
    sptLookup 3 (sptFromAList (sptToAList (.bs (.ls 11) 13 (.ls 17) : Spt Nat))) ==
      sptLookup 3 (.bs (.ls 11) 13 (.ls 17) : Spt Nat) &&
    sptLookup 0 (sptFromAList (sptToAList (.bn .ln .ln : Spt Nat))) ==
      sptLookup 0 (.bn .ln .ln : Spt Nat) &&
    sptLookup 0 (sptFromAList (sptToAList (.bs .ln 23 .ln : Spt Nat))) ==
      sptLookup 0 (.bs .ln 23 .ln : Spt Nat)

#guard sptLookupFromToAListGuard
#guard sptWf (.bn .ln .ln : Spt Nat) == false
#guard sptWf (.bs .ln 23 .ln : Spt Nat) == false

end Flapjack.Test.SptreeOrderParity

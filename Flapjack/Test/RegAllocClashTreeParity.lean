import Flapjack.Compiler.Backend.RegAlloc.ClashTree
namespace Flapjack.Test.RegAllocClashTreeParity
open RegAlloc
-- Full-tree replay of the eight original reg_alloc_clash_tree_probe rows.
-- These finite observations do not prove the full allocator theorem.
example : numsetListDelete [1,1] (sptInsert 1 7 (sptInsert 2 8 .ln)) =
    sptInsert 2 (8 : Nat) .ln := by decide +kernel
example : checkCol (fun _ => 0) (sptInsert 1 () (sptInsert 2 () .ln)) = none := by decide +kernel
example : checkPartialCol (fun _ => 0) [1,1] (sptInsert 1 () .ln) .ln =
    some (sptInsert 1 () .ln, .ln) := by decide +kernel
example : checkPartialCol (fun _ => 0) [1,2] .ln .ln = none := by decide +kernel
example : checkClashTree id (.delta [1] []) .ln .ln = some (.ln,.ln) := by decide +kernel
example : checkClashTree id (.seq (.delta [2] [1]) (.delta [] [2])) .ln .ln =
    some (sptInsert 1 () .ln,sptInsert 1 () .ln) := by decide +kernel
example : checkClashTree id (.branch none (.delta [] [1]) (.delta [] [2])) .ln .ln =
    some (sptInsert 2 () (sptInsert 1 () .ln),sptInsert 2 () (sptInsert 1 () .ln)) := by decide +kernel
example : checkClashTree (fun _ => 0)
    (.branch (some (sptInsert 1 () (sptInsert 2 () .ln))) (.delta [] []) (.delta [] []))
    .ln .ln = none := by decide +kernel
end Flapjack.Test.RegAllocClashTreeParity

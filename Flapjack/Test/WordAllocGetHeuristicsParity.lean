import Flapjack.Compiler.Backend.WordAlloc.GetHeuristics

namespace Flapjack.Test.WordAllocGetHeuristicsParity
open Flapjack WordAlloc

/- Same-input whole-result kernel replay of fresh original HOL observations.
The original probe also checks the structural insert representation used here. -/
private def move : WordLangProgHOL (BitVec 64) := .move 3 [(4,2)]
private def costs (n : Nat) : Spt Nat := sptInsert 4 n (sptInsert 2 n .ln)

example : getHeuristics 0 7 (.skip : WordLangProgHOL (BitVec 64)) = ([], none) := by decide +kernel
example : getHeuristics 1 7 (.skip : WordLangProgHOL (BitVec 64)) = ([], some .ln) := by decide +kernel
example : getHeuristics 2 7 move = ([(3,(4,2))], none) := by decide +kernel
example : getHeuristics 3 7 move = ([(42,(2,4))], some (costs 10)) := by decide +kernel
example : getHeuristics 1 7 (.move 3 [(4,2),(2,4)] : WordLangProgHOL (BitVec 64)) =
    ([(84,(2,4))], some (costs 20)) := by decide +kernel
example : getHeuristics 1 7 (.seq move (.call none (some 7) [] none)) =
    ([(42,(2,4))], some (costs 2)) := by decide +kernel
example : getHeuristics 1 7 (.seq move (.call none (some 8) [] none)) =
    ([(42,(2,4))], some (costs 10)) := by decide +kernel
example : getHeuristics 1 7 (.get 5 .nextFree : WordLangProgHOL (BitVec 64)) =
    ([], some (sptInsert 5 20 .ln)) := by decide +kernel
example : getHeuristics 1208925819614629174706176 7
    (.move 3 [(4,2)] : WordLangProgHOL (BitVec 16)) = ([(3,(4,2))], none) := by decide +kernel
example : getHeuristics 1208925819614629174706177 7
    (.move 3 [(4,2)] : WordLangProgHOL (BitVec 16)) =
    ([(42,(2,4))], some (costs 10)) := by decide +kernel

end Flapjack.Test.WordAllocGetHeuristicsParity

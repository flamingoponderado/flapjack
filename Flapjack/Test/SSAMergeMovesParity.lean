import Flapjack.Compiler.Backend.WordAlloc.SSAMergeMoves
namespace Flapjack.Test.SSAMergeMovesParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc
-- Complete results match original merge_moves, including both resulting trees.
example : mergeMoves [] (sptFromAList [(1,7)]) (sptFromAList [(1,9)]) 5 =
  ([],[],5,sptFromAList [(1,7)],sptFromAList [(1,9)]) := by decide +kernel
example : mergeMoves [1] .ln .ln 5 = ([],[],5,.ln,.ln) := by decide +kernel
example : mergeMoves [1] .ln (sptFromAList [(1,9)]) 5 =
  ([],[],5,.ln,sptFromAList [(1,9)]) := by decide +kernel
example : mergeMoves [1] (sptFromAList [(1,7)]) .ln 5 =
  ([],[],5,sptFromAList [(1,7)],.ln) := by decide +kernel
example : mergeMoves [1] (sptFromAList [(1,7)]) (sptFromAList [(1,7)]) 5 =
  ([],[],5,sptFromAList [(1,7)],sptFromAList [(1,7)]) := by decide +kernel
example : mergeMoves [1] (sptFromAList [(1,7)]) (sptFromAList [(1,9)]) 5 =
  ([(5,7)],[(5,9)],9,sptFromAList [(1,5)],sptFromAList [(1,5)]) := by decide +kernel
example : mergeMoves [0,2] (sptFromAList [(0,7),(2,11)]) (sptFromAList [(0,9),(2,13)]) 5 =
  ([(9,7),(5,11)],[(9,9),(5,13)],13,sptFromAList [(0,9),(2,5)],sptFromAList [(0,9),(2,5)]) := by decide +kernel
example : mergeMoves [1,1] (sptFromAList [(1,7)]) (sptFromAList [(1,9)]) 5 =
  ([(5,7)],[(5,9)],9,sptFromAList [(1,5)],sptFromAList [(1,5)]) := by decide +kernel
example : mergeMoves [0,4] (.bn .ln .ln) (sptFromAList [(0,7),(4,9)]) 0 =
  ([],[],0,.bn .ln .ln,sptFromAList [(0,7),(4,9)]) := by decide +kernel
example : mergeMoves [0] (.ls 18446744073709551616) (.ls 3) 18446744073709551616 =
  ([(18446744073709551616,18446744073709551616)],[(18446744073709551616,3)],
   18446744073709551620,.ls 18446744073709551616,.ls 18446744073709551616) := by decide +kernel
end Flapjack.Test.SSAMergeMovesParity

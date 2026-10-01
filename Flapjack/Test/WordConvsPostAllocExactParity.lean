import Flapjack.Pancake.WordConvs

/-! Kernel replay of the four original post-allocation rows from
word_convs_alloc_conventions_probe.out, using exact Spt cutsets. -/
namespace Flapjack.Test.WordConvsPostAllocExactParity
example : postAllocConventionsHOL (width := 8) 2 (.move 0 [(2, 6)]) = true := by cbv
example : postAllocConventionsHOL (width := 8) 2 (.move 0 [(3, 4)]) = false := by cbv
example : postAllocConventionsHOL (width := 8) 2
    (.alloc 2 (sptInsert 2 () .ln, .ln)) = false := by cbv
example : postAllocConventionsHOL (width := 8) 2 (.return 4 [2]) = true := by cbv

def runChecks : IO Bool := do
  IO.println "PASS exact post-allocation convention matches four original HOL rows"
  pure true
end Flapjack.Test.WordConvsPostAllocExactParity

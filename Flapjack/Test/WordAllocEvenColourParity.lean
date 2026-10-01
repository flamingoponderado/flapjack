import Flapjack.Compiler.Backend.WordAlloc.EvenColour

/-! Original physical/virtual, sparse-tree and duplicate-entry observations. -/
namespace Flapjack.Test.WordAllocEvenColourParity
open Flapjack Flapjack.WordAlloc

-- even_colour_empty
example : everyEvenColour (sptFromAList []) = true := by
  decide +kernel

-- even_colour_zero
example : everyEvenColour (sptFromAList [(0, 0)]) = true := by
  decide +kernel

-- even_colour_zero_bad
example : everyEvenColour (sptFromAList [(0, 1)]) = false := by
  decide +kernel

-- even_colour_physical
example : everyEvenColour (sptFromAList [(2, 1), (4, 2), (20, 10)]) = true := by
  decide +kernel

-- even_colour_physical_bad
example : everyEvenColour (sptFromAList [(2, 1), (4, 3), (20, 10)]) = false := by
  decide +kernel

-- even_colour_virtual
example : everyEvenColour (sptFromAList [(1, 99), (3, 0), (5, 400)]) = true := by
  decide +kernel

-- even_colour_mixed
example : everyEvenColour (sptFromAList [(0, 0), (1, 50), (2, 1), (3, 900), (8, 4), (9, 1000)]) = true := by
  decide +kernel

-- even_colour_mixed_bad
example : everyEvenColour (sptFromAList [(0, 0), (1, 50), (2, 1), (3, 900), (8, 5), (9, 1000)]) = false := by
  decide +kernel

-- even_colour_virtual_large
example : everyEvenColour (sptFromAList [(999999999999999999999, 0)]) = true := by
  decide +kernel

-- even_colour_physical_large
example : everyEvenColour (sptFromAList [(18446744073709551616, 9223372036854775808)]) = true := by
  decide +kernel

-- even_colour_physical_large_bad
example : everyEvenColour (sptFromAList [(18446744073709551616, 9223372036854775809)]) = false := by
  decide +kernel

-- even_colour_duplicate_first_good
example : everyEvenColour (sptFromAList [(2, 1), (2, 9)]) = true := by
  decide +kernel

-- even_colour_duplicate_first_bad
example : everyEvenColour (sptFromAList [(2, 9), (2, 1)]) = false := by
  decide +kernel

-- even_colour_duplicate_virtual
example : everyEvenColour (sptFromAList [(3, 100), (3, 0)]) = true := by
  decide +kernel

-- even_colour_no_zero
example : everyEvenColour (sptFromAList [(6, 3), (10, 5), (14, 7)]) = true := by
  decide +kernel

-- even_colour_last_bad
example : everyEvenColour (sptFromAList [(6, 3), (10, 5), (14, 8)]) = false := by
  decide +kernel

-- even_colour_empty_internal
example : everyEvenColour (.bn .ln .ln) = true := by
  decide +kernel

-- even_colour_physical_root_bad
example : everyEvenColour (.bs .ln 7 .ln) = false := by
  decide +kernel

-- even_colour_virtual_left
example : everyEvenColour (.bn .ln (.ls 89)) = true := by
  decide +kernel

-- even_colour_physical_right_bad
example : everyEvenColour (.bn (.ls 89) .ln) = false := by
  decide +kernel

end Flapjack.Test.WordAllocEvenColourParity

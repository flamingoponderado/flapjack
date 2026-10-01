import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvenStartingLocals

namespace Flapjack.Test.WordAllocEvenLocalsParity
open Flapjack
open Flapjack.Compiler.Backend.WordAlloc.Proofs

-- wa_even_empty=T
example : evenStartingLocals (sptFromAList ([] : List (Nat × WordLocW 64))) := by
  exact evenStartingLocals_empty

-- wa_even_zero=T
example : evenStartingLocals (sptFromAList ([(0,.word 0)] : List (Nat × WordLocW 64))) := by
  simp only [sptFromAList, evenStartingLocals_insert, evenStartingLocals_empty]
  decide

-- wa_even_even_holes=T
example : evenStartingLocals (sptFromAList ([(0,.word 1),(8,.loc 7 9),(64,.word 3)] : List (Nat × WordLocW 64))) := by
  simp only [sptFromAList, evenStartingLocals_insert, evenStartingLocals_empty]
  decide

-- wa_even_odd=F
example : ¬ evenStartingLocals (sptFromAList ([(3,.word 0)] : List (Nat × WordLocW 64))) := by
  simp only [sptFromAList, evenStartingLocals_insert, evenStartingLocals_empty]
  decide

-- wa_even_mixed=F
example : ¬ evenStartingLocals (sptFromAList ([(2,.loc 0 0),(5,.word 0)] : List (Nat × WordLocW 64))) := by
  simp only [sptFromAList, evenStartingLocals_insert, evenStartingLocals_empty]
  decide

-- wa_even_overwrite=T
example : evenStartingLocals (sptFromAList ([(8,.word 7),(8,.loc 2 3)] : List (Nat × WordLocW 64))) := by
  simp only [sptFromAList, evenStartingLocals_insert, evenStartingLocals_empty]
  decide

end Flapjack.Test.WordAllocEvenLocalsParity

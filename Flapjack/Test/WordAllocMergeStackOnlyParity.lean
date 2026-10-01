import Flapjack.Compiler.Backend.WordAlloc.StackOnly

namespace Flapjack.Test.WordAllocMergeStackOnlyParity
open Flapjack Flapjack.WordAlloc

-- mso_present_alloc=T
example : mergeStackOnly (0,1) (.ls (),.ln) = (sptInsert 1 () (.ls ()),.ls ()) := by simp [mergeStackOnly, sptLookup, sptInsert, isAllocVar, isPhyVar]

-- mso_present_physical=T
example : mergeStackOnly (0,2) (.ls (),.ln) = (.ls (),.ln) := by simp [mergeStackOnly, sptLookup, isAllocVar, isPhyVar]

-- mso_present_stack=T
example : mergeStackOnly (0,3) (.ls (),.ln) = (.ls (),.ls ()) := by simp [mergeStackOnly, sptLookup, isAllocVar, isPhyVar]

-- mso_absent_stack_alloc=T
example : mergeStackOnly (3,1) (.ln,.ln) = (sptInsert 1 () .ln,.ln) := by simp [mergeStackOnly, sptLookup, sptInsert, isAllocVar, isStackVar]

-- mso_absent_stack_physical=T
example : mergeStackOnly (3,2) (.ln,.ls ()) = (.ln,.ls ()) := by simp [mergeStackOnly, sptLookup, isAllocVar, isStackVar]

-- mso_absent_delete_missing=T
example : mergeStackOnly (2,1) (.ls (),.ln) = (.ls (),.ln) := by simp [mergeStackOnly, sptLookup, sptDelete, isStackVar]

-- mso_absent_delete_root=T
example : mergeStackOnly (2,0) (.ls (),.bn .ln .ln) = (.ln,.bn .ln .ln) := by simp [mergeStackOnly, sptLookup, sptDelete, isStackVar]

-- mso_present_overwrite=T
example : mergeStackOnly (0,5) (.ls (),.ls ()) = (sptInsert 5 () (.ls ()),.ls ()) := by simp [mergeStackOnly, sptLookup, sptInsert, isAllocVar, isPhyVar]

-- mso_raw=T
example : mergeStackOnly (2,0) (.bn .ln .ln,.bn .ln .ln) = (.bn .ln .ln,.bn .ln .ln) := by simp [mergeStackOnly, sptLookup, sptDelete, isStackVar]

end Flapjack.Test.WordAllocMergeStackOnlyParity

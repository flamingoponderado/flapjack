import Flapjack.Compiler.Backend.WordAlloc.ProgramWrites

namespace Flapjack.Test.WordAllocProgramWritesParity
open WordAlloc

/-- Identical inputs and full output trees for the seven direct original
get_writes observations. Regression replays do not establish independent
cross-language equivalence or complete the executed compiler route. -/
example : getWrites (.move 5 [(1, 9), (1, 8), (2, 7)] : WordLangProgHOL (BitVec 8)) =
    sptInsert 1 () (sptInsert 1 () (sptInsert 2 () .ln)) := by decide +kernel

example : getWrites (.storeConsts 1 2 3 4 [] : WordLangProgHOL (BitVec 8)) =
    sptInsert 1 () (sptInsert 2 () (sptInsert 3 () (sptInsert 4 () .ln))) := by
  decide +kernel

example : getWrites (.inst (.mem .load16 1 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) =
    .ln := by decide +kernel

example : getWrites (.shareInst .load16 1 (.var 2) : WordLangProgHOL (BitVec 8)) =
    sptInsert 1 () .ln := by decide +kernel

example : getWrites (.shareInst .store16 1 (.var 2) : WordLangProgHOL (BitVec 8)) =
    .ln := by decide +kernel

example : getWrites (.seq (.locValue 1 2) (.locValue 3 4) : WordLangProgHOL (BitVec 8)) =
    .ln := by decide +kernel

example : getWrites (.install 1 2 3 4 (.ln, .ln) : WordLangProgHOL (BitVec 8)) =
    sptInsert 1 () .ln := by decide +kernel

end Flapjack.Test.WordAllocProgramWritesParity

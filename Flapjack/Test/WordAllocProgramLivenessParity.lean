import Flapjack.Compiler.Backend.WordAlloc.ProgramLiveness

namespace Flapjack.Test.WordAllocProgramLivenessParity
open WordAlloc

/-- Replay direct original get_live_store_consts=T with identical live tree
and constructor fields; this distinguishes the shadowed second source row. -/
example :
    let live := sptFromAList [(1, ()), (2, ()), (9, ())]
    let out := getLive (.storeConsts 1 2 3 4 [] : WordLangProgHOL (BitVec 8)) live []
    sptLookup 1 out = none ∧ sptLookup 2 out = none ∧
      sptLookup 3 out = some () ∧ sptLookup 4 out = some () ∧
      sptLookup 9 out = some () := by decide +kernel

/-- Direct original get_live_break_outside=T. -/
example : getLive (.break 2 : WordLangProgHOL (BitVec 8)) .ln [] = .ln := by
  decide +kernel

/-- Direct original get_live_return=T; repeated return values remain set entries. -/
example :
    let out := getLive (.return 1 [2, 2] : WordLangProgHOL (BitVec 8)) .ln []
    sptLookup 1 out = some () ∧ sptLookup 2 out = some () ∧
      sptLookup 3 out = none := by decide +kernel

end Flapjack.Test.WordAllocProgramLivenessParity

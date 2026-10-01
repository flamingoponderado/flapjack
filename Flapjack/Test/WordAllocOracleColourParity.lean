import Flapjack.Compiler.Backend.WordAlloc.OracleColour
namespace Flapjack.Test.WordAllocOracleColourParity
open Flapjack Flapjack.WordAlloc Flapjack.RegAlloc
/-! Same-input kernel replay of all original oracle rejection stages plus
actual renamed output and stack-bound equality. Finite regression evidence. -/
-- oc_none=T
example : oracleColourOk 0 (none) (.delta [] [])
    (.skip : WordLangProgHOL (BitVec 64)) [] = (none) := by
  cbv

-- oc_empty=T
example : oracleColourOk 0 (some .ln) (.delta [] [])
    (.skip : WordLangProgHOL (BitVec 64)) [] = (some .skip) := by
  cbv

-- oc_physical_bad=T
example : oracleColourOk 0 (some (sptInsert 2 99 .ln)) (.delta [] [])
    (.skip : WordLangProgHOL (BitVec 64)) [] = (none) := by
  cbv

-- oc_checker_collision=T
example : oracleColourOk 0 (some .ln) (.set (sptInsert 3 () (sptInsert 5 () .ln)))
    (.skip : WordLangProgHOL (BitVec 64)) [] = (none) := by
  cbv

-- oc_forced_collision=T
example : oracleColourOk 0 (some .ln) (.delta [] [])
    (.skip : WordLangProgHOL (BitVec 64)) [(3,5)] = (none) := by
  cbv

-- oc_forced_distinct=T
example : oracleColourOk 0 (some .ln) (.delta [] [])
    (.skip : WordLangProgHOL (BitVec 64)) [(2,4)] = (some .skip) := by
  cbv

-- oc_rename=T
example : oracleColourOk 0 (some (sptInsert 3 4 (sptInsert 5 7 .ln))) (.delta [] [])
    (.assign 3 (.var 5) : WordLangProgHOL (BitVec 64)) [] = (some (.assign 8 (.var 14))) := by
  cbv

-- oc_stack_equal=T
example : oracleColourOk 4 (some (sptInsert 3 4 .ln)) (.delta [] [])
    (.alloc 3 (sptInsert 3 () .ln,.ln) : WordLangProgHOL (BitVec 64)) [] = (some (.alloc 8 (sptInsert 8 () .ln,.ln))) := by
  cbv

-- oc_stack_below=T
example : oracleColourOk 5 (some (sptInsert 3 4 .ln)) (.delta [] [])
    (.alloc 3 (sptInsert 3 () .ln,.ln) : WordLangProgHOL (BitVec 64)) [] = (none) := by
  cbv

-- oc_raw_map=T
example : oracleColourOk 0 (some (.bn .ln .ln)) (.delta [] [])
    (.skip : WordLangProgHOL (BitVec 64)) [] = (some .skip) := by
  cbv

end Flapjack.Test.WordAllocOracleColourParity

import Flapjack.Compiler.Backend.WordAlloc.TotalColour

namespace Flapjack.Test.WordAllocTotalColourParity
open Flapjack Flapjack.WordAlloc

/-! Direct original total_colour observations, including missing and mapped
physical/virtual registers, zero colours, and arbitrary-precision keys. -/
-- tc_absent_zero=0
example : totalColour (.ln) 0 = 0 := by simp [totalColour, sptLookup, isPhyVar]
-- tc_absent_physical=2
example : totalColour (.ln) 2 = 2 := by simp [totalColour, sptLookup, isPhyVar]
-- tc_absent_virtual=0
example : totalColour (.ln) 3 = 0 := by simp [totalColour, sptLookup, isPhyVar]
-- tc_absent_large_physical=4294967296
example : totalColour (.ln) 4294967296 = 4294967296 := by simp [totalColour, sptLookup, isPhyVar]
-- tc_absent_large_virtual=0
example : totalColour (.ln) 4294967297 = 0 := by simp [totalColour, sptLookup, isPhyVar]
-- tc_mapped_physical=14
example : totalColour (sptInsert 2 7 .ln) 2 = 14 := by simp [totalColour, sptLookup_sptInsert_same]
-- tc_mapped_virtual=16
example : totalColour (sptInsert 3 8 .ln) 3 = 16 := by simp [totalColour, sptLookup_sptInsert_same]
-- tc_mapped_zero=0
example : totalColour (sptInsert 3 0 .ln) 3 = 0 := by simp [totalColour, sptLookup_sptInsert_same]

end Flapjack.Test.WordAllocTotalColourParity

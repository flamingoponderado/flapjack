import Flapjack.Compiler.Backend.WordAlloc.TotalColour
namespace Flapjack.Test.SpDefaultParity
open Flapjack Flapjack.WordAlloc

/-! Kernel replay of `scripts/hol-probes/word_alloc_sp_default_probe.out`:
original HOL `sp_default` and `total_colour`/`total_colour_alt` rows. -/

-- spd_missing_phy=3
example : spDefault .ln 6 = 3 := by rfl
-- spd_missing_virtual=0
example : spDefault .ln 7 = 0 := by rfl
-- spd_present_phy=9
example : spDefault (sptInsert 6 9 .ln) 6 = 9 := by simp [spDefault, sptInsert, sptLookup]
-- spd_present_virtual=4
example : spDefault (sptInsert 7 4 .ln) 7 = 4 := by simp [spDefault, sptInsert, sptLookup]
-- spd_present_zero=0
example : spDefault (sptInsert 6 0 .ln) 6 = 0 := by simp [spDefault, sptInsert, sptLookup]
-- spd_raw_bs=5
example : spDefault (.bs .ln 5 .ln) 0 = 5 := by rfl
-- spd_raw_bn_hit=8
example : spDefault (.bn .ln (.ls 8)) 1 = 8 := by rfl
-- spd_raw_bn_miss=1
example : spDefault (.bn .ln (.ls 8)) 2 = 1 := by rfl
-- spd_large_phy=18446744073709551616
example : spDefault .ln 36893488147419103232 = 18446744073709551616 := by rfl
-- spd_large_virtual=0
example : spDefault .ln 36893488147419103233 = 0 := by rfl

/-- `total_colour_alt` applied at a point: both sides of each `tc_*` row. -/
theorem alt (col : Spt Nat) (x : Nat) : totalColour col x = 2 * spDefault col x :=
  congrFun (totalColourAlt col) x

-- tc_missing_phy=(6,6)
example : (totalColour .ln 6, ((fun x => 2 * x) ∘ spDefault .ln) 6) = (6, 6) := by rfl
example : totalColour .ln 6 = 6 := (alt .ln 6).trans rfl
-- tc_missing_virtual=(0,0)
example : (totalColour .ln 7, ((fun x => 2 * x) ∘ spDefault .ln) 7) = (0, 0) := by rfl
example : totalColour .ln 7 = 0 := (alt .ln 7).trans rfl
-- tc_present=(18,18)
example : (totalColour (sptInsert 6 9 .ln) 6, ((fun x => 2 * x) ∘ spDefault (sptInsert 6 9 .ln)) 6)
    = (18, 18) := by simp [totalColour, spDefault, sptInsert, sptLookup]
example : totalColour (sptInsert 6 9 .ln) 6 = 18 :=
  (alt _ 6).trans (by simp [spDefault, sptInsert, sptLookup])
-- tc_raw=(16,16)
example : (totalColour (.bn .ln (.ls 8)) 1, ((fun x => 2 * x) ∘ spDefault (.bn .ln (.ls 8))) 1)
    = (16, 16) := by rfl
example : totalColour (.bn .ln (.ls 8)) 1 = 16 := (alt _ 1).trans rfl
-- tc_large=(36893488147419103232,36893488147419103232)
example : (totalColour .ln 36893488147419103232,
    ((fun x => 2 * x) ∘ spDefault .ln) 36893488147419103232)
    = (36893488147419103232, 36893488147419103232) := by rfl
example : totalColour .ln 36893488147419103232 = 36893488147419103232 := (alt _ _).trans rfl

end Flapjack.Test.SpDefaultParity

import Flapjack.Misc.ListEl

namespace Flapjack.Test.HolListElParity
open Flapjack
/-! Kernel replay of fresh original HOL `HD`/`EL` values
(`scripts/hol-probes/hol_list_el_probe.out`) at the pinned HOL revision.
`holHd`/`holEl` are noncomputable (their unspecified `[]` case is opaque), so
in-range values are computed through `holEl_eq_getElem`. Finite observations
do not establish cross-prover equivalence. -/

-- hd_cons=3
example : holHd [3, 4] = 3 := rfl
-- hd_bool=F
example : holHd [false, true] = false := rfl
-- el_zero=5
example : holEl 0 [5, 6, 7] = 5 := by rw [holEl_eq_getElem 0 _ (by decide)]; rfl
-- el_last=7
example : holEl 2 [5, 6, 7] = 7 := by rw [holEl_eq_getElem 2 _ (by decide)]; rfl
-- el_nested=[2; 3]
example : holEl 1 [[1], [2, 3]] = [2, 3] := by rw [holEl_eq_getElem 1 _ (by decide)]; rfl
-- el_large=18446744073709551617
example : holEl 1 [18446744073709551616, 18446744073709551617] = 18446744073709551617 := by
  rw [holEl_eq_getElem 1 _ (by decide)]; rfl

end Flapjack.Test.HolListElParity

import Flapjack.Compiler.Backend.RegAlloc.ConsideredVar

namespace Flapjack.Test.RegAllocConsideredVarParity
open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase
/-! Same-input kernel replay of fresh original EVAL results
(`scripts/hol-probes/reg_alloc_considered_var_probe.out`) for `is_Fixed`,
`is_Atemp`, `is_Fixed_k` (below/equal/above `k`), `considered_var` and
`deg_or_inf`, including out-of-array failures and state preservation. Finite
observations do not establish general cross-prover equivalence. -/

def s : State :=
  { adj_ls := [[], [], [], []], node_tag := [.Fixed 1, .Atemp, .Stemp, .Fixed 7],
    degrees := [4, 5, 6, 9], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [],
    avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 2, 3],
    move_related := [false, false, false, false], stack := [] }

-- if_fixed=M_success T
example : (isFixed 0 s).1 = .success true := by decide +kernel
-- if_atemp=M_success F
example : (isFixed 1 s).1 = .success false := by decide +kernel
-- if_oob=M_failure Subscript
example : (isFixed 4 s).1 = .failure .Subscript := by decide +kernel
-- ia_atemp=M_success T
example : (isAtemp 1 s).1 = .success true := by decide +kernel
-- ia_stemp=M_success F
example : (isAtemp 2 s).1 = .success false := by decide +kernel
-- ia_fixed=M_success F
example : (isAtemp 0 s).1 = .success false := by decide +kernel
-- ifk_below=M_success T
example : (isFixedK 3 0 s).1 = .success true := by decide +kernel
-- ifk_above=M_success F
example : (isFixedK 3 3 s).1 = .success false := by decide +kernel
-- ifk_equal=M_success F
example : (isFixedK 7 3 s).1 = .success false := by decide +kernel
-- ifk_stemp=M_success F
example : (isFixedK 3 2 s).1 = .success false := by decide +kernel
-- cv_atemp=M_success T
example : (consideredVar 3 1 s).1 = .success true := by decide +kernel
-- cv_fixed_low=M_success T
example : (consideredVar 3 0 s).1 = .success true := by decide +kernel
-- cv_fixed_high=M_success F
example : (consideredVar 3 3 s).1 = .success false := by decide +kernel
-- cv_stemp=M_success F
example : (consideredVar 3 2 s).1 = .success false := by decide +kernel
-- cv_oob=M_failure Subscript
example : (consideredVar 3 9 s).1 = .failure .Subscript := by decide +kernel
-- doi_fixed_low=M_success 3
example : (degOrInf 3 0 s).1 = .success 3 := by decide +kernel
-- doi_fixed_high=M_success 9
example : (degOrInf 3 3 s).1 = .success 9 := by decide +kernel
-- doi_atemp=M_success 5
example : (degOrInf 3 1 s).1 = .success 5 := by decide +kernel
-- doi_oob=M_failure Subscript
example : (degOrInf 3 4 s).1 = .failure .Subscript := by decide +kernel
-- doi_state=T
example : (degOrInf 3 1 s).2 = s := by decide +kernel

end Flapjack.Test.RegAllocConsideredVarParity

import Flapjack.Compiler.Backend.RegAlloc.SplitDegree

namespace Flapjack.Test.RegAllocSplitDegreeParity
open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase
/-! Same-input kernel replay of fresh original EVAL results
(`scripts/hol-probes/reg_alloc_split_degree_probe.out`) for `is_not_coalesced`
and `split_degree`: self/other coalesce targets, low/high/equal degree,
`v ≥ d` short-circuit (including an out-of-array `v`), an out-of-array
`v < d` failure, and state preservation. Finite observations do not establish
general cross-prover equivalence. -/

def s : State :=
  { adj_ls := [[], [], []], node_tag := [.Atemp, .Atemp, .Atemp], degrees := [1, 5, 2],
    dim := 3, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [],
    unavail_moves_wl := [], coalesced := [0, 0, 2], move_related := [false, true, false],
    stack := [] }

-- inc_self=M_success T
example : (isNotCoalesced 0 s).1 = .success true := by decide +kernel
-- inc_other=M_success F
example : (isNotCoalesced 1 s).1 = .success false := by decide +kernel
-- inc_last=M_success T
example : (isNotCoalesced 2 s).1 = .success true := by decide +kernel
-- inc_oob=M_failure Subscript
example : (isNotCoalesced 3 s).1 = .failure .Subscript := by decide +kernel
-- sd_low_self=M_success T
example : (splitDegree 3 4 0 s).1 = .success true := by decide +kernel
-- sd_high=M_success F
example : (splitDegree 3 4 1 s).1 = .success false := by decide +kernel
-- sd_low_coalesced_k6=M_success F
example : (splitDegree 3 6 1 s).1 = .success false := by decide +kernel
-- sd_eq_k=M_success F
example : (splitDegree 3 2 2 s).1 = .success false := by decide +kernel
-- sd_out_of_d=M_success T
example : (splitDegree 1 4 2 s).1 = .success true := by decide +kernel
-- sd_oob_bound_true=M_failure Subscript
example : (splitDegree 10 4 3 s).1 = .failure .Subscript := by decide +kernel
-- sd_beyond_all=M_success T
example : (splitDegree 3 0 7 s).1 = .success true := by decide +kernel
-- sd_state=T
example : (splitDegree 3 4 0 s).2 = s := by decide +kernel

end Flapjack.Test.RegAllocSplitDegreeParity

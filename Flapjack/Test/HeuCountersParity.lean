import Flapjack.Compiler.Backend.WordAlloc.HeuCounters

namespace Flapjack.Test.HeuCountersParity
open Flapjack Flapjack.WordAlloc

-- Original hc_lhs_const_absent=T
example : add1LhsConst 2 .ln = sptInsert 2 (1, 0, 0, 0, 0) .ln := by
  simp [add1LhsConst, sptLookup, sptInsert]

-- Original hc_lhs_const_present=T
example : add1LhsConst 2 (sptInsert 2 (2, 3, 5, 7, 11) .ln) = sptInsert 2 (3, 3, 5, 7, 11) .ln := by
  simp [add1LhsConst, sptLookup, sptInsert]

-- Original hc_lhs_const_repeat=T
example : add1LhsConst 2 (add1LhsConst 2 .ln) = sptInsert 2 (2, 0, 0, 0, 0) .ln := by
  simp [add1LhsConst, sptLookup, sptInsert]

-- Original hc_lhs_const_other=T
example : sptLookup 7 (add1LhsConst 2 (sptInsert 7 (2, 3, 5, 7, 11) .ln)) = some (2, 3, 5, 7, 11) := by
  simp [add1LhsConst, sptLookup, sptInsert]

-- Original hc_lhs_reg_absent=T
example : add1LhsReg 2 .ln = sptInsert 2 (0, 1, 0, 0, 0) .ln := by
  simp [add1LhsReg, sptLookup, sptInsert]

-- Original hc_lhs_reg_present=T
example : add1LhsReg 2 (sptInsert 2 (2, 3, 5, 7, 11) .ln) = sptInsert 2 (2, 4, 5, 7, 11) .ln := by
  simp [add1LhsReg, sptLookup, sptInsert]

-- Original hc_lhs_reg_repeat=T
example : add1LhsReg 2 (add1LhsReg 2 .ln) = sptInsert 2 (0, 2, 0, 0, 0) .ln := by
  simp [add1LhsReg, sptLookup, sptInsert]

-- Original hc_lhs_reg_other=T
example : sptLookup 7 (add1LhsReg 2 (sptInsert 7 (2, 3, 5, 7, 11) .ln)) = some (2, 3, 5, 7, 11) := by
  simp [add1LhsReg, sptLookup, sptInsert]

-- Original hc_lhs_mem_absent=T
example : add1LhsMem 2 .ln = sptInsert 2 (0, 0, 1, 0, 0) .ln := by
  simp [add1LhsMem, sptLookup, sptInsert]

-- Original hc_lhs_mem_present=T
example : add1LhsMem 2 (sptInsert 2 (2, 3, 5, 7, 11) .ln) = sptInsert 2 (2, 3, 6, 7, 11) .ln := by
  simp [add1LhsMem, sptLookup, sptInsert]

-- Original hc_lhs_mem_repeat=T
example : add1LhsMem 2 (add1LhsMem 2 .ln) = sptInsert 2 (0, 0, 2, 0, 0) .ln := by
  simp [add1LhsMem, sptLookup, sptInsert]

-- Original hc_lhs_mem_other=T
example : sptLookup 7 (add1LhsMem 2 (sptInsert 7 (2, 3, 5, 7, 11) .ln)) = some (2, 3, 5, 7, 11) := by
  simp [add1LhsMem, sptLookup, sptInsert]

-- Original hc_rhs_reg_absent=T
example : add1RhsReg 2 .ln = sptInsert 2 (0, 0, 0, 1, 0) .ln := by
  simp [add1RhsReg, sptLookup, sptInsert]

-- Original hc_rhs_reg_present=T
example : add1RhsReg 2 (sptInsert 2 (2, 3, 5, 7, 11) .ln) = sptInsert 2 (2, 3, 5, 8, 11) .ln := by
  simp [add1RhsReg, sptLookup, sptInsert]

-- Original hc_rhs_reg_repeat=T
example : add1RhsReg 2 (add1RhsReg 2 .ln) = sptInsert 2 (0, 0, 0, 2, 0) .ln := by
  simp [add1RhsReg, sptLookup, sptInsert]

-- Original hc_rhs_reg_other=T
example : sptLookup 7 (add1RhsReg 2 (sptInsert 7 (2, 3, 5, 7, 11) .ln)) = some (2, 3, 5, 7, 11) := by
  simp [add1RhsReg, sptLookup, sptInsert]

-- Original hc_rhs_mem_absent=T
example : add1RhsMem 2 .ln = sptInsert 2 (0, 0, 0, 0, 1) .ln := by
  simp [add1RhsMem, sptLookup, sptInsert]

-- Original hc_rhs_mem_present=T
example : add1RhsMem 2 (sptInsert 2 (2, 3, 5, 7, 11) .ln) = sptInsert 2 (2, 3, 5, 7, 12) .ln := by
  simp [add1RhsMem, sptLookup, sptInsert]

-- Original hc_rhs_mem_repeat=T
example : add1RhsMem 2 (add1RhsMem 2 .ln) = sptInsert 2 (0, 0, 0, 0, 2) .ln := by
  simp [add1RhsMem, sptLookup, sptInsert]

-- Original hc_rhs_mem_other=T
example : sptLookup 7 (add1RhsMem 2 (sptInsert 7 (2, 3, 5, 7, 11) .ln)) = some (2, 3, 5, 7, 11) := by
  simp [add1RhsMem, sptLookup, sptInsert]

end Flapjack.Test.HeuCountersParity

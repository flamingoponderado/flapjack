import Flapjack.Compiler.Backend.WordAlloc.HeuInst

namespace Flapjack.Test.HeuInstParity
open Flapjack Flapjack.WordAlloc
/-! Explicit counter-tree kernel replay of fresh original HOL observations.
All counted clauses, aliasing, widths1/32/64/128, ignored addresses, raw-tree
catchalls and unbounded Nat counters are covered. Finite regression evidence
does not establish cross-prover equivalence or executed allocator routing. -/
-- hi_skip=T
example : getHeuInst (.skip : WordLangInst (BitVec 64)) (sptInsert 7 (2,3,5,7,11) .ln) =
    (sptInsert 7 (2,3,5,7,11) .ln) := by decide +kernel
-- hi_const=T
example : getHeuInst (.const 1 7 : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (1,0,0,0,0) .ln) := by decide +kernel
-- hi_binreg=T
example : getHeuInst (.arith (.binop .add 1 2 (.reg 3)) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,1,0,0,0) (sptInsert 2 (0,0,0,1,0) (sptInsert 3 (0,0,0,1,0) .ln))) := by decide +kernel
-- hi_shiftreg=T
example : getHeuInst (.arith (.shift .lsl 1 2 (.reg 3)) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,1,0,0,0) (sptInsert 2 (0,0,0,1,0) (sptInsert 3 (0,0,0,1,0) .ln))) := by decide +kernel
-- hi_div=T
example : getHeuInst (.arith (.div 1 2 3) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,1,0,0,0) (sptInsert 2 (0,0,0,1,0) (sptInsert 3 (0,0,0,1,0) .ln))) := by decide +kernel
-- hi_binimm=T
example : getHeuInst (.arith (.binop .add 1 2 (.imm 7)) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,1,0,0,0) (sptInsert 2 (0,0,0,1,0) .ln)) := by decide +kernel
-- hi_shiftimm=T
example : getHeuInst (.arith (.shift .lsl 1 2 (.imm 7)) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,1,0,0,0) (sptInsert 2 (0,0,0,1,0) .ln)) := by decide +kernel
-- hi_carry=T
example : getHeuInst (.arith (.addCarry 1 2 3 4) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,1,0,0,0) (sptInsert 2 (0,0,0,1,0) (sptInsert 3 (0,0,0,1,0) (sptInsert 4 (0,1,0,1,0) .ln)))) := by decide +kernel
-- hi_addoverflow=T
example : getHeuInst (.arith (.addOverflow 1 2 3 4) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,1,0,0,0) (sptInsert 2 (0,0,0,1,0) (sptInsert 3 (0,0,0,1,0) (sptInsert 4 (0,1,0,0,0) .ln)))) := by decide +kernel
-- hi_suboverflow=T
example : getHeuInst (.arith (.subOverflow 1 2 3 4) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,1,0,0,0) (sptInsert 2 (0,0,0,1,0) (sptInsert 3 (0,0,0,1,0) (sptInsert 4 (0,1,0,0,0) .ln)))) := by decide +kernel
-- hi_longmul=T
example : getHeuInst (.arith (.longMul 1 2 3 4) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,1,0,0,0) (sptInsert 2 (0,1,0,0,0) (sptInsert 3 (0,0,0,1,0) (sptInsert 4 (0,0,0,1,0) .ln)))) := by decide +kernel
-- hi_longdiv=T
example : getHeuInst (.arith (.longDiv 1 2 3 4 5) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,1,0,0,0) (sptInsert 2 (0,1,0,0,0) (sptInsert 3 (0,0,0,1,0) (sptInsert 4 (0,0,0,1,0) (sptInsert 5 (0,0,0,1,0) .ln))))) := by decide +kernel
-- hi_load=T
example : getHeuInst (.mem .load 1 (.addr 99 7) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,0,1,0,0) .ln) := by decide +kernel
-- hi_load32=T
example : getHeuInst (.mem .load32 1 (.addr 99 7) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,0,1,0,0) .ln) := by decide +kernel
-- hi_load8=T
example : getHeuInst (.mem .load8 1 (.addr 99 7) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,0,1,0,0) .ln) := by decide +kernel
-- hi_store=T
example : getHeuInst (.mem .store 1 (.addr 99 7) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,0,0,0,1) .ln) := by decide +kernel
-- hi_store32=T
example : getHeuInst (.mem .store32 1 (.addr 99 7) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,0,0,0,1) .ln) := by decide +kernel
-- hi_store8=T
example : getHeuInst (.mem .store8 1 (.addr 99 7) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,0,0,0,1) .ln) := by decide +kernel
-- hi_fpless=T
example : getHeuInst (.arith (.binop .add 1 1 (.reg 1)) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,1,0,2,0) .ln) := by decide +kernel
-- hi_carry_alias=T
example : getHeuInst (.arith (.addCarry 1 1 1 1) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,2,0,3,0) .ln) := by decide +kernel
-- hi_longdiv_alias=T
example : getHeuInst (.arith (.longDiv 1 1 1 1 1) : WordLangInst (BitVec 64)) .ln =
    (sptInsert 1 (0,2,0,3,0) .ln) := by decide +kernel
-- hi_to_alias=T
example : getHeuInst (.arith (.addCarry 1 1 1 1) : WordLangInst (BitVec 64)) (sptInsert 1 (7,11,13,17,19) (sptInsert 9 (23,29,31,37,41) .ln)) =
    (sptInsert 1 (7,13,13,20,19) (sptInsert 9 (23,29,31,37,41) .ln)) := by decide +kernel
-- hi_large=T
example : getHeuInst (.const 1 1 : WordLangInst (BitVec 1)) (sptInsert 1 (18446744073709551616,3,5,7,11) .ln) =
    (sptInsert 1 (18446744073709551617,3,5,7,11) .ln) := by decide +kernel
-- hi_const_raw=T
example : getHeuInst (.const 0 7 : WordLangInst (BitVec 64)) (.bn .ln .ln) =
    (.bs .ln (1,0,0,0,0) .ln) := by decide +kernel
-- hi_load16_raw=T
example : getHeuInst (.mem .load16 1 (.addr 99 7) : WordLangInst (BitVec 64)) (.bn .ln .ln) =
    (.bn .ln .ln) := by decide +kernel
-- hi_store16_raw=T
example : getHeuInst (.mem .store16 1 (.addr 99 7) : WordLangInst (BitVec 64)) (.bn .ln .ln) =
    (.bn .ln .ln) := by decide +kernel
-- hi_fpabs_raw=T
end Flapjack.Test.HeuInstParity

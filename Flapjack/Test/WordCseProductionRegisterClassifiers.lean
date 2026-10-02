import Flapjack.RiscV.WordCse

/-! Original register-classifier observations at executed CSE callers.
Source-only overflow and FP cases remain on the full carrier frontier. -/
namespace Flapjack.Test.WordCseProductionRegisterClassifiers
open Flapjack Flapjack.RiscV

-- Original rk_a0_firstRegOfArith_8.
example : wordCseFirstRegOfArith (.binOp .add 99 3 (.reg 5) : WordArith (BitVec 8)) = 99 := by rfl

-- Original rk_a0_arithWrites_8.
example : wordCseArithWrites (.binOp .add 99 3 (.reg 5) : WordArith (BitVec 8)) = [99] := by rfl

-- Original rk_a0_arithReads_8.
example : wordCseArithReads (.binOp .add 99 3 (.reg 5) : WordArith (BitVec 8)) = [3, 5] := by rfl

-- Original rk_a0_can_mem_arith_8.
example : wordCseCanMemArith (.binOp .add 99 3 (.reg 5) : WordArith (BitVec 8)) = true := by rfl

-- Original rk_a1_firstRegOfArith_8.
example : wordCseFirstRegOfArith (.binOp .sub 99 4 (.imm 255) : WordArith (BitVec 8)) = 99 := by rfl

-- Original rk_a1_arithWrites_8.
example : wordCseArithWrites (.binOp .sub 99 4 (.imm 255) : WordArith (BitVec 8)) = [99] := by rfl

-- Original rk_a1_arithReads_8.
example : wordCseArithReads (.binOp .sub 99 4 (.imm 255) : WordArith (BitVec 8)) = [4] := by rfl

-- Original rk_a1_can_mem_arith_8.
example : wordCseCanMemArith (.binOp .sub 99 4 (.imm 255) : WordArith (BitVec 8)) = false := by rfl

-- Original rk_a2_firstRegOfArith_8.
example : wordCseFirstRegOfArith (.shift .ror 99 3 (.imm 255) : WordArith (BitVec 8)) = 99 := by rfl

-- Original rk_a2_arithWrites_8.
example : wordCseArithWrites (.shift .ror 99 3 (.imm 255) : WordArith (BitVec 8)) = [99] := by rfl

-- Original rk_a2_arithReads_8.
example : wordCseArithReads (.shift .ror 99 3 (.imm 255) : WordArith (BitVec 8)) = [3] := by rfl

-- Original rk_a2_can_mem_arith_8.
example : wordCseCanMemArith (.shift .ror 99 3 (.imm 255) : WordArith (BitVec 8)) = true := by rfl

-- Original rk_a3_firstRegOfArith_8.
example : wordCseFirstRegOfArith (.shift .lsl 99 3 (.reg 5) : WordArith (BitVec 8)) = 99 := by rfl

-- Original rk_a3_arithWrites_8.
example : wordCseArithWrites (.shift .lsl 99 3 (.reg 5) : WordArith (BitVec 8)) = [99] := by rfl

-- Original rk_a3_arithReads_8.
example : wordCseArithReads (.shift .lsl 99 3 (.reg 5) : WordArith (BitVec 8)) = [3, 5] := by rfl

-- Original rk_a3_can_mem_arith_8.
example : wordCseCanMemArith (.shift .lsl 99 3 (.reg 5) : WordArith (BitVec 8)) = false := by rfl

-- Original rk_a4_firstRegOfArith_8.
example : wordCseFirstRegOfArith (.div 99 3 5 : WordArith (BitVec 8)) = 99 := by rfl

-- Original rk_a4_arithWrites_8.
example : wordCseArithWrites (.div 99 3 5 : WordArith (BitVec 8)) = [99] := by rfl

-- Original rk_a4_arithReads_8.
example : wordCseArithReads (.div 99 3 5 : WordArith (BitVec 8)) = [3, 5] := by rfl

-- Original rk_a4_can_mem_arith_8.
example : wordCseCanMemArith (.div 99 3 5 : WordArith (BitVec 8)) = true := by rfl

-- Original rk_a5_firstRegOfArith_8.
example : wordCseFirstRegOfArith (.longMul 99 98 3 5 : WordArith (BitVec 8)) = 99 := by rfl

-- Original rk_a5_arithWrites_8.
example : wordCseArithWrites (.longMul 99 98 3 5 : WordArith (BitVec 8)) = [99, 98] := by rfl

-- Original rk_a5_arithReads_8.
example : wordCseArithReads (.longMul 99 98 3 5 : WordArith (BitVec 8)) = [3, 5] := by rfl

-- Original rk_a5_can_mem_arith_8.
example : wordCseCanMemArith (.longMul 99 98 3 5 : WordArith (BitVec 8)) = false := by rfl

-- Original rk_a6_firstRegOfArith_8.
example : wordCseFirstRegOfArith (.longDiv 99 98 3 5 7 : WordArith (BitVec 8)) = 99 := by rfl

-- Original rk_a6_arithWrites_8.
example : wordCseArithWrites (.longDiv 99 98 3 5 7 : WordArith (BitVec 8)) = [99, 98] := by rfl

-- Original rk_a6_arithReads_8.
example : wordCseArithReads (.longDiv 99 98 3 5 7 : WordArith (BitVec 8)) = [3, 5, 7] := by rfl

-- Original rk_a6_can_mem_arith_8.
example : wordCseCanMemArith (.longDiv 99 98 3 5 7 : WordArith (BitVec 8)) = false := by rfl

-- Original rk_a7_firstRegOfArith_8.
example : wordCseFirstRegOfArith (.cakeAddCarry 99 3 5 98 : WordArith (BitVec 8)) = 99 := by rfl

-- Original rk_a7_arithWrites_8.
example : wordCseArithWrites (.cakeAddCarry 99 3 5 98 : WordArith (BitVec 8)) = [99, 98] := by rfl

-- Original rk_a7_arithReads_8.
example : wordCseArithReads (.cakeAddCarry 99 3 5 98 : WordArith (BitVec 8)) = [3, 5, 98] := by rfl

-- Original rk_a7_can_mem_arith_8.
example : wordCseCanMemArith (.cakeAddCarry 99 3 5 98 : WordArith (BitVec 8)) = false := by rfl

-- Original rk_a0_firstRegOfArith_80.
example : wordCseFirstRegOfArith (.binOp .add 99 3 (.reg 5) : WordArith (BitVec 80)) = 99 := by rfl

-- Original rk_a0_arithWrites_80.
example : wordCseArithWrites (.binOp .add 99 3 (.reg 5) : WordArith (BitVec 80)) = [99] := by rfl

-- Original rk_a0_arithReads_80.
example : wordCseArithReads (.binOp .add 99 3 (.reg 5) : WordArith (BitVec 80)) = [3, 5] := by rfl

-- Original rk_a0_can_mem_arith_80.
example : wordCseCanMemArith (.binOp .add 99 3 (.reg 5) : WordArith (BitVec 80)) = true := by rfl

-- Original rk_a1_firstRegOfArith_80.
example : wordCseFirstRegOfArith (.binOp .sub 99 4 (.imm 255) : WordArith (BitVec 80)) = 99 := by rfl

-- Original rk_a1_arithWrites_80.
example : wordCseArithWrites (.binOp .sub 99 4 (.imm 255) : WordArith (BitVec 80)) = [99] := by rfl

-- Original rk_a1_arithReads_80.
example : wordCseArithReads (.binOp .sub 99 4 (.imm 255) : WordArith (BitVec 80)) = [4] := by rfl

-- Original rk_a1_can_mem_arith_80.
example : wordCseCanMemArith (.binOp .sub 99 4 (.imm 255) : WordArith (BitVec 80)) = false := by rfl

-- Original rk_a2_firstRegOfArith_80.
example : wordCseFirstRegOfArith (.shift .ror 99 3 (.imm 255) : WordArith (BitVec 80)) = 99 := by rfl

-- Original rk_a2_arithWrites_80.
example : wordCseArithWrites (.shift .ror 99 3 (.imm 255) : WordArith (BitVec 80)) = [99] := by rfl

-- Original rk_a2_arithReads_80.
example : wordCseArithReads (.shift .ror 99 3 (.imm 255) : WordArith (BitVec 80)) = [3] := by rfl

-- Original rk_a2_can_mem_arith_80.
example : wordCseCanMemArith (.shift .ror 99 3 (.imm 255) : WordArith (BitVec 80)) = true := by rfl

-- Original rk_a3_firstRegOfArith_80.
example : wordCseFirstRegOfArith (.shift .lsl 99 3 (.reg 5) : WordArith (BitVec 80)) = 99 := by rfl

-- Original rk_a3_arithWrites_80.
example : wordCseArithWrites (.shift .lsl 99 3 (.reg 5) : WordArith (BitVec 80)) = [99] := by rfl

-- Original rk_a3_arithReads_80.
example : wordCseArithReads (.shift .lsl 99 3 (.reg 5) : WordArith (BitVec 80)) = [3, 5] := by rfl

-- Original rk_a3_can_mem_arith_80.
example : wordCseCanMemArith (.shift .lsl 99 3 (.reg 5) : WordArith (BitVec 80)) = false := by rfl

-- Original rk_a4_firstRegOfArith_80.
example : wordCseFirstRegOfArith (.div 99 3 5 : WordArith (BitVec 80)) = 99 := by rfl

-- Original rk_a4_arithWrites_80.
example : wordCseArithWrites (.div 99 3 5 : WordArith (BitVec 80)) = [99] := by rfl

-- Original rk_a4_arithReads_80.
example : wordCseArithReads (.div 99 3 5 : WordArith (BitVec 80)) = [3, 5] := by rfl

-- Original rk_a4_can_mem_arith_80.
example : wordCseCanMemArith (.div 99 3 5 : WordArith (BitVec 80)) = true := by rfl

-- Original rk_a5_firstRegOfArith_80.
example : wordCseFirstRegOfArith (.longMul 99 98 3 5 : WordArith (BitVec 80)) = 99 := by rfl

-- Original rk_a5_arithWrites_80.
example : wordCseArithWrites (.longMul 99 98 3 5 : WordArith (BitVec 80)) = [99, 98] := by rfl

-- Original rk_a5_arithReads_80.
example : wordCseArithReads (.longMul 99 98 3 5 : WordArith (BitVec 80)) = [3, 5] := by rfl

-- Original rk_a5_can_mem_arith_80.
example : wordCseCanMemArith (.longMul 99 98 3 5 : WordArith (BitVec 80)) = false := by rfl

-- Original rk_a6_firstRegOfArith_80.
example : wordCseFirstRegOfArith (.longDiv 99 98 3 5 7 : WordArith (BitVec 80)) = 99 := by rfl

-- Original rk_a6_arithWrites_80.
example : wordCseArithWrites (.longDiv 99 98 3 5 7 : WordArith (BitVec 80)) = [99, 98] := by rfl

-- Original rk_a6_arithReads_80.
example : wordCseArithReads (.longDiv 99 98 3 5 7 : WordArith (BitVec 80)) = [3, 5, 7] := by rfl

-- Original rk_a6_can_mem_arith_80.
example : wordCseCanMemArith (.longDiv 99 98 3 5 7 : WordArith (BitVec 80)) = false := by rfl

-- Original rk_a7_firstRegOfArith_80.
example : wordCseFirstRegOfArith (.cakeAddCarry 99 3 5 98 : WordArith (BitVec 80)) = 99 := by rfl

-- Original rk_a7_arithWrites_80.
example : wordCseArithWrites (.cakeAddCarry 99 3 5 98 : WordArith (BitVec 80)) = [99, 98] := by rfl

-- Original rk_a7_arithReads_80.
example : wordCseArithReads (.cakeAddCarry 99 3 5 98 : WordArith (BitVec 80)) = [3, 5, 98] := by rfl

-- Original rk_a7_can_mem_arith_80.
example : wordCseCanMemArith (.cakeAddCarry 99 3 5 98 : WordArith (BitVec 80)) = false := by rfl

-- Original rk_store_load.
example : wordCseIsStore .load = false := rfl

-- Original rk_store_load8.
example : wordCseIsStore .load8 = false := rfl

-- Original rk_store_load16.
example : wordCseIsStore .load16 = false := rfl

-- Original rk_store_load32.
example : wordCseIsStore .load32 = false := rfl

-- Original rk_store_store.
example : wordCseIsStore .store = true := rfl

-- Original rk_store_store8.
example : wordCseIsStore .store8 = true := rfl

-- Original rk_store_store16.
example : wordCseIsStore .store16 = true := rfl

-- Original rk_store_store32.
example : wordCseIsStore .store32 = true := rfl

-- Exclusion holds even under an arbitrary diagnostic instance, as required
-- by the existing full production codec-domain theorem.
example {α : Type} [WordCseHash α] (a b c d e : Nat) :
    wordCseCanMemArith (.addCarry a b c d e : WordArith α) = false := rfl

example : wordCseArithReads (.cakeAddCarry 99 3 5 99 : WordArith Nat) = [3,5,99] := rfl
example : wordCseArithWrites (.cakeAddCarry 99 3 5 99 : WordArith Nat) = [99,99] := rfl

#print axioms wordCseArithInfo_native
end Flapjack.Test.WordCseProductionRegisterClassifiers

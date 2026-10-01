import Flapjack.Compiler.Backend.WordCse.Proofs.KeyInjectivity
namespace Flapjack.Test.WordCseRegisterKeysParity
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordCse
-- rk_a0_firstRegOfArith_8
example : firstRegOfArith (width := 8) (.binop .add 99 3 (.reg 5)) = 99 := by rfl

-- rk_a0_arithWrites_8
example : arithWrites (width := 8) (.binop .add 99 3 (.reg 5)) = [99] := by rfl

-- rk_a0_arithReads_8
example : arithReads (width := 8) (.binop .add 99 3 (.reg 5)) = [3, 5] := by rfl

-- rk_a0_can_mem_arith_8
example : canMemArith (width := 8) (.binop .add 99 3 (.reg 5)) = true := by rfl

-- rk_a1_firstRegOfArith_8
example : firstRegOfArith (width := 8) (.binop .sub 99 4 (.imm 255)) = 99 := by rfl

-- rk_a1_arithWrites_8
example : arithWrites (width := 8) (.binop .sub 99 4 (.imm 255)) = [99] := by rfl

-- rk_a1_arithReads_8
example : arithReads (width := 8) (.binop .sub 99 4 (.imm 255)) = [4] := by rfl

-- rk_a1_can_mem_arith_8
example : canMemArith (width := 8) (.binop .sub 99 4 (.imm 255)) = false := by rfl

-- rk_a2_firstRegOfArith_8
example : firstRegOfArith (width := 8) (.shift .ror 99 3 (.imm 255)) = 99 := by rfl

-- rk_a2_arithWrites_8
example : arithWrites (width := 8) (.shift .ror 99 3 (.imm 255)) = [99] := by rfl

-- rk_a2_arithReads_8
example : arithReads (width := 8) (.shift .ror 99 3 (.imm 255)) = [3] := by rfl

-- rk_a2_can_mem_arith_8
example : canMemArith (width := 8) (.shift .ror 99 3 (.imm 255)) = true := by rfl

-- rk_a3_firstRegOfArith_8
example : firstRegOfArith (width := 8) (.shift .lsl 99 3 (.reg 5)) = 99 := by rfl

-- rk_a3_arithWrites_8
example : arithWrites (width := 8) (.shift .lsl 99 3 (.reg 5)) = [99] := by rfl

-- rk_a3_arithReads_8
example : arithReads (width := 8) (.shift .lsl 99 3 (.reg 5)) = [3, 5] := by rfl

-- rk_a3_can_mem_arith_8
example : canMemArith (width := 8) (.shift .lsl 99 3 (.reg 5)) = false := by rfl

-- rk_a4_firstRegOfArith_8
example : firstRegOfArith (width := 8) (.div 99 3 5) = 99 := by rfl

-- rk_a4_arithWrites_8
example : arithWrites (width := 8) (.div 99 3 5) = [99] := by rfl

-- rk_a4_arithReads_8
example : arithReads (width := 8) (.div 99 3 5) = [3, 5] := by rfl

-- rk_a4_can_mem_arith_8
example : canMemArith (width := 8) (.div 99 3 5) = true := by rfl

-- rk_a5_firstRegOfArith_8
example : firstRegOfArith (width := 8) (.longMul 99 98 3 5) = 99 := by rfl

-- rk_a5_arithWrites_8
example : arithWrites (width := 8) (.longMul 99 98 3 5) = [99, 98] := by rfl

-- rk_a5_arithReads_8
example : arithReads (width := 8) (.longMul 99 98 3 5) = [3, 5] := by rfl

-- rk_a5_can_mem_arith_8
example : canMemArith (width := 8) (.longMul 99 98 3 5) = false := by rfl

-- rk_a6_firstRegOfArith_8
example : firstRegOfArith (width := 8) (.longDiv 99 98 3 5 7) = 99 := by rfl

-- rk_a6_arithWrites_8
example : arithWrites (width := 8) (.longDiv 99 98 3 5 7) = [99, 98] := by rfl

-- rk_a6_arithReads_8
example : arithReads (width := 8) (.longDiv 99 98 3 5 7) = [3, 5, 7] := by rfl

-- rk_a6_can_mem_arith_8
example : canMemArith (width := 8) (.longDiv 99 98 3 5 7) = false := by rfl

-- rk_a7_firstRegOfArith_8
example : firstRegOfArith (width := 8) (.addCarry 99 3 5 98) = 99 := by rfl

-- rk_a7_arithWrites_8
example : arithWrites (width := 8) (.addCarry 99 3 5 98) = [99, 98] := by rfl

-- rk_a7_arithReads_8
example : arithReads (width := 8) (.addCarry 99 3 5 98) = [3, 5, 98] := by rfl

-- rk_a7_can_mem_arith_8
example : canMemArith (width := 8) (.addCarry 99 3 5 98) = false := by rfl

-- rk_a8_firstRegOfArith_8
example : firstRegOfArith (width := 8) (.addOverflow 99 3 5 98) = 99 := by rfl

-- rk_a8_arithWrites_8
example : arithWrites (width := 8) (.addOverflow 99 3 5 98) = [99, 98] := by rfl

-- rk_a8_arithReads_8
example : arithReads (width := 8) (.addOverflow 99 3 5 98) = [3, 5] := by rfl

-- rk_a8_can_mem_arith_8
example : canMemArith (width := 8) (.addOverflow 99 3 5 98) = false := by rfl

-- rk_a9_firstRegOfArith_8
example : firstRegOfArith (width := 8) (.subOverflow 99 3 5 98) = 99 := by rfl

-- rk_a9_arithWrites_8
example : arithWrites (width := 8) (.subOverflow 99 3 5 98) = [99, 98] := by rfl

-- rk_a9_arithReads_8
example : arithReads (width := 8) (.subOverflow 99 3 5 98) = [3, 5] := by rfl

-- rk_a9_can_mem_arith_8
example : canMemArith (width := 8) (.subOverflow 99 3 5 98) = false := by rfl

-- rk_a0_firstRegOfArith_80
example : firstRegOfArith (width := 80) (.binop .add 99 3 (.reg 5)) = 99 := by rfl

-- rk_a0_arithWrites_80
example : arithWrites (width := 80) (.binop .add 99 3 (.reg 5)) = [99] := by rfl

-- rk_a0_arithReads_80
example : arithReads (width := 80) (.binop .add 99 3 (.reg 5)) = [3, 5] := by rfl

-- rk_a0_can_mem_arith_80
example : canMemArith (width := 80) (.binop .add 99 3 (.reg 5)) = true := by rfl

-- rk_a1_firstRegOfArith_80
example : firstRegOfArith (width := 80) (.binop .sub 99 4 (.imm 255)) = 99 := by rfl

-- rk_a1_arithWrites_80
example : arithWrites (width := 80) (.binop .sub 99 4 (.imm 255)) = [99] := by rfl

-- rk_a1_arithReads_80
example : arithReads (width := 80) (.binop .sub 99 4 (.imm 255)) = [4] := by rfl

-- rk_a1_can_mem_arith_80
example : canMemArith (width := 80) (.binop .sub 99 4 (.imm 255)) = false := by rfl

-- rk_a2_firstRegOfArith_80
example : firstRegOfArith (width := 80) (.shift .ror 99 3 (.imm 255)) = 99 := by rfl

-- rk_a2_arithWrites_80
example : arithWrites (width := 80) (.shift .ror 99 3 (.imm 255)) = [99] := by rfl

-- rk_a2_arithReads_80
example : arithReads (width := 80) (.shift .ror 99 3 (.imm 255)) = [3] := by rfl

-- rk_a2_can_mem_arith_80
example : canMemArith (width := 80) (.shift .ror 99 3 (.imm 255)) = true := by rfl

-- rk_a3_firstRegOfArith_80
example : firstRegOfArith (width := 80) (.shift .lsl 99 3 (.reg 5)) = 99 := by rfl

-- rk_a3_arithWrites_80
example : arithWrites (width := 80) (.shift .lsl 99 3 (.reg 5)) = [99] := by rfl

-- rk_a3_arithReads_80
example : arithReads (width := 80) (.shift .lsl 99 3 (.reg 5)) = [3, 5] := by rfl

-- rk_a3_can_mem_arith_80
example : canMemArith (width := 80) (.shift .lsl 99 3 (.reg 5)) = false := by rfl

-- rk_a4_firstRegOfArith_80
example : firstRegOfArith (width := 80) (.div 99 3 5) = 99 := by rfl

-- rk_a4_arithWrites_80
example : arithWrites (width := 80) (.div 99 3 5) = [99] := by rfl

-- rk_a4_arithReads_80
example : arithReads (width := 80) (.div 99 3 5) = [3, 5] := by rfl

-- rk_a4_can_mem_arith_80
example : canMemArith (width := 80) (.div 99 3 5) = true := by rfl

-- rk_a5_firstRegOfArith_80
example : firstRegOfArith (width := 80) (.longMul 99 98 3 5) = 99 := by rfl

-- rk_a5_arithWrites_80
example : arithWrites (width := 80) (.longMul 99 98 3 5) = [99, 98] := by rfl

-- rk_a5_arithReads_80
example : arithReads (width := 80) (.longMul 99 98 3 5) = [3, 5] := by rfl

-- rk_a5_can_mem_arith_80
example : canMemArith (width := 80) (.longMul 99 98 3 5) = false := by rfl

-- rk_a6_firstRegOfArith_80
example : firstRegOfArith (width := 80) (.longDiv 99 98 3 5 7) = 99 := by rfl

-- rk_a6_arithWrites_80
example : arithWrites (width := 80) (.longDiv 99 98 3 5 7) = [99, 98] := by rfl

-- rk_a6_arithReads_80
example : arithReads (width := 80) (.longDiv 99 98 3 5 7) = [3, 5, 7] := by rfl

-- rk_a6_can_mem_arith_80
example : canMemArith (width := 80) (.longDiv 99 98 3 5 7) = false := by rfl

-- rk_a7_firstRegOfArith_80
example : firstRegOfArith (width := 80) (.addCarry 99 3 5 98) = 99 := by rfl

-- rk_a7_arithWrites_80
example : arithWrites (width := 80) (.addCarry 99 3 5 98) = [99, 98] := by rfl

-- rk_a7_arithReads_80
example : arithReads (width := 80) (.addCarry 99 3 5 98) = [3, 5, 98] := by rfl

-- rk_a7_can_mem_arith_80
example : canMemArith (width := 80) (.addCarry 99 3 5 98) = false := by rfl

-- rk_a8_firstRegOfArith_80
example : firstRegOfArith (width := 80) (.addOverflow 99 3 5 98) = 99 := by rfl

-- rk_a8_arithWrites_80
example : arithWrites (width := 80) (.addOverflow 99 3 5 98) = [99, 98] := by rfl

-- rk_a8_arithReads_80
example : arithReads (width := 80) (.addOverflow 99 3 5 98) = [3, 5] := by rfl

-- rk_a8_can_mem_arith_80
example : canMemArith (width := 80) (.addOverflow 99 3 5 98) = false := by rfl

-- rk_a9_firstRegOfArith_80
example : firstRegOfArith (width := 80) (.subOverflow 99 3 5 98) = 99 := by rfl

-- rk_a9_arithWrites_80
example : arithWrites (width := 80) (.subOverflow 99 3 5 98) = [99, 98] := by rfl

-- rk_a9_arithReads_80
example : arithReads (width := 80) (.subOverflow 99 3 5 98) = [3, 5] := by rfl

-- rk_a9_can_mem_arith_80
example : canMemArith (width := 80) (.subOverflow 99 3 5 98) = false := by rfl

-- rk_fp_fpLess
example : fpWrites (.fpLess 99 98 3) = [99] := by rfl

-- rk_fp_fpLessEqual
example : fpWrites (.fpLessEqual 99 98 3) = [99] := by rfl

-- rk_fp_fpEqual
example : fpWrites (.fpEqual 99 98 3) = [99] := by rfl

-- rk_fp_fpAbs
example : fpWrites (.fpAbs 99 98) = [] := by rfl

-- rk_fp_fpNeg
example : fpWrites (.fpNeg 99 98) = [] := by rfl

-- rk_fp_fpSqrt
example : fpWrites (.fpSqrt 99 98) = [] := by rfl

-- rk_fp_fpAdd
example : fpWrites (.fpAdd 99 98 3) = [] := by rfl

-- rk_fp_fpSub
example : fpWrites (.fpSub 99 98 3) = [] := by rfl

-- rk_fp_fpMul
example : fpWrites (.fpMul 99 98 3) = [] := by rfl

-- rk_fp_fpDiv
example : fpWrites (.fpDiv 99 98 3) = [] := by rfl

-- rk_fp_fpFma
example : fpWrites (.fpFma 99 98 3) = [] := by rfl

-- rk_fp_fpMov
example : fpWrites (.fpMov 99 98) = [] := by rfl

-- rk_fp_fpMovToReg
example : fpWrites (.fpMovToReg 99 98 3) = [99, 98] := by rfl

-- rk_fp_fpMovFromReg
example : fpWrites (.fpMovFromReg 99 98 3) = [] := by rfl

-- rk_fp_fpToInt
example : fpWrites (.fpToInt 99 98) = [] := by rfl

-- rk_fp_fpFromInt
example : fpWrites (.fpFromInt 99 98) = [] := by rfl

-- rk_store_load
example : isStore .load = false := by rfl

-- rk_store_load8
example : isStore .load8 = false := by rfl

-- rk_store_load16
example : isStore .load16 = false := by rfl

-- rk_store_load32
example : isStore .load32 = false := by rfl

-- rk_store_store
example : isStore .store = true := by rfl

-- rk_store_store8
example : isStore .store8 = true := by rfl

-- rk_store_store16
example : isStore .store16 = true := by rfl

-- rk_store_store32
example : isStore .store32 = true := by rfl

example {width : Nat} [NeZero width] (a b : BitVec width)
    (h : wordToNum a = wordToNum b) : a = b := (wordToNumUnique a b).mp h
example (a b : BinOp) (h : arithOpToNum a = arithOpToNum b) : a = b :=
  (arithOpToNumEq a b).mp h
example (a b : HolMemop) (h : memOpToNum a = memOpToNum b) : a = b :=
  (memOpToNumEq a b).mp h
example (a b : Shift) (h : shiftToNum a = shiftToNum b) : a = b :=
  (shiftToNumEq a b).mp h
end Flapjack.Test.WordCseRegisterKeysParity

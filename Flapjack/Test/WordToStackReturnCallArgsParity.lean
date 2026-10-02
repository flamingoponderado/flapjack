import Flapjack.Compiler.Backend.WordToStack.Proofs.ReturnCallArgs

namespace Flapjack.Test.WordToStackReturnCallArgsParity
open Flapjack Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
/- Expected whole-predicate values read from fresh original captured HOL output;
source/native carriers reuse reviewed constructor fixtures. Regression only. -/

-- rca_pred_inst_8_1_0
example : callArgs (.inst (.skip:HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_8_1_1
example : callArgs (.inst (.skip:HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_9_1_0
example : callArgs (.inst (.const 1 255:HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_9_1_1
example : callArgs (.inst (.const 1 255:HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_10_1_0
example : callArgs (.inst (.mem .load 1 (.addr 2 255):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_10_1_1
example : callArgs (.inst (.mem .load 1 (.addr 2 255):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_11_1_0
example : callArgs (.inst (.mem .load8 1 (.addr 2 255):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_11_1_1
example : callArgs (.inst (.mem .load8 1 (.addr 2 255):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_12_1_0
example : callArgs (.inst (.mem .load16 1 (.addr 2 255):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_12_1_1
example : callArgs (.inst (.mem .load16 1 (.addr 2 255):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_13_1_0
example : callArgs (.inst (.mem .load32 1 (.addr 2 255):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_13_1_1
example : callArgs (.inst (.mem .load32 1 (.addr 2 255):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_14_1_0
example : callArgs (.inst (.mem .store 1 (.addr 2 255):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_14_1_1
example : callArgs (.inst (.mem .store 1 (.addr 2 255):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_15_1_0
example : callArgs (.inst (.mem .store8 1 (.addr 2 255):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_15_1_1
example : callArgs (.inst (.mem .store8 1 (.addr 2 255):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_16_1_0
example : callArgs (.inst (.mem .store16 1 (.addr 2 255):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_16_1_1
example : callArgs (.inst (.mem .store16 1 (.addr 2 255):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_17_1_0
example : callArgs (.inst (.mem .store32 1 (.addr 2 255):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_17_1_1
example : callArgs (.inst (.mem .store32 1 (.addr 2 255):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_18_1_0
example : callArgs (.inst (.arith (.binop .add 1 2 (.reg 3)):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_18_1_1
example : callArgs (.inst (.arith (.binop .add 1 2 (.reg 3)):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_19_1_0
example : callArgs (.inst (.arith (.binop .and 1 2 (.imm 255)):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_19_1_1
example : callArgs (.inst (.arith (.binop .and 1 2 (.imm 255)):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_20_1_0
example : callArgs (.inst (.arith (.shift .lsl 1 2 (.reg 3)):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_20_1_1
example : callArgs (.inst (.arith (.shift .lsl 1 2 (.reg 3)):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_21_1_0
example : callArgs (.inst (.arith (.shift .ror 1 2 (.imm 255)):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_21_1_1
example : callArgs (.inst (.arith (.shift .ror 1 2 (.imm 255)):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_22_1_0
example : callArgs (.inst (.arith (.div 1 2 3):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_22_1_1
example : callArgs (.inst (.arith (.div 1 2 3):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_23_1_0
example : callArgs (.inst (.arith (.longMul 1 2 3 4):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_23_1_1
example : callArgs (.inst (.arith (.longMul 1 2 3 4):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_24_1_0
example : callArgs (.inst (.arith (.longDiv 1 2 3 4 5):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_24_1_1
example : callArgs (.inst (.arith (.longDiv 1 2 3 4 5):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_25_1_0
example : callArgs (.inst (.arith (.addCarry 1 2 3 4):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_25_1_1
example : callArgs (.inst (.arith (.addCarry 1 2 3 4):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_26_1_0
example : callArgs (.inst (.arith (.addOverflow 1 2 3 4):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_26_1_1
example : callArgs (.inst (.arith (.addOverflow 1 2 3 4):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_27_1_0
example : callArgs (.inst (.arith (.subOverflow 1 2 3 4):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_27_1_1
example : callArgs (.inst (.arith (.subOverflow 1 2 3 4):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_28_1_0
example : callArgs (.inst (.fp (.fpLess 1 99 100):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_28_1_1
example : callArgs (.inst (.fp (.fpLess 1 99 100):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_29_1_0
example : callArgs (.inst (.fp (.fpLessEqual 1 99 100):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_29_1_1
example : callArgs (.inst (.fp (.fpLessEqual 1 99 100):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_30_1_0
example : callArgs (.inst (.fp (.fpEqual 1 99 100):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_30_1_1
example : callArgs (.inst (.fp (.fpEqual 1 99 100):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_31_1_0
example : callArgs (.inst (.fp (.fpAbs 100 100):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_31_1_1
example : callArgs (.inst (.fp (.fpAbs 100 100):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_32_1_0
example : callArgs (.inst (.fp (.fpNeg 100 100):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_32_1_1
example : callArgs (.inst (.fp (.fpNeg 100 100):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_33_1_0
example : callArgs (.inst (.fp (.fpSqrt 100 100):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_33_1_1
example : callArgs (.inst (.fp (.fpSqrt 100 100):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_34_1_0
example : callArgs (.inst (.fp (.fpAdd 100 100 100):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_34_1_1
example : callArgs (.inst (.fp (.fpAdd 100 100 100):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_35_1_0
example : callArgs (.inst (.fp (.fpSub 100 100 100):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_35_1_1
example : callArgs (.inst (.fp (.fpSub 100 100 100):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_36_1_0
example : callArgs (.inst (.fp (.fpMul 100 100 100):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_36_1_1
example : callArgs (.inst (.fp (.fpMul 100 100 100):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_37_1_0
example : callArgs (.inst (.fp (.fpDiv 100 100 100):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_37_1_1
example : callArgs (.inst (.fp (.fpDiv 100 100 100):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_38_1_0
example : callArgs (.inst (.fp (.fpFma 100 100 100):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_38_1_1
example : callArgs (.inst (.fp (.fpFma 100 100 100):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_39_1_0
example : callArgs (.inst (.fp (.fpMov 100 100):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_39_1_1
example : callArgs (.inst (.fp (.fpMov 100 100):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_40_1_0
example : callArgs (.inst (.fp (.fpToInt 100 100):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_40_1_1
example : callArgs (.inst (.fp (.fpToInt 100 100):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_41_1_0
example : callArgs (.inst (.fp (.fpFromInt 100 100):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_41_1_1
example : callArgs (.inst (.fp (.fpFromInt 100 100):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_42_1_0
example : callArgs (.inst (.fp (.fpMovToReg 1 2 100):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_42_1_1
example : callArgs (.inst (.fp (.fpMovToReg 1 2 100):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_43_1_0
example : callArgs (.inst (.fp (.fpMovFromReg 100 1 2):HolInst 1) : HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_43_1_1
example : callArgs (.inst (.fp (.fpMovFromReg 100 1 2):HolInst 1) : HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_44_1_0
example : callArgs (.skip:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_44_1_1
example : callArgs (.skip:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_45_1_0
example : callArgs (.inst (.const 1 255):HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_45_1_1
example : callArgs (.inst (.const 1 255):HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_46_1_0
example : callArgs (.get 1 .currHeap:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_46_1_1
example : callArgs (.get 1 .currHeap:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_47_1_0
example : callArgs (.set .currHeap 1:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_47_1_1
example : callArgs (.set .currHeap 1:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_48_1_0
example : callArgs (.set .bitmapBase 1:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_48_1_1
example : callArgs (.set .bitmapBase 1:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_49_1_0
example : callArgs (.opCurrHeap .add 1 2:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_49_1_1
example : callArgs (.opCurrHeap .add 1 2:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_50_1_0
example : callArgs (.call none (.inl 999) (some (.halt 100,999,999)):HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_50_1_1
example : callArgs (.call none (.inl 999) (some (.halt 100,999,999)):HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_51_1_0
example : callArgs (.call none (.inr 2) none:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_51_1_1
example : callArgs (.call none (.inr 2) none:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_52_1_0
example : ¬ callArgs (.call (some (.halt 1,2,999,999)) (.inl 999) (some (.halt 3,999,999)):HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_52_1_1
example : ¬ callArgs (.call (some (.halt 1,2,999,999)) (.inl 999) (some (.halt 3,999,999)):HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_53_1_0
example : ¬ callArgs (.seq (.halt 1) (.halt 2):HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_53_1_1
example : ¬ callArgs (.seq (.halt 1) (.halt 2):HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_54_1_0
example : ¬ callArgs (.ite .equal 1 (.reg 2) .skip (.halt 3):HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_54_1_1
example : ¬ callArgs (.ite .equal 1 (.reg 2) .skip (.halt 3):HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_55_1_0
example : callArgs (.ite .equal 1 (.imm 255) .skip .skip:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_55_1_1
example : callArgs (.ite .equal 1 (.imm 255) .skip .skip:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_56_1_0
example : ¬ callArgs (.loop (.halt 2):HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_56_1_1
example : ¬ callArgs (.loop (.halt 2):HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_57_1_0
example : callArgs (.jumpLower 1 2 999:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_57_1_1
example : callArgs (.jumpLower 1 2 999:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_58_1_0
example : callArgs (.alloc 999:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_58_1_1
example : callArgs (.alloc 999:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_59_1_0
example : callArgs (.storeConsts 0 0 (some 999):HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_59_1_1
example : callArgs (.storeConsts 0 0 (some 999):HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_60_1_0
example : callArgs (.raise 1:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_60_1_1
example : callArgs (.raise 1:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_61_1_0
example : callArgs (.ret 1:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_61_1_1
example : callArgs (.ret 1:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_62_1_0
example : callArgs (.break 999:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_62_1_1
example : callArgs (.break 999:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_63_1_0
example : callArgs (.continue 999:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_63_1_1
example : callArgs (.continue 999:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_64_1_0
example : ¬ callArgs (.ffi (Flapjack.Basis.Pure.MlString.ofString "x") 1 2 3 4 5:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_64_1_1
example : ¬ callArgs (.ffi (Flapjack.Basis.Pure.MlString.ofString "x") 1 2 3 4 5:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_65_1_0
example : callArgs (.tick:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_65_1_1
example : callArgs (.tick:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_66_1_0
example : callArgs (.locValue 1 999 999:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_66_1_1
example : callArgs (.locValue 1 999 999:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_67_1_0
example : ¬ callArgs (.install 1 2 3 4 5:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_67_1_1
example : ¬ callArgs (.install 1 2 3 4 5:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_68_1_0
example : callArgs (.shMemOp .load16 1 (.addr 2 255):HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_68_1_1
example : callArgs (.shMemOp .load16 1 (.addr 2 255):HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_69_1_0
example : callArgs (.codeBufferWrite 1 2:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_69_1_1
example : callArgs (.codeBufferWrite 1 2:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_70_1_0
example : callArgs (.dataBufferWrite 1 2:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_70_1_1
example : callArgs (.dataBufferWrite 1 2:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_71_1_0
example : callArgs (.rawCall 999:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_71_1_1
example : callArgs (.rawCall 999:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_72_1_0
example : callArgs (.stackAlloc 999:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_72_1_1
example : callArgs (.stackAlloc 999:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_73_1_0
example : callArgs (.stackFree 999:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_73_1_1
example : callArgs (.stackFree 999:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_74_1_0
example : callArgs (.stackStore 1 999:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_74_1_1
example : callArgs (.stackStore 1 999:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_75_1_0
example : callArgs (.stackStore 999 1:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_75_1_1
example : callArgs (.stackStore 999 1:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_76_1_0
example : callArgs (.stackLoad 1 999:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_76_1_1
example : callArgs (.stackLoad 1 999:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_77_1_0
example : callArgs (.stackLoad 999 1:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_77_1_1
example : callArgs (.stackLoad 999 1:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_78_1_0
example : callArgs (.stackStoreAny 1 2:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_78_1_1
example : callArgs (.stackStoreAny 1 2:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_79_1_0
example : callArgs (.stackLoadAny 1 2:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_79_1_1
example : callArgs (.stackLoadAny 1 2:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_80_1_0
example : callArgs (.stackGetSize 1:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_80_1_1
example : callArgs (.stackGetSize 1:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_81_1_0
example : callArgs (.stackSetSize 1:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_81_1_1
example : callArgs (.stackSetSize 1:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_82_1_0
example : callArgs (.bitmapLoad 1 2:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_82_1_1
example : callArgs (.bitmapLoad 1 2:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_83_1_0
example : callArgs (.halt 1:HolProg 1) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_83_1_1
example : ¬ callArgs (.halt 1:HolProg 1) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_8_64_0
example : callArgs (.inst (.skip:HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_8_64_1
example : callArgs (.inst (.skip:HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_9_64_0
example : callArgs (.inst (.const 1 255:HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_9_64_1
example : callArgs (.inst (.const 1 255:HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_10_64_0
example : callArgs (.inst (.mem .load 1 (.addr 2 255):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_10_64_1
example : callArgs (.inst (.mem .load 1 (.addr 2 255):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_11_64_0
example : callArgs (.inst (.mem .load8 1 (.addr 2 255):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_11_64_1
example : callArgs (.inst (.mem .load8 1 (.addr 2 255):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_12_64_0
example : callArgs (.inst (.mem .load16 1 (.addr 2 255):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_12_64_1
example : callArgs (.inst (.mem .load16 1 (.addr 2 255):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_13_64_0
example : callArgs (.inst (.mem .load32 1 (.addr 2 255):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_13_64_1
example : callArgs (.inst (.mem .load32 1 (.addr 2 255):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_14_64_0
example : callArgs (.inst (.mem .store 1 (.addr 2 255):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_14_64_1
example : callArgs (.inst (.mem .store 1 (.addr 2 255):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_15_64_0
example : callArgs (.inst (.mem .store8 1 (.addr 2 255):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_15_64_1
example : callArgs (.inst (.mem .store8 1 (.addr 2 255):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_16_64_0
example : callArgs (.inst (.mem .store16 1 (.addr 2 255):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_16_64_1
example : callArgs (.inst (.mem .store16 1 (.addr 2 255):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_17_64_0
example : callArgs (.inst (.mem .store32 1 (.addr 2 255):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_17_64_1
example : callArgs (.inst (.mem .store32 1 (.addr 2 255):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_18_64_0
example : callArgs (.inst (.arith (.binop .add 1 2 (.reg 3)):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_18_64_1
example : callArgs (.inst (.arith (.binop .add 1 2 (.reg 3)):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_19_64_0
example : callArgs (.inst (.arith (.binop .and 1 2 (.imm 255)):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_19_64_1
example : callArgs (.inst (.arith (.binop .and 1 2 (.imm 255)):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_20_64_0
example : callArgs (.inst (.arith (.shift .lsl 1 2 (.reg 3)):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_20_64_1
example : callArgs (.inst (.arith (.shift .lsl 1 2 (.reg 3)):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_21_64_0
example : callArgs (.inst (.arith (.shift .ror 1 2 (.imm 255)):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_21_64_1
example : callArgs (.inst (.arith (.shift .ror 1 2 (.imm 255)):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_22_64_0
example : callArgs (.inst (.arith (.div 1 2 3):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_22_64_1
example : callArgs (.inst (.arith (.div 1 2 3):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_23_64_0
example : callArgs (.inst (.arith (.longMul 1 2 3 4):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_23_64_1
example : callArgs (.inst (.arith (.longMul 1 2 3 4):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_24_64_0
example : callArgs (.inst (.arith (.longDiv 1 2 3 4 5):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_24_64_1
example : callArgs (.inst (.arith (.longDiv 1 2 3 4 5):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_25_64_0
example : callArgs (.inst (.arith (.addCarry 1 2 3 4):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_25_64_1
example : callArgs (.inst (.arith (.addCarry 1 2 3 4):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_26_64_0
example : callArgs (.inst (.arith (.addOverflow 1 2 3 4):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_26_64_1
example : callArgs (.inst (.arith (.addOverflow 1 2 3 4):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_27_64_0
example : callArgs (.inst (.arith (.subOverflow 1 2 3 4):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_27_64_1
example : callArgs (.inst (.arith (.subOverflow 1 2 3 4):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_28_64_0
example : callArgs (.inst (.fp (.fpLess 1 99 100):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_28_64_1
example : callArgs (.inst (.fp (.fpLess 1 99 100):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_29_64_0
example : callArgs (.inst (.fp (.fpLessEqual 1 99 100):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_29_64_1
example : callArgs (.inst (.fp (.fpLessEqual 1 99 100):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_30_64_0
example : callArgs (.inst (.fp (.fpEqual 1 99 100):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_30_64_1
example : callArgs (.inst (.fp (.fpEqual 1 99 100):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_31_64_0
example : callArgs (.inst (.fp (.fpAbs 100 100):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_31_64_1
example : callArgs (.inst (.fp (.fpAbs 100 100):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_32_64_0
example : callArgs (.inst (.fp (.fpNeg 100 100):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_32_64_1
example : callArgs (.inst (.fp (.fpNeg 100 100):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_33_64_0
example : callArgs (.inst (.fp (.fpSqrt 100 100):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_33_64_1
example : callArgs (.inst (.fp (.fpSqrt 100 100):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_34_64_0
example : callArgs (.inst (.fp (.fpAdd 100 100 100):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_34_64_1
example : callArgs (.inst (.fp (.fpAdd 100 100 100):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_35_64_0
example : callArgs (.inst (.fp (.fpSub 100 100 100):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_35_64_1
example : callArgs (.inst (.fp (.fpSub 100 100 100):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_36_64_0
example : callArgs (.inst (.fp (.fpMul 100 100 100):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_36_64_1
example : callArgs (.inst (.fp (.fpMul 100 100 100):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_37_64_0
example : callArgs (.inst (.fp (.fpDiv 100 100 100):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_37_64_1
example : callArgs (.inst (.fp (.fpDiv 100 100 100):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_38_64_0
example : callArgs (.inst (.fp (.fpFma 100 100 100):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_38_64_1
example : callArgs (.inst (.fp (.fpFma 100 100 100):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_39_64_0
example : callArgs (.inst (.fp (.fpMov 100 100):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_39_64_1
example : callArgs (.inst (.fp (.fpMov 100 100):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_40_64_0
example : callArgs (.inst (.fp (.fpToInt 100 100):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_40_64_1
example : callArgs (.inst (.fp (.fpToInt 100 100):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_41_64_0
example : callArgs (.inst (.fp (.fpFromInt 100 100):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_41_64_1
example : callArgs (.inst (.fp (.fpFromInt 100 100):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_42_64_0
example : callArgs (.inst (.fp (.fpMovToReg 1 2 100):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_42_64_1
example : callArgs (.inst (.fp (.fpMovToReg 1 2 100):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_43_64_0
example : callArgs (.inst (.fp (.fpMovFromReg 100 1 2):HolInst 64) : HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_43_64_1
example : callArgs (.inst (.fp (.fpMovFromReg 100 1 2):HolInst 64) : HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_44_64_0
example : callArgs (.skip:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_44_64_1
example : callArgs (.skip:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_45_64_0
example : callArgs (.inst (.const 1 255):HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_45_64_1
example : callArgs (.inst (.const 1 255):HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_46_64_0
example : callArgs (.get 1 .currHeap:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_46_64_1
example : callArgs (.get 1 .currHeap:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_47_64_0
example : callArgs (.set .currHeap 1:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_47_64_1
example : callArgs (.set .currHeap 1:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_48_64_0
example : callArgs (.set .bitmapBase 1:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_48_64_1
example : callArgs (.set .bitmapBase 1:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_49_64_0
example : callArgs (.opCurrHeap .add 1 2:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_49_64_1
example : callArgs (.opCurrHeap .add 1 2:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_50_64_0
example : callArgs (.call none (.inl 999) (some (.halt 100,999,999)):HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_50_64_1
example : callArgs (.call none (.inl 999) (some (.halt 100,999,999)):HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_51_64_0
example : callArgs (.call none (.inr 2) none:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_51_64_1
example : callArgs (.call none (.inr 2) none:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_52_64_0
example : ¬ callArgs (.call (some (.halt 1,2,999,999)) (.inl 999) (some (.halt 3,999,999)):HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_52_64_1
example : ¬ callArgs (.call (some (.halt 1,2,999,999)) (.inl 999) (some (.halt 3,999,999)):HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_53_64_0
example : ¬ callArgs (.seq (.halt 1) (.halt 2):HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_53_64_1
example : ¬ callArgs (.seq (.halt 1) (.halt 2):HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_54_64_0
example : ¬ callArgs (.ite .equal 1 (.reg 2) .skip (.halt 3):HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_54_64_1
example : ¬ callArgs (.ite .equal 1 (.reg 2) .skip (.halt 3):HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_55_64_0
example : callArgs (.ite .equal 1 (.imm 255) .skip .skip:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_55_64_1
example : callArgs (.ite .equal 1 (.imm 255) .skip .skip:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_56_64_0
example : ¬ callArgs (.loop (.halt 2):HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_56_64_1
example : ¬ callArgs (.loop (.halt 2):HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_57_64_0
example : callArgs (.jumpLower 1 2 999:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_57_64_1
example : callArgs (.jumpLower 1 2 999:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_58_64_0
example : callArgs (.alloc 999:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_58_64_1
example : callArgs (.alloc 999:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_59_64_0
example : callArgs (.storeConsts 0 0 (some 999):HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_59_64_1
example : callArgs (.storeConsts 0 0 (some 999):HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_60_64_0
example : callArgs (.raise 1:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_60_64_1
example : callArgs (.raise 1:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_61_64_0
example : callArgs (.ret 1:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_61_64_1
example : callArgs (.ret 1:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_62_64_0
example : callArgs (.break 999:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_62_64_1
example : callArgs (.break 999:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_63_64_0
example : callArgs (.continue 999:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_63_64_1
example : callArgs (.continue 999:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_64_64_0
example : ¬ callArgs (.ffi (Flapjack.Basis.Pure.MlString.ofString "x") 1 2 3 4 5:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_64_64_1
example : ¬ callArgs (.ffi (Flapjack.Basis.Pure.MlString.ofString "x") 1 2 3 4 5:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_65_64_0
example : callArgs (.tick:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_65_64_1
example : callArgs (.tick:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_66_64_0
example : callArgs (.locValue 1 999 999:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_66_64_1
example : callArgs (.locValue 1 999 999:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_67_64_0
example : ¬ callArgs (.install 1 2 3 4 5:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_67_64_1
example : ¬ callArgs (.install 1 2 3 4 5:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_68_64_0
example : callArgs (.shMemOp .load16 1 (.addr 2 255):HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_68_64_1
example : callArgs (.shMemOp .load16 1 (.addr 2 255):HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_69_64_0
example : callArgs (.codeBufferWrite 1 2:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_69_64_1
example : callArgs (.codeBufferWrite 1 2:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_70_64_0
example : callArgs (.dataBufferWrite 1 2:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_70_64_1
example : callArgs (.dataBufferWrite 1 2:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_71_64_0
example : callArgs (.rawCall 999:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_71_64_1
example : callArgs (.rawCall 999:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_72_64_0
example : callArgs (.stackAlloc 999:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_72_64_1
example : callArgs (.stackAlloc 999:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_73_64_0
example : callArgs (.stackFree 999:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_73_64_1
example : callArgs (.stackFree 999:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_74_64_0
example : callArgs (.stackStore 1 999:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_74_64_1
example : callArgs (.stackStore 1 999:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_75_64_0
example : callArgs (.stackStore 999 1:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_75_64_1
example : callArgs (.stackStore 999 1:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_76_64_0
example : callArgs (.stackLoad 1 999:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_76_64_1
example : callArgs (.stackLoad 1 999:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_77_64_0
example : callArgs (.stackLoad 999 1:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_77_64_1
example : callArgs (.stackLoad 999 1:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_78_64_0
example : callArgs (.stackStoreAny 1 2:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_78_64_1
example : callArgs (.stackStoreAny 1 2:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_79_64_0
example : callArgs (.stackLoadAny 1 2:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_79_64_1
example : callArgs (.stackLoadAny 1 2:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_80_64_0
example : callArgs (.stackGetSize 1:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_80_64_1
example : callArgs (.stackGetSize 1:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_81_64_0
example : callArgs (.stackSetSize 1:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_81_64_1
example : callArgs (.stackSetSize 1:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_82_64_0
example : callArgs (.bitmapLoad 1 2:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_82_64_1
example : callArgs (.bitmapLoad 1 2:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_83_64_0
example : callArgs (.halt 1:HolProg 64) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_83_64_1
example : ¬ callArgs (.halt 1:HolProg 64) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_8_80_0
example : callArgs (.inst (.skip:HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_8_80_1
example : callArgs (.inst (.skip:HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_9_80_0
example : callArgs (.inst (.const 1 255:HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_9_80_1
example : callArgs (.inst (.const 1 255:HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_10_80_0
example : callArgs (.inst (.mem .load 1 (.addr 2 255):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_10_80_1
example : callArgs (.inst (.mem .load 1 (.addr 2 255):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_11_80_0
example : callArgs (.inst (.mem .load8 1 (.addr 2 255):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_11_80_1
example : callArgs (.inst (.mem .load8 1 (.addr 2 255):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_12_80_0
example : callArgs (.inst (.mem .load16 1 (.addr 2 255):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_12_80_1
example : callArgs (.inst (.mem .load16 1 (.addr 2 255):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_13_80_0
example : callArgs (.inst (.mem .load32 1 (.addr 2 255):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_13_80_1
example : callArgs (.inst (.mem .load32 1 (.addr 2 255):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_14_80_0
example : callArgs (.inst (.mem .store 1 (.addr 2 255):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_14_80_1
example : callArgs (.inst (.mem .store 1 (.addr 2 255):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_15_80_0
example : callArgs (.inst (.mem .store8 1 (.addr 2 255):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_15_80_1
example : callArgs (.inst (.mem .store8 1 (.addr 2 255):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_16_80_0
example : callArgs (.inst (.mem .store16 1 (.addr 2 255):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_16_80_1
example : callArgs (.inst (.mem .store16 1 (.addr 2 255):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_17_80_0
example : callArgs (.inst (.mem .store32 1 (.addr 2 255):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_17_80_1
example : callArgs (.inst (.mem .store32 1 (.addr 2 255):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_18_80_0
example : callArgs (.inst (.arith (.binop .add 1 2 (.reg 3)):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_18_80_1
example : callArgs (.inst (.arith (.binop .add 1 2 (.reg 3)):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_19_80_0
example : callArgs (.inst (.arith (.binop .and 1 2 (.imm 255)):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_19_80_1
example : callArgs (.inst (.arith (.binop .and 1 2 (.imm 255)):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_20_80_0
example : callArgs (.inst (.arith (.shift .lsl 1 2 (.reg 3)):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_20_80_1
example : callArgs (.inst (.arith (.shift .lsl 1 2 (.reg 3)):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_21_80_0
example : callArgs (.inst (.arith (.shift .ror 1 2 (.imm 255)):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_21_80_1
example : callArgs (.inst (.arith (.shift .ror 1 2 (.imm 255)):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_22_80_0
example : callArgs (.inst (.arith (.div 1 2 3):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_22_80_1
example : callArgs (.inst (.arith (.div 1 2 3):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_23_80_0
example : callArgs (.inst (.arith (.longMul 1 2 3 4):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_23_80_1
example : callArgs (.inst (.arith (.longMul 1 2 3 4):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_24_80_0
example : callArgs (.inst (.arith (.longDiv 1 2 3 4 5):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_24_80_1
example : callArgs (.inst (.arith (.longDiv 1 2 3 4 5):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_25_80_0
example : callArgs (.inst (.arith (.addCarry 1 2 3 4):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_25_80_1
example : callArgs (.inst (.arith (.addCarry 1 2 3 4):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_26_80_0
example : callArgs (.inst (.arith (.addOverflow 1 2 3 4):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_26_80_1
example : callArgs (.inst (.arith (.addOverflow 1 2 3 4):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_27_80_0
example : callArgs (.inst (.arith (.subOverflow 1 2 3 4):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_27_80_1
example : callArgs (.inst (.arith (.subOverflow 1 2 3 4):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_28_80_0
example : callArgs (.inst (.fp (.fpLess 1 99 100):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_28_80_1
example : callArgs (.inst (.fp (.fpLess 1 99 100):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_29_80_0
example : callArgs (.inst (.fp (.fpLessEqual 1 99 100):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_29_80_1
example : callArgs (.inst (.fp (.fpLessEqual 1 99 100):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_30_80_0
example : callArgs (.inst (.fp (.fpEqual 1 99 100):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_30_80_1
example : callArgs (.inst (.fp (.fpEqual 1 99 100):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_31_80_0
example : callArgs (.inst (.fp (.fpAbs 100 100):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_31_80_1
example : callArgs (.inst (.fp (.fpAbs 100 100):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_32_80_0
example : callArgs (.inst (.fp (.fpNeg 100 100):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_32_80_1
example : callArgs (.inst (.fp (.fpNeg 100 100):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_33_80_0
example : callArgs (.inst (.fp (.fpSqrt 100 100):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_33_80_1
example : callArgs (.inst (.fp (.fpSqrt 100 100):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_34_80_0
example : callArgs (.inst (.fp (.fpAdd 100 100 100):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_34_80_1
example : callArgs (.inst (.fp (.fpAdd 100 100 100):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_35_80_0
example : callArgs (.inst (.fp (.fpSub 100 100 100):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_35_80_1
example : callArgs (.inst (.fp (.fpSub 100 100 100):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_36_80_0
example : callArgs (.inst (.fp (.fpMul 100 100 100):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_36_80_1
example : callArgs (.inst (.fp (.fpMul 100 100 100):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_37_80_0
example : callArgs (.inst (.fp (.fpDiv 100 100 100):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_37_80_1
example : callArgs (.inst (.fp (.fpDiv 100 100 100):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_38_80_0
example : callArgs (.inst (.fp (.fpFma 100 100 100):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_38_80_1
example : callArgs (.inst (.fp (.fpFma 100 100 100):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_39_80_0
example : callArgs (.inst (.fp (.fpMov 100 100):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_39_80_1
example : callArgs (.inst (.fp (.fpMov 100 100):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_40_80_0
example : callArgs (.inst (.fp (.fpToInt 100 100):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_40_80_1
example : callArgs (.inst (.fp (.fpToInt 100 100):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_41_80_0
example : callArgs (.inst (.fp (.fpFromInt 100 100):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_41_80_1
example : callArgs (.inst (.fp (.fpFromInt 100 100):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_42_80_0
example : callArgs (.inst (.fp (.fpMovToReg 1 2 100):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_42_80_1
example : callArgs (.inst (.fp (.fpMovToReg 1 2 100):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_inst_43_80_0
example : callArgs (.inst (.fp (.fpMovFromReg 100 1 2):HolInst 80) : HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_inst_43_80_1
example : callArgs (.inst (.fp (.fpMovFromReg 100 1 2):HolInst 80) : HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_44_80_0
example : callArgs (.skip:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_44_80_1
example : callArgs (.skip:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_45_80_0
example : callArgs (.inst (.const 1 255):HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_45_80_1
example : callArgs (.inst (.const 1 255):HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_46_80_0
example : callArgs (.get 1 .currHeap:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_46_80_1
example : callArgs (.get 1 .currHeap:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_47_80_0
example : callArgs (.set .currHeap 1:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_47_80_1
example : callArgs (.set .currHeap 1:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_48_80_0
example : callArgs (.set .bitmapBase 1:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_48_80_1
example : callArgs (.set .bitmapBase 1:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_49_80_0
example : callArgs (.opCurrHeap .add 1 2:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_49_80_1
example : callArgs (.opCurrHeap .add 1 2:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_50_80_0
example : callArgs (.call none (.inl 999) (some (.halt 100,999,999)):HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_50_80_1
example : callArgs (.call none (.inl 999) (some (.halt 100,999,999)):HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_51_80_0
example : callArgs (.call none (.inr 2) none:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_51_80_1
example : callArgs (.call none (.inr 2) none:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_52_80_0
example : ¬ callArgs (.call (some (.halt 1,2,999,999)) (.inl 999) (some (.halt 3,999,999)):HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_52_80_1
example : ¬ callArgs (.call (some (.halt 1,2,999,999)) (.inl 999) (some (.halt 3,999,999)):HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_53_80_0
example : ¬ callArgs (.seq (.halt 1) (.halt 2):HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_53_80_1
example : ¬ callArgs (.seq (.halt 1) (.halt 2):HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_54_80_0
example : ¬ callArgs (.ite .equal 1 (.reg 2) .skip (.halt 3):HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_54_80_1
example : ¬ callArgs (.ite .equal 1 (.reg 2) .skip (.halt 3):HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_55_80_0
example : callArgs (.ite .equal 1 (.imm 255) .skip .skip:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_55_80_1
example : callArgs (.ite .equal 1 (.imm 255) .skip .skip:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_56_80_0
example : ¬ callArgs (.loop (.halt 2):HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_56_80_1
example : ¬ callArgs (.loop (.halt 2):HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_57_80_0
example : callArgs (.jumpLower 1 2 999:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_57_80_1
example : callArgs (.jumpLower 1 2 999:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_58_80_0
example : callArgs (.alloc 999:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_58_80_1
example : callArgs (.alloc 999:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_59_80_0
example : callArgs (.storeConsts 0 0 (some 999):HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_59_80_1
example : callArgs (.storeConsts 0 0 (some 999):HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_60_80_0
example : callArgs (.raise 1:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_60_80_1
example : callArgs (.raise 1:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_61_80_0
example : callArgs (.ret 1:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_61_80_1
example : callArgs (.ret 1:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_62_80_0
example : callArgs (.break 999:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_62_80_1
example : callArgs (.break 999:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_63_80_0
example : callArgs (.continue 999:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_63_80_1
example : callArgs (.continue 999:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_64_80_0
example : ¬ callArgs (.ffi (Flapjack.Basis.Pure.MlString.ofString "x") 1 2 3 4 5:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_64_80_1
example : ¬ callArgs (.ffi (Flapjack.Basis.Pure.MlString.ofString "x") 1 2 3 4 5:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_65_80_0
example : callArgs (.tick:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_65_80_1
example : callArgs (.tick:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_66_80_0
example : callArgs (.locValue 1 999 999:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_66_80_1
example : callArgs (.locValue 1 999 999:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_67_80_0
example : ¬ callArgs (.install 1 2 3 4 5:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_67_80_1
example : ¬ callArgs (.install 1 2 3 4 5:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_68_80_0
example : callArgs (.shMemOp .load16 1 (.addr 2 255):HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_68_80_1
example : callArgs (.shMemOp .load16 1 (.addr 2 255):HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_69_80_0
example : callArgs (.codeBufferWrite 1 2:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_69_80_1
example : callArgs (.codeBufferWrite 1 2:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_70_80_0
example : callArgs (.dataBufferWrite 1 2:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_70_80_1
example : callArgs (.dataBufferWrite 1 2:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_71_80_0
example : callArgs (.rawCall 999:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_71_80_1
example : callArgs (.rawCall 999:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_72_80_0
example : callArgs (.stackAlloc 999:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_72_80_1
example : callArgs (.stackAlloc 999:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_73_80_0
example : callArgs (.stackFree 999:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_73_80_1
example : callArgs (.stackFree 999:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_74_80_0
example : callArgs (.stackStore 1 999:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_74_80_1
example : callArgs (.stackStore 1 999:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_75_80_0
example : callArgs (.stackStore 999 1:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_75_80_1
example : callArgs (.stackStore 999 1:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_76_80_0
example : callArgs (.stackLoad 1 999:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_76_80_1
example : callArgs (.stackLoad 1 999:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_77_80_0
example : callArgs (.stackLoad 999 1:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_77_80_1
example : callArgs (.stackLoad 999 1:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_78_80_0
example : callArgs (.stackStoreAny 1 2:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_78_80_1
example : callArgs (.stackStoreAny 1 2:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_79_80_0
example : callArgs (.stackLoadAny 1 2:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_79_80_1
example : callArgs (.stackLoadAny 1 2:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_80_80_0
example : callArgs (.stackGetSize 1:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_80_80_1
example : callArgs (.stackGetSize 1:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_81_80_0
example : callArgs (.stackSetSize 1:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_81_80_1
example : callArgs (.stackSetSize 1:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_82_80_0
example : callArgs (.bitmapLoad 1 2:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_82_80_1
example : callArgs (.bitmapLoad 1 2:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_pred_prog_83_80_0
example : callArgs (.halt 1:HolProg 80) 1 2 3 4 0 := by
  simp [callArgs]

-- rca_pred_prog_83_80_1
example : ¬ callArgs (.halt 1:HolProg 80) 7 8 9 10 11 := by
  simp [callArgs]

-- rca_1_0_0_move_good
example : callArgs (width := 1) (stackMoveNative 0 1180591620717411303425 3 1 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_1_0_0_move_bad
example : callArgs (width := 1) (stackMoveNative 0 1180591620717411303425 3 2 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_1_0_0_aux
example : callArgs (width := 1) (copyRetAuxNative 0 1180591620717411303425 0) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative]

-- rca_1_0_0_ret_0_0_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_1_0_0_ret_0_0_1
example : callArgs (width := 1) (copyRetNative (width := 1) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_1_0_0_ret_0_1_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_1_0_0_ret_0_1_1
example : callArgs (width := 1) (copyRetNative (width := 1) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_1_0_0_ret_1_0_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_1_0_0_ret_1_0_1
example : callArgs (width := 1) (copyRetNative (width := 1) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_1_0_0_ret_1_1_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_1_0_0_ret_1_1_1
example : callArgs (width := 1) (copyRetNative (width := 1) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_1_0_4_move_good
example : callArgs (width := 1) (stackMoveNative 0 1180591620717411303425 3 5 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_1_0_4_move_bad
example : callArgs (width := 1) (stackMoveNative 0 1180591620717411303425 3 6 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_1_0_4_aux
example : callArgs (width := 1) (copyRetAuxNative 4 1180591620717411303425 0) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative]

-- rca_1_0_4_ret_0_0_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_1_0_4_ret_0_0_1
example : callArgs (width := 1) (copyRetNative (width := 1) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_1_0_4_ret_0_1_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_1_0_4_ret_0_1_1
example : callArgs (width := 1) (copyRetNative (width := 1) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_1_0_4_ret_1_0_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_1_0_4_ret_1_0_1
example : callArgs (width := 1) (copyRetNative (width := 1) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_1_0_4_ret_1_1_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_1_0_4_ret_1_1_1
example : callArgs (width := 1) (copyRetNative (width := 1) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_1_1_0_move_good
example : callArgs (width := 1) (stackMoveNative 1 1180591620717411303425 3 1 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_1_1_0_move_bad
example : callArgs (width := 1) (stackMoveNative 1 1180591620717411303425 3 2 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_1_1_0_aux
example : callArgs (width := 1) (copyRetAuxNative 0 1180591620717411303425 1) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_1_1_0_ret_0_0_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) false false (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_1_1_0_ret_0_0_1
example : callArgs (width := 1) (copyRetNative (width := 1) false false (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_1_1_0_ret_0_1_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) false true (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_1_1_0_ret_0_1_1
example : callArgs (width := 1) (copyRetNative (width := 1) false true (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_1_1_0_ret_1_0_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) true false (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_1_1_0_ret_1_0_1
example : callArgs (width := 1) (copyRetNative (width := 1) true false (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_1_1_0_ret_1_1_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) true true (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_1_1_0_ret_1_1_1
example : callArgs (width := 1) (copyRetNative (width := 1) true true (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_1_1_4_move_good
example : callArgs (width := 1) (stackMoveNative 1 1180591620717411303425 3 5 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_1_1_4_move_bad
example : callArgs (width := 1) (stackMoveNative 1 1180591620717411303425 3 6 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_1_1_4_aux
example : callArgs (width := 1) (copyRetAuxNative 4 1180591620717411303425 1) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_1_1_4_ret_0_0_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) false false (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_1_1_4_ret_0_0_1
example : callArgs (width := 1) (copyRetNative (width := 1) false false (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_1_1_4_ret_0_1_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) false true (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_1_1_4_ret_0_1_1
example : callArgs (width := 1) (copyRetNative (width := 1) false true (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_1_1_4_ret_1_0_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) true false (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_1_1_4_ret_1_0_1
example : callArgs (width := 1) (copyRetNative (width := 1) true false (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_1_1_4_ret_1_1_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) true true (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_1_1_4_ret_1_1_1
example : callArgs (width := 1) (copyRetNative (width := 1) true true (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_1_4_0_move_good
example : callArgs (width := 1) (stackMoveNative 4 1180591620717411303425 3 1 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_1_4_0_move_bad
example : callArgs (width := 1) (stackMoveNative 4 1180591620717411303425 3 2 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_1_4_0_aux
example : callArgs (width := 1) (copyRetAuxNative 0 1180591620717411303425 4) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_1_4_0_ret_0_0_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_1_4_0_ret_0_0_1
example : callArgs (width := 1) (copyRetNative (width := 1) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_1_4_0_ret_0_1_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_1_4_0_ret_0_1_1
example : callArgs (width := 1) (copyRetNative (width := 1) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_1_4_0_ret_1_0_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_1_4_0_ret_1_0_1
example : callArgs (width := 1) (copyRetNative (width := 1) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_1_4_0_ret_1_1_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_1_4_0_ret_1_1_1
example : callArgs (width := 1) (copyRetNative (width := 1) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_1_4_4_move_good
example : callArgs (width := 1) (stackMoveNative 4 1180591620717411303425 3 5 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_1_4_4_move_bad
example : callArgs (width := 1) (stackMoveNative 4 1180591620717411303425 3 6 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_1_4_4_aux
example : callArgs (width := 1) (copyRetAuxNative 4 1180591620717411303425 4) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_1_4_4_ret_0_0_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_1_4_4_ret_0_0_1
example : callArgs (width := 1) (copyRetNative (width := 1) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_1_4_4_ret_0_1_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_1_4_4_ret_0_1_1
example : callArgs (width := 1) (copyRetNative (width := 1) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_1_4_4_ret_1_0_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_1_4_4_ret_1_0_1
example : callArgs (width := 1) (copyRetNative (width := 1) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_1_4_4_ret_1_1_0
example : ¬ callArgs (width := 1) (copyRetNative (width := 1) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_1_4_4_ret_1_1_1
example : callArgs (width := 1) (copyRetNative (width := 1) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_2_0_0_move_good
example : callArgs (width := 2) (stackMoveNative 0 1180591620717411303425 3 1 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_2_0_0_move_bad
example : callArgs (width := 2) (stackMoveNative 0 1180591620717411303425 3 2 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_2_0_0_aux
example : callArgs (width := 2) (copyRetAuxNative 0 1180591620717411303425 0) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative]

-- rca_2_0_0_ret_0_0_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_2_0_0_ret_0_0_1
example : callArgs (width := 2) (copyRetNative (width := 2) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_2_0_0_ret_0_1_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_2_0_0_ret_0_1_1
example : callArgs (width := 2) (copyRetNative (width := 2) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_2_0_0_ret_1_0_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_2_0_0_ret_1_0_1
example : callArgs (width := 2) (copyRetNative (width := 2) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_2_0_0_ret_1_1_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_2_0_0_ret_1_1_1
example : callArgs (width := 2) (copyRetNative (width := 2) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_2_0_4_move_good
example : callArgs (width := 2) (stackMoveNative 0 1180591620717411303425 3 5 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_2_0_4_move_bad
example : callArgs (width := 2) (stackMoveNative 0 1180591620717411303425 3 6 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_2_0_4_aux
example : callArgs (width := 2) (copyRetAuxNative 4 1180591620717411303425 0) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative]

-- rca_2_0_4_ret_0_0_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_2_0_4_ret_0_0_1
example : callArgs (width := 2) (copyRetNative (width := 2) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_2_0_4_ret_0_1_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_2_0_4_ret_0_1_1
example : callArgs (width := 2) (copyRetNative (width := 2) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_2_0_4_ret_1_0_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_2_0_4_ret_1_0_1
example : callArgs (width := 2) (copyRetNative (width := 2) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_2_0_4_ret_1_1_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_2_0_4_ret_1_1_1
example : callArgs (width := 2) (copyRetNative (width := 2) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_2_1_0_move_good
example : callArgs (width := 2) (stackMoveNative 1 1180591620717411303425 3 1 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_2_1_0_move_bad
example : callArgs (width := 2) (stackMoveNative 1 1180591620717411303425 3 2 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_2_1_0_aux
example : callArgs (width := 2) (copyRetAuxNative 0 1180591620717411303425 1) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_2_1_0_ret_0_0_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) false false (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_2_1_0_ret_0_0_1
example : callArgs (width := 2) (copyRetNative (width := 2) false false (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_2_1_0_ret_0_1_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) false true (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_2_1_0_ret_0_1_1
example : callArgs (width := 2) (copyRetNative (width := 2) false true (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_2_1_0_ret_1_0_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) true false (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_2_1_0_ret_1_0_1
example : callArgs (width := 2) (copyRetNative (width := 2) true false (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_2_1_0_ret_1_1_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) true true (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_2_1_0_ret_1_1_1
example : callArgs (width := 2) (copyRetNative (width := 2) true true (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_2_1_4_move_good
example : callArgs (width := 2) (stackMoveNative 1 1180591620717411303425 3 5 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_2_1_4_move_bad
example : callArgs (width := 2) (stackMoveNative 1 1180591620717411303425 3 6 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_2_1_4_aux
example : callArgs (width := 2) (copyRetAuxNative 4 1180591620717411303425 1) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_2_1_4_ret_0_0_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) false false (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_2_1_4_ret_0_0_1
example : callArgs (width := 2) (copyRetNative (width := 2) false false (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_2_1_4_ret_0_1_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) false true (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_2_1_4_ret_0_1_1
example : callArgs (width := 2) (copyRetNative (width := 2) false true (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_2_1_4_ret_1_0_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) true false (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_2_1_4_ret_1_0_1
example : callArgs (width := 2) (copyRetNative (width := 2) true false (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_2_1_4_ret_1_1_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) true true (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_2_1_4_ret_1_1_1
example : callArgs (width := 2) (copyRetNative (width := 2) true true (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_2_4_0_move_good
example : callArgs (width := 2) (stackMoveNative 4 1180591620717411303425 3 1 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_2_4_0_move_bad
example : callArgs (width := 2) (stackMoveNative 4 1180591620717411303425 3 2 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_2_4_0_aux
example : callArgs (width := 2) (copyRetAuxNative 0 1180591620717411303425 4) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_2_4_0_ret_0_0_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_2_4_0_ret_0_0_1
example : callArgs (width := 2) (copyRetNative (width := 2) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_2_4_0_ret_0_1_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_2_4_0_ret_0_1_1
example : callArgs (width := 2) (copyRetNative (width := 2) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_2_4_0_ret_1_0_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_2_4_0_ret_1_0_1
example : callArgs (width := 2) (copyRetNative (width := 2) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_2_4_0_ret_1_1_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_2_4_0_ret_1_1_1
example : callArgs (width := 2) (copyRetNative (width := 2) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_2_4_4_move_good
example : callArgs (width := 2) (stackMoveNative 4 1180591620717411303425 3 5 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_2_4_4_move_bad
example : callArgs (width := 2) (stackMoveNative 4 1180591620717411303425 3 6 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_2_4_4_aux
example : callArgs (width := 2) (copyRetAuxNative 4 1180591620717411303425 4) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_2_4_4_ret_0_0_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_2_4_4_ret_0_0_1
example : callArgs (width := 2) (copyRetNative (width := 2) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_2_4_4_ret_0_1_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_2_4_4_ret_0_1_1
example : callArgs (width := 2) (copyRetNative (width := 2) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_2_4_4_ret_1_0_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_2_4_4_ret_1_0_1
example : callArgs (width := 2) (copyRetNative (width := 2) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_2_4_4_ret_1_1_0
example : ¬ callArgs (width := 2) (copyRetNative (width := 2) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_2_4_4_ret_1_1_1
example : callArgs (width := 2) (copyRetNative (width := 2) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_8_0_0_move_good
example : callArgs (width := 8) (stackMoveNative 0 1180591620717411303425 3 1 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_8_0_0_move_bad
example : callArgs (width := 8) (stackMoveNative 0 1180591620717411303425 3 2 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_8_0_0_aux
example : callArgs (width := 8) (copyRetAuxNative 0 1180591620717411303425 0) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative]

-- rca_8_0_0_ret_0_0_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_8_0_0_ret_0_0_1
example : callArgs (width := 8) (copyRetNative (width := 8) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_8_0_0_ret_0_1_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_8_0_0_ret_0_1_1
example : callArgs (width := 8) (copyRetNative (width := 8) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_8_0_0_ret_1_0_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_8_0_0_ret_1_0_1
example : callArgs (width := 8) (copyRetNative (width := 8) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_8_0_0_ret_1_1_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_8_0_0_ret_1_1_1
example : callArgs (width := 8) (copyRetNative (width := 8) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_8_0_4_move_good
example : callArgs (width := 8) (stackMoveNative 0 1180591620717411303425 3 5 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_8_0_4_move_bad
example : callArgs (width := 8) (stackMoveNative 0 1180591620717411303425 3 6 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_8_0_4_aux
example : callArgs (width := 8) (copyRetAuxNative 4 1180591620717411303425 0) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative]

-- rca_8_0_4_ret_0_0_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_8_0_4_ret_0_0_1
example : callArgs (width := 8) (copyRetNative (width := 8) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_8_0_4_ret_0_1_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_8_0_4_ret_0_1_1
example : callArgs (width := 8) (copyRetNative (width := 8) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_8_0_4_ret_1_0_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_8_0_4_ret_1_0_1
example : callArgs (width := 8) (copyRetNative (width := 8) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_8_0_4_ret_1_1_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_8_0_4_ret_1_1_1
example : callArgs (width := 8) (copyRetNative (width := 8) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_8_1_0_move_good
example : callArgs (width := 8) (stackMoveNative 1 1180591620717411303425 3 1 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_8_1_0_move_bad
example : callArgs (width := 8) (stackMoveNative 1 1180591620717411303425 3 2 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_8_1_0_aux
example : callArgs (width := 8) (copyRetAuxNative 0 1180591620717411303425 1) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_8_1_0_ret_0_0_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) false false (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_8_1_0_ret_0_0_1
example : callArgs (width := 8) (copyRetNative (width := 8) false false (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_8_1_0_ret_0_1_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) false true (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_8_1_0_ret_0_1_1
example : callArgs (width := 8) (copyRetNative (width := 8) false true (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_8_1_0_ret_1_0_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) true false (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_8_1_0_ret_1_0_1
example : callArgs (width := 8) (copyRetNative (width := 8) true false (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_8_1_0_ret_1_1_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) true true (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_8_1_0_ret_1_1_1
example : callArgs (width := 8) (copyRetNative (width := 8) true true (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_8_1_4_move_good
example : callArgs (width := 8) (stackMoveNative 1 1180591620717411303425 3 5 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_8_1_4_move_bad
example : callArgs (width := 8) (stackMoveNative 1 1180591620717411303425 3 6 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_8_1_4_aux
example : callArgs (width := 8) (copyRetAuxNative 4 1180591620717411303425 1) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_8_1_4_ret_0_0_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) false false (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_8_1_4_ret_0_0_1
example : callArgs (width := 8) (copyRetNative (width := 8) false false (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_8_1_4_ret_0_1_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) false true (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_8_1_4_ret_0_1_1
example : callArgs (width := 8) (copyRetNative (width := 8) false true (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_8_1_4_ret_1_0_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) true false (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_8_1_4_ret_1_0_1
example : callArgs (width := 8) (copyRetNative (width := 8) true false (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_8_1_4_ret_1_1_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) true true (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_8_1_4_ret_1_1_1
example : callArgs (width := 8) (copyRetNative (width := 8) true true (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_8_4_0_move_good
example : callArgs (width := 8) (stackMoveNative 4 1180591620717411303425 3 1 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_8_4_0_move_bad
example : callArgs (width := 8) (stackMoveNative 4 1180591620717411303425 3 2 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_8_4_0_aux
example : callArgs (width := 8) (copyRetAuxNative 0 1180591620717411303425 4) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_8_4_0_ret_0_0_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_8_4_0_ret_0_0_1
example : callArgs (width := 8) (copyRetNative (width := 8) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_8_4_0_ret_0_1_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_8_4_0_ret_0_1_1
example : callArgs (width := 8) (copyRetNative (width := 8) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_8_4_0_ret_1_0_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_8_4_0_ret_1_0_1
example : callArgs (width := 8) (copyRetNative (width := 8) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_8_4_0_ret_1_1_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_8_4_0_ret_1_1_1
example : callArgs (width := 8) (copyRetNative (width := 8) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_8_4_4_move_good
example : callArgs (width := 8) (stackMoveNative 4 1180591620717411303425 3 5 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_8_4_4_move_bad
example : callArgs (width := 8) (stackMoveNative 4 1180591620717411303425 3 6 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_8_4_4_aux
example : callArgs (width := 8) (copyRetAuxNative 4 1180591620717411303425 4) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_8_4_4_ret_0_0_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_8_4_4_ret_0_0_1
example : callArgs (width := 8) (copyRetNative (width := 8) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_8_4_4_ret_0_1_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_8_4_4_ret_0_1_1
example : callArgs (width := 8) (copyRetNative (width := 8) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_8_4_4_ret_1_0_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_8_4_4_ret_1_0_1
example : callArgs (width := 8) (copyRetNative (width := 8) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_8_4_4_ret_1_1_0
example : ¬ callArgs (width := 8) (copyRetNative (width := 8) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_8_4_4_ret_1_1_1
example : callArgs (width := 8) (copyRetNative (width := 8) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_64_0_0_move_good
example : callArgs (width := 64) (stackMoveNative 0 1180591620717411303425 3 1 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_64_0_0_move_bad
example : callArgs (width := 64) (stackMoveNative 0 1180591620717411303425 3 2 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_64_0_0_aux
example : callArgs (width := 64) (copyRetAuxNative 0 1180591620717411303425 0) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative]

-- rca_64_0_0_ret_0_0_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_64_0_0_ret_0_0_1
example : callArgs (width := 64) (copyRetNative (width := 64) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_64_0_0_ret_0_1_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_64_0_0_ret_0_1_1
example : callArgs (width := 64) (copyRetNative (width := 64) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_64_0_0_ret_1_0_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_64_0_0_ret_1_0_1
example : callArgs (width := 64) (copyRetNative (width := 64) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_64_0_0_ret_1_1_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_64_0_0_ret_1_1_1
example : callArgs (width := 64) (copyRetNative (width := 64) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_64_0_4_move_good
example : callArgs (width := 64) (stackMoveNative 0 1180591620717411303425 3 5 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_64_0_4_move_bad
example : callArgs (width := 64) (stackMoveNative 0 1180591620717411303425 3 6 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_64_0_4_aux
example : callArgs (width := 64) (copyRetAuxNative 4 1180591620717411303425 0) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative]

-- rca_64_0_4_ret_0_0_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_64_0_4_ret_0_0_1
example : callArgs (width := 64) (copyRetNative (width := 64) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_64_0_4_ret_0_1_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_64_0_4_ret_0_1_1
example : callArgs (width := 64) (copyRetNative (width := 64) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_64_0_4_ret_1_0_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_64_0_4_ret_1_0_1
example : callArgs (width := 64) (copyRetNative (width := 64) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_64_0_4_ret_1_1_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_64_0_4_ret_1_1_1
example : callArgs (width := 64) (copyRetNative (width := 64) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_64_1_0_move_good
example : callArgs (width := 64) (stackMoveNative 1 1180591620717411303425 3 1 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_64_1_0_move_bad
example : callArgs (width := 64) (stackMoveNative 1 1180591620717411303425 3 2 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_64_1_0_aux
example : callArgs (width := 64) (copyRetAuxNative 0 1180591620717411303425 1) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_64_1_0_ret_0_0_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) false false (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_64_1_0_ret_0_0_1
example : callArgs (width := 64) (copyRetNative (width := 64) false false (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_64_1_0_ret_0_1_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) false true (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_64_1_0_ret_0_1_1
example : callArgs (width := 64) (copyRetNative (width := 64) false true (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_64_1_0_ret_1_0_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) true false (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_64_1_0_ret_1_0_1
example : callArgs (width := 64) (copyRetNative (width := 64) true false (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_64_1_0_ret_1_1_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) true true (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_64_1_0_ret_1_1_1
example : callArgs (width := 64) (copyRetNative (width := 64) true true (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_64_1_4_move_good
example : callArgs (width := 64) (stackMoveNative 1 1180591620717411303425 3 5 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_64_1_4_move_bad
example : callArgs (width := 64) (stackMoveNative 1 1180591620717411303425 3 6 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_64_1_4_aux
example : callArgs (width := 64) (copyRetAuxNative 4 1180591620717411303425 1) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_64_1_4_ret_0_0_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) false false (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_64_1_4_ret_0_0_1
example : callArgs (width := 64) (copyRetNative (width := 64) false false (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_64_1_4_ret_0_1_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) false true (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_64_1_4_ret_0_1_1
example : callArgs (width := 64) (copyRetNative (width := 64) false true (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_64_1_4_ret_1_0_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) true false (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_64_1_4_ret_1_0_1
example : callArgs (width := 64) (copyRetNative (width := 64) true false (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_64_1_4_ret_1_1_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) true true (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_64_1_4_ret_1_1_1
example : callArgs (width := 64) (copyRetNative (width := 64) true true (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_64_4_0_move_good
example : callArgs (width := 64) (stackMoveNative 4 1180591620717411303425 3 1 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_64_4_0_move_bad
example : callArgs (width := 64) (stackMoveNative 4 1180591620717411303425 3 2 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_64_4_0_aux
example : callArgs (width := 64) (copyRetAuxNative 0 1180591620717411303425 4) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_64_4_0_ret_0_0_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_64_4_0_ret_0_0_1
example : callArgs (width := 64) (copyRetNative (width := 64) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_64_4_0_ret_0_1_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_64_4_0_ret_0_1_1
example : callArgs (width := 64) (copyRetNative (width := 64) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_64_4_0_ret_1_0_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_64_4_0_ret_1_0_1
example : callArgs (width := 64) (copyRetNative (width := 64) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_64_4_0_ret_1_1_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_64_4_0_ret_1_1_1
example : callArgs (width := 64) (copyRetNative (width := 64) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_64_4_4_move_good
example : callArgs (width := 64) (stackMoveNative 4 1180591620717411303425 3 5 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_64_4_4_move_bad
example : callArgs (width := 64) (stackMoveNative 4 1180591620717411303425 3 6 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_64_4_4_aux
example : callArgs (width := 64) (copyRetAuxNative 4 1180591620717411303425 4) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_64_4_4_ret_0_0_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_64_4_4_ret_0_0_1
example : callArgs (width := 64) (copyRetNative (width := 64) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_64_4_4_ret_0_1_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_64_4_4_ret_0_1_1
example : callArgs (width := 64) (copyRetNative (width := 64) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_64_4_4_ret_1_0_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_64_4_4_ret_1_0_1
example : callArgs (width := 64) (copyRetNative (width := 64) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_64_4_4_ret_1_1_0
example : ¬ callArgs (width := 64) (copyRetNative (width := 64) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_64_4_4_ret_1_1_1
example : callArgs (width := 64) (copyRetNative (width := 64) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_80_0_0_move_good
example : callArgs (width := 80) (stackMoveNative 0 1180591620717411303425 3 1 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_80_0_0_move_bad
example : callArgs (width := 80) (stackMoveNative 0 1180591620717411303425 3 2 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_80_0_0_aux
example : callArgs (width := 80) (copyRetAuxNative 0 1180591620717411303425 0) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative]

-- rca_80_0_0_ret_0_0_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_80_0_0_ret_0_0_1
example : callArgs (width := 80) (copyRetNative (width := 80) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_80_0_0_ret_0_1_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_80_0_0_ret_0_1_1
example : callArgs (width := 80) (copyRetNative (width := 80) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_80_0_0_ret_1_0_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_80_0_0_ret_1_0_1
example : callArgs (width := 80) (copyRetNative (width := 80) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_80_0_0_ret_1_1_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_80_0_0_ret_1_1_1
example : callArgs (width := 80) (copyRetNative (width := 80) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_80_0_4_move_good
example : callArgs (width := 80) (stackMoveNative 0 1180591620717411303425 3 5 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_80_0_4_move_bad
example : callArgs (width := 80) (stackMoveNative 0 1180591620717411303425 3 6 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_80_0_4_aux
example : callArgs (width := 80) (copyRetAuxNative 4 1180591620717411303425 0) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative]

-- rca_80_0_4_ret_0_0_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_80_0_4_ret_0_0_1
example : callArgs (width := 80) (copyRetNative (width := 80) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_80_0_4_ret_0_1_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_80_0_4_ret_0_1_1
example : callArgs (width := 80) (copyRetNative (width := 80) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_80_0_4_ret_1_0_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_80_0_4_ret_1_0_1
example : callArgs (width := 80) (copyRetNative (width := 80) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_80_0_4_ret_1_1_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_80_0_4_ret_1_1_1
example : callArgs (width := 80) (copyRetNative (width := 80) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_80_1_0_move_good
example : callArgs (width := 80) (stackMoveNative 1 1180591620717411303425 3 1 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_80_1_0_move_bad
example : callArgs (width := 80) (stackMoveNative 1 1180591620717411303425 3 2 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_80_1_0_aux
example : callArgs (width := 80) (copyRetAuxNative 0 1180591620717411303425 1) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_80_1_0_ret_0_0_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) false false (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_80_1_0_ret_0_0_1
example : callArgs (width := 80) (copyRetNative (width := 80) false false (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_80_1_0_ret_0_1_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) false true (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_80_1_0_ret_0_1_1
example : callArgs (width := 80) (copyRetNative (width := 80) false true (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_80_1_0_ret_1_0_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) true false (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_80_1_0_ret_1_0_1
example : callArgs (width := 80) (copyRetNative (width := 80) true false (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_80_1_0_ret_1_1_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) true true (0,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_80_1_0_ret_1_1_1
example : callArgs (width := 80) (copyRetNative (width := 80) true true (0,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_80_1_4_move_good
example : callArgs (width := 80) (stackMoveNative 1 1180591620717411303425 3 5 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_80_1_4_move_bad
example : callArgs (width := 80) (stackMoveNative 1 1180591620717411303425 3 6 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_80_1_4_aux
example : callArgs (width := 80) (copyRetAuxNative 4 1180591620717411303425 1) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_80_1_4_ret_0_0_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) false false (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_80_1_4_ret_0_0_1
example : callArgs (width := 80) (copyRetNative (width := 80) false false (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_80_1_4_ret_0_1_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) false true (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_80_1_4_ret_0_1_1
example : callArgs (width := 80) (copyRetNative (width := 80) false true (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_80_1_4_ret_1_0_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) true false (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_80_1_4_ret_1_0_1
example : callArgs (width := 80) (copyRetNative (width := 80) true false (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_80_1_4_ret_1_1_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) true true (4,1180591620717411303425,true) [2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_80_1_4_ret_1_1_1
example : callArgs (width := 80) (copyRetNative (width := 80) true true (4,1180591620717411303425,true) [2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet]

-- rca_80_4_0_move_good
example : callArgs (width := 80) (stackMoveNative 4 1180591620717411303425 3 1 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_80_4_0_move_bad
example : callArgs (width := 80) (stackMoveNative 4 1180591620717411303425 3 2 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_80_4_0_aux
example : callArgs (width := 80) (copyRetAuxNative 0 1180591620717411303425 4) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_80_4_0_ret_0_0_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_80_4_0_ret_0_0_1
example : callArgs (width := 80) (copyRetNative (width := 80) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_80_4_0_ret_0_1_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_80_4_0_ret_0_1_1
example : callArgs (width := 80) (copyRetNative (width := 80) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_80_4_0_ret_1_0_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_80_4_0_ret_1_0_1
example : callArgs (width := 80) (copyRetNative (width := 80) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_80_4_0_ret_1_1_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_80_4_0_ret_1_1_1
example : callArgs (width := 80) (copyRetNative (width := 80) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_80_4_4_move_good
example : callArgs (width := 80) (stackMoveNative 4 1180591620717411303425 3 5 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_80_4_4_move_bad
example : callArgs (width := 80) (stackMoveNative 4 1180591620717411303425 3 6 (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, stackMoveNative]

-- rca_80_4_4_aux
example : callArgs (width := 80) (copyRetAuxNative 4 1180591620717411303425 4) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, listSeq]

-- rca_80_4_4_ret_0_0_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_80_4_4_ret_0_0_1
example : callArgs (width := 80) (copyRetNative (width := 80) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_80_4_4_ret_0_1_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_80_4_4_ret_0_1_1
example : callArgs (width := 80) (copyRetNative (width := 80) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_80_4_4_ret_1_0_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_80_4_4_ret_1_0_1
example : callArgs (width := 80) (copyRetNative (width := 80) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, listSeq]

-- rca_80_4_4_ret_1_1_0
example : ¬ callArgs (width := 80) (copyRetNative (width := 80) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

-- rca_80_4_4_ret_1_1_1
example : callArgs (width := 80) (copyRetNative (width := 80) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 1)) 1 2 3 4 0 := by
  simp [callArgs, copyRetAuxNative, copyRetNative, seqStackFreeNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq]

#print axioms Flapjack.Compiler.Backend.StackProps.callArgs
#print axioms Flapjack.WordToStackProofs.stackMoveCallArgs
#print axioms Flapjack.WordToStackProofs.copyRetAuxCallArgs
#print axioms Flapjack.WordToStackProofs.copyRetCallArgs
end Flapjack.Test.WordToStackReturnCallArgsParity

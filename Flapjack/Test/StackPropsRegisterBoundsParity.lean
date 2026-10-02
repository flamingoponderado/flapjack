import Flapjack.Compiler.Backend.StackProps.RegisterBounds
open Flapjack Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

-- rb_exp_0_3_1
example : ¬ regBoundExp (.var 3:WordLangExpHOL (BitVec 1)) 3 := by simp [regBoundExp]

-- rb_exp_0_4_1
example : regBoundExp (.var 3:WordLangExpHOL (BitVec 1)) 4 := by simp [regBoundExp]

-- rb_exp_1_0_1
example : regBoundExp (.const 255:WordLangExpHOL (BitVec 1)) 0 := by simp [regBoundExp]

-- rb_exp_1_100_1
example : regBoundExp (.const 255:WordLangExpHOL (BitVec 1)) 100 := by simp [regBoundExp]

-- rb_exp_2_0_1
example : ¬ regBoundExp (.lookup .currHeap:WordLangExpHOL (BitVec 1)) 0 := by simp [regBoundExp]

-- rb_exp_2_100_1
example : ¬ regBoundExp (.lookup .currHeap:WordLangExpHOL (BitVec 1)) 100 := by simp [regBoundExp]

-- rb_exp_3_3_1
example : ¬ regBoundExp (.load (.var 3):WordLangExpHOL (BitVec 1)) 3 := by simp [regBoundExp]

-- rb_exp_3_4_1
example : regBoundExp (.load (.var 3):WordLangExpHOL (BitVec 1)) 4 := by simp [regBoundExp]

-- rb_exp_4_5_1
example : ¬ regBoundExp (.shift .lsl (.var 3) (.var 5):WordLangExpHOL (BitVec 1)) 5 := by simp [regBoundExp]

-- rb_exp_4_6_1
example : regBoundExp (.shift .lsl (.var 3) (.var 5):WordLangExpHOL (BitVec 1)) 6 := by simp [regBoundExp]

-- rb_exp_5_0_1
example : regBoundExp (.op .add []:WordLangExpHOL (BitVec 1)) 0 := by simp [regBoundExp]

-- rb_exp_5_100_1
example : regBoundExp (.op .add []:WordLangExpHOL (BitVec 1)) 100 := by simp [regBoundExp]

-- rb_exp_6_9_1
example : ¬ regBoundExp (.op .add [.var 1,.load (.var 9)]:WordLangExpHOL (BitVec 1)) 9 := by simp [regBoundExp]

-- rb_exp_6_10_1
example : regBoundExp (.op .add [.var 1,.load (.var 9)]:WordLangExpHOL (BitVec 1)) 10 := by simp [regBoundExp]

-- rb_exp_7_0_1
example : ¬ regBoundExp (.op .xor [.lookup .currHeap,.const 255]:WordLangExpHOL (BitVec 1)) 0 := by simp [regBoundExp]

-- rb_exp_7_100_1
example : ¬ regBoundExp (.op .xor [.lookup .currHeap,.const 255]:WordLangExpHOL (BitVec 1)) 100 := by simp [regBoundExp]

-- rb_inst_8_0_1
example : regBoundInst (.skip:HolInst 1) 0 := by simp [regBoundInst]

-- rb_inst_8_100_1
example : regBoundInst (.skip:HolInst 1) 100 := by simp [regBoundInst]

-- rb_inst_9_1_1
example : ¬ regBoundInst (.const 1 255:HolInst 1) 1 := by simp [regBoundInst]

-- rb_inst_9_2_1
example : regBoundInst (.const 1 255:HolInst 1) 2 := by simp [regBoundInst]

-- rb_inst_10_2_1
example : ¬ regBoundInst (.mem .load 1 (.addr 2 255):HolInst 1) 2 := by simp [regBoundInst]

-- rb_inst_10_3_1
example : regBoundInst (.mem .load 1 (.addr 2 255):HolInst 1) 3 := by simp [regBoundInst]

-- rb_inst_11_2_1
example : ¬ regBoundInst (.mem .load8 1 (.addr 2 255):HolInst 1) 2 := by simp [regBoundInst]

-- rb_inst_11_3_1
example : regBoundInst (.mem .load8 1 (.addr 2 255):HolInst 1) 3 := by simp [regBoundInst]

-- rb_inst_12_2_1
example : ¬ regBoundInst (.mem .load16 1 (.addr 2 255):HolInst 1) 2 := by simp [regBoundInst]

-- rb_inst_12_3_1
example : regBoundInst (.mem .load16 1 (.addr 2 255):HolInst 1) 3 := by simp [regBoundInst]

-- rb_inst_13_2_1
example : ¬ regBoundInst (.mem .load32 1 (.addr 2 255):HolInst 1) 2 := by simp [regBoundInst]

-- rb_inst_13_3_1
example : regBoundInst (.mem .load32 1 (.addr 2 255):HolInst 1) 3 := by simp [regBoundInst]

-- rb_inst_14_2_1
example : ¬ regBoundInst (.mem .store 1 (.addr 2 255):HolInst 1) 2 := by simp [regBoundInst]

-- rb_inst_14_3_1
example : regBoundInst (.mem .store 1 (.addr 2 255):HolInst 1) 3 := by simp [regBoundInst]

-- rb_inst_15_2_1
example : ¬ regBoundInst (.mem .store8 1 (.addr 2 255):HolInst 1) 2 := by simp [regBoundInst]

-- rb_inst_15_3_1
example : regBoundInst (.mem .store8 1 (.addr 2 255):HolInst 1) 3 := by simp [regBoundInst]

-- rb_inst_16_2_1
example : ¬ regBoundInst (.mem .store16 1 (.addr 2 255):HolInst 1) 2 := by simp [regBoundInst]

-- rb_inst_16_3_1
example : regBoundInst (.mem .store16 1 (.addr 2 255):HolInst 1) 3 := by simp [regBoundInst]

-- rb_inst_17_2_1
example : ¬ regBoundInst (.mem .store32 1 (.addr 2 255):HolInst 1) 2 := by simp [regBoundInst]

-- rb_inst_17_3_1
example : regBoundInst (.mem .store32 1 (.addr 2 255):HolInst 1) 3 := by simp [regBoundInst]

-- rb_inst_18_3_1
example : ¬ regBoundInst (.arith (.binop .add 1 2 (.reg 3)):HolInst 1) 3 := by simp [regBoundInst]

-- rb_inst_18_4_1
example : regBoundInst (.arith (.binop .add 1 2 (.reg 3)):HolInst 1) 4 := by simp [regBoundInst]

-- rb_inst_19_2_1
example : ¬ regBoundInst (.arith (.binop .and 1 2 (.imm 255)):HolInst 1) 2 := by simp [regBoundInst]

-- rb_inst_19_3_1
example : regBoundInst (.arith (.binop .and 1 2 (.imm 255)):HolInst 1) 3 := by simp [regBoundInst]

-- rb_inst_20_3_1
example : ¬ regBoundInst (.arith (.shift .lsl 1 2 (.reg 3)):HolInst 1) 3 := by simp [regBoundInst]

-- rb_inst_20_4_1
example : regBoundInst (.arith (.shift .lsl 1 2 (.reg 3)):HolInst 1) 4 := by simp [regBoundInst]

-- rb_inst_21_2_1
example : ¬ regBoundInst (.arith (.shift .ror 1 2 (.imm 255)):HolInst 1) 2 := by simp [regBoundInst]

-- rb_inst_21_3_1
example : regBoundInst (.arith (.shift .ror 1 2 (.imm 255)):HolInst 1) 3 := by simp [regBoundInst]

-- rb_inst_22_3_1
example : ¬ regBoundInst (.arith (.div 1 2 3):HolInst 1) 3 := by simp [regBoundInst]

-- rb_inst_22_4_1
example : regBoundInst (.arith (.div 1 2 3):HolInst 1) 4 := by simp [regBoundInst]

-- rb_inst_23_4_1
example : ¬ regBoundInst (.arith (.longMul 1 2 3 4):HolInst 1) 4 := by simp [regBoundInst]

-- rb_inst_23_5_1
example : regBoundInst (.arith (.longMul 1 2 3 4):HolInst 1) 5 := by simp [regBoundInst]

-- rb_inst_24_5_1
example : ¬ regBoundInst (.arith (.longDiv 1 2 3 4 5):HolInst 1) 5 := by simp [regBoundInst]

-- rb_inst_24_6_1
example : regBoundInst (.arith (.longDiv 1 2 3 4 5):HolInst 1) 6 := by simp [regBoundInst]

-- rb_inst_25_4_1
example : ¬ regBoundInst (.arith (.addCarry 1 2 3 4):HolInst 1) 4 := by simp [regBoundInst]

-- rb_inst_25_5_1
example : regBoundInst (.arith (.addCarry 1 2 3 4):HolInst 1) 5 := by simp [regBoundInst]

-- rb_inst_26_4_1
example : ¬ regBoundInst (.arith (.addOverflow 1 2 3 4):HolInst 1) 4 := by simp [regBoundInst]

-- rb_inst_26_5_1
example : regBoundInst (.arith (.addOverflow 1 2 3 4):HolInst 1) 5 := by simp [regBoundInst]

-- rb_inst_27_4_1
example : ¬ regBoundInst (.arith (.subOverflow 1 2 3 4):HolInst 1) 4 := by simp [regBoundInst]

-- rb_inst_27_5_1
example : regBoundInst (.arith (.subOverflow 1 2 3 4):HolInst 1) 5 := by simp [regBoundInst]

-- rb_inst_28_1_1
example : ¬ regBoundInst (.fp (.fpLess 1 99 100):HolInst 1) 1 := by simp [regBoundInst]

-- rb_inst_28_2_1
example : regBoundInst (.fp (.fpLess 1 99 100):HolInst 1) 2 := by simp [regBoundInst]

-- rb_inst_29_1_1
example : ¬ regBoundInst (.fp (.fpLessEqual 1 99 100):HolInst 1) 1 := by simp [regBoundInst]

-- rb_inst_29_2_1
example : regBoundInst (.fp (.fpLessEqual 1 99 100):HolInst 1) 2 := by simp [regBoundInst]

-- rb_inst_30_1_1
example : ¬ regBoundInst (.fp (.fpEqual 1 99 100):HolInst 1) 1 := by simp [regBoundInst]

-- rb_inst_30_2_1
example : regBoundInst (.fp (.fpEqual 1 99 100):HolInst 1) 2 := by simp [regBoundInst]

-- rb_inst_31_0_1
example : regBoundInst (.fp (.fpAbs 100 100):HolInst 1) 0 := by simp [regBoundInst]

-- rb_inst_31_100_1
example : regBoundInst (.fp (.fpAbs 100 100):HolInst 1) 100 := by simp [regBoundInst]

-- rb_inst_32_0_1
example : regBoundInst (.fp (.fpNeg 100 100):HolInst 1) 0 := by simp [regBoundInst]

-- rb_inst_32_100_1
example : regBoundInst (.fp (.fpNeg 100 100):HolInst 1) 100 := by simp [regBoundInst]

-- rb_inst_33_0_1
example : regBoundInst (.fp (.fpSqrt 100 100):HolInst 1) 0 := by simp [regBoundInst]

-- rb_inst_33_100_1
example : regBoundInst (.fp (.fpSqrt 100 100):HolInst 1) 100 := by simp [regBoundInst]

-- rb_inst_34_0_1
example : regBoundInst (.fp (.fpAdd 100 100 100):HolInst 1) 0 := by simp [regBoundInst]

-- rb_inst_34_100_1
example : regBoundInst (.fp (.fpAdd 100 100 100):HolInst 1) 100 := by simp [regBoundInst]

-- rb_inst_35_0_1
example : regBoundInst (.fp (.fpSub 100 100 100):HolInst 1) 0 := by simp [regBoundInst]

-- rb_inst_35_100_1
example : regBoundInst (.fp (.fpSub 100 100 100):HolInst 1) 100 := by simp [regBoundInst]

-- rb_inst_36_0_1
example : regBoundInst (.fp (.fpMul 100 100 100):HolInst 1) 0 := by simp [regBoundInst]

-- rb_inst_36_100_1
example : regBoundInst (.fp (.fpMul 100 100 100):HolInst 1) 100 := by simp [regBoundInst]

-- rb_inst_37_0_1
example : regBoundInst (.fp (.fpDiv 100 100 100):HolInst 1) 0 := by simp [regBoundInst]

-- rb_inst_37_100_1
example : regBoundInst (.fp (.fpDiv 100 100 100):HolInst 1) 100 := by simp [regBoundInst]

-- rb_inst_38_0_1
example : regBoundInst (.fp (.fpFma 100 100 100):HolInst 1) 0 := by simp [regBoundInst]

-- rb_inst_38_100_1
example : regBoundInst (.fp (.fpFma 100 100 100):HolInst 1) 100 := by simp [regBoundInst]

-- rb_inst_39_0_1
example : regBoundInst (.fp (.fpMov 100 100):HolInst 1) 0 := by simp [regBoundInst]

-- rb_inst_39_100_1
example : regBoundInst (.fp (.fpMov 100 100):HolInst 1) 100 := by simp [regBoundInst]

-- rb_inst_40_0_1
example : regBoundInst (.fp (.fpToInt 100 100):HolInst 1) 0 := by simp [regBoundInst]

-- rb_inst_40_100_1
example : regBoundInst (.fp (.fpToInt 100 100):HolInst 1) 100 := by simp [regBoundInst]

-- rb_inst_41_0_1
example : regBoundInst (.fp (.fpFromInt 100 100):HolInst 1) 0 := by simp [regBoundInst]

-- rb_inst_41_100_1
example : regBoundInst (.fp (.fpFromInt 100 100):HolInst 1) 100 := by simp [regBoundInst]

-- rb_inst_42_2_1
example : ¬ regBoundInst (.fp (.fpMovToReg 1 2 100):HolInst 1) 2 := by simp [regBoundInst]

-- rb_inst_42_3_1
example : regBoundInst (.fp (.fpMovToReg 1 2 100):HolInst 1) 3 := by simp [regBoundInst]

-- rb_inst_43_2_1
example : ¬ regBoundInst (.fp (.fpMovFromReg 100 1 2):HolInst 1) 2 := by simp [regBoundInst]

-- rb_inst_43_3_1
example : regBoundInst (.fp (.fpMovFromReg 100 1 2):HolInst 1) 3 := by simp [regBoundInst]

-- rb_prog_44_0_1
example : regBound (.skip:HolProg 1) 0 := by simp [regBound]

-- rb_prog_44_100_1
example : regBound (.skip:HolProg 1) 100 := by simp [regBound]

-- rb_prog_45_1_1
example : ¬ regBound (.inst (.const 1 255):HolProg 1) 1 := by simp [regBound, regBoundInst]

-- rb_prog_45_2_1
example : regBound (.inst (.const 1 255):HolProg 1) 2 := by simp [regBound, regBoundInst]

-- rb_prog_46_1_1
example : ¬ regBound (.get 1 .currHeap:HolProg 1) 1 := by simp [regBound]

-- rb_prog_46_2_1
example : regBound (.get 1 .currHeap:HolProg 1) 2 := by simp [regBound]

-- rb_prog_47_1_1
example : ¬ regBound (.set .currHeap 1:HolProg 1) 1 := by simp [regBound]

-- rb_prog_47_2_1
example : regBound (.set .currHeap 1:HolProg 1) 2 := by simp [regBound]

-- rb_prog_48_0_1
example : ¬ regBound (.set .bitmapBase 1:HolProg 1) 0 := by simp [regBound]

-- rb_prog_48_100_1
example : ¬ regBound (.set .bitmapBase 1:HolProg 1) 100 := by simp [regBound]

-- rb_prog_49_2_1
example : ¬ regBound (.opCurrHeap .add 1 2:HolProg 1) 2 := by simp [regBound]

-- rb_prog_49_3_1
example : regBound (.opCurrHeap .add 1 2:HolProg 1) 3 := by simp [regBound]

-- rb_prog_50_0_1
example : regBound (.call none (.inl 999) (some (.halt 100,999,999)):HolProg 1) 0 := by simp [regBound]

-- rb_prog_50_100_1
example : regBound (.call none (.inl 999) (some (.halt 100,999,999)):HolProg 1) 100 := by simp [regBound]

-- rb_prog_51_2_1
example : ¬ regBound (.call none (.inr 2) none:HolProg 1) 2 := by simp [regBound]

-- rb_prog_51_3_1
example : regBound (.call none (.inr 2) none:HolProg 1) 3 := by simp [regBound]

-- rb_prog_52_3_1
example : ¬ regBound (.call (some (.halt 1,2,999,999)) (.inl 999) (some (.halt 3,999,999)):HolProg 1) 3 := by simp [regBound]

-- rb_prog_52_4_1
example : regBound (.call (some (.halt 1,2,999,999)) (.inl 999) (some (.halt 3,999,999)):HolProg 1) 4 := by simp [regBound]

-- rb_prog_53_2_1
example : ¬ regBound (.seq (.halt 1) (.halt 2):HolProg 1) 2 := by simp [regBound]

-- rb_prog_53_3_1
example : regBound (.seq (.halt 1) (.halt 2):HolProg 1) 3 := by simp [regBound]

-- rb_prog_54_3_1
example : ¬ regBound (.ite .equal 1 (.reg 2) .skip (.halt 3):HolProg 1) 3 := by simp [regBound]

-- rb_prog_54_4_1
example : regBound (.ite .equal 1 (.reg 2) .skip (.halt 3):HolProg 1) 4 := by simp [regBound]

-- rb_prog_55_1_1
example : ¬ regBound (.ite .equal 1 (.imm 255) .skip .skip:HolProg 1) 1 := by simp [regBound]

-- rb_prog_55_2_1
example : regBound (.ite .equal 1 (.imm 255) .skip .skip:HolProg 1) 2 := by simp [regBound]

-- rb_prog_56_2_1
example : ¬ regBound (.loop (.halt 2):HolProg 1) 2 := by simp [regBound]

-- rb_prog_56_3_1
example : regBound (.loop (.halt 2):HolProg 1) 3 := by simp [regBound]

-- rb_prog_57_2_1
example : ¬ regBound (.jumpLower 1 2 999:HolProg 1) 2 := by simp [regBound]

-- rb_prog_57_3_1
example : regBound (.jumpLower 1 2 999:HolProg 1) 3 := by simp [regBound]

-- rb_prog_58_0_1
example : regBound (.alloc 999:HolProg 1) 0 := by simp [regBound]

-- rb_prog_58_100_1
example : regBound (.alloc 999:HolProg 1) 100 := by simp [regBound]

-- rb_prog_59_3_1
example : ¬ regBound (.storeConsts 0 0 (some 999):HolProg 1) 3 := by simp [regBound]

-- rb_prog_59_4_1
example : regBound (.storeConsts 0 0 (some 999):HolProg 1) 4 := by simp [regBound]

-- rb_prog_60_1_1
example : ¬ regBound (.raise 1:HolProg 1) 1 := by simp [regBound]

-- rb_prog_60_2_1
example : regBound (.raise 1:HolProg 1) 2 := by simp [regBound]

-- rb_prog_61_1_1
example : ¬ regBound (.ret 1:HolProg 1) 1 := by simp [regBound]

-- rb_prog_61_2_1
example : regBound (.ret 1:HolProg 1) 2 := by simp [regBound]

-- rb_prog_62_0_1
example : regBound (.break 999:HolProg 1) 0 := by simp [regBound]

-- rb_prog_62_100_1
example : regBound (.break 999:HolProg 1) 100 := by simp [regBound]

-- rb_prog_63_0_1
example : regBound (.continue 999:HolProg 1) 0 := by simp [regBound]

-- rb_prog_63_100_1
example : regBound (.continue 999:HolProg 1) 100 := by simp [regBound]

-- rb_prog_64_5_1
example : ¬ regBound (.ffi (Flapjack.Basis.Pure.MlString.ofString "x") 1 2 3 4 5:HolProg 1) 5 := by simp [regBound]

-- rb_prog_64_6_1
example : regBound (.ffi (Flapjack.Basis.Pure.MlString.ofString "x") 1 2 3 4 5:HolProg 1) 6 := by simp [regBound]

-- rb_prog_65_0_1
example : regBound (.tick:HolProg 1) 0 := by simp [regBound]

-- rb_prog_65_100_1
example : regBound (.tick:HolProg 1) 100 := by simp [regBound]

-- rb_prog_66_1_1
example : ¬ regBound (.locValue 1 999 999:HolProg 1) 1 := by simp [regBound]

-- rb_prog_66_2_1
example : regBound (.locValue 1 999 999:HolProg 1) 2 := by simp [regBound]

-- rb_prog_67_5_1
example : ¬ regBound (.install 1 2 3 4 5:HolProg 1) 5 := by simp [regBound]

-- rb_prog_67_6_1
example : regBound (.install 1 2 3 4 5:HolProg 1) 6 := by simp [regBound]

-- rb_prog_68_2_1
example : ¬ regBound (.shMemOp .load16 1 (.addr 2 255):HolProg 1) 2 := by simp [regBound]

-- rb_prog_68_3_1
example : regBound (.shMemOp .load16 1 (.addr 2 255):HolProg 1) 3 := by simp [regBound]

-- rb_prog_69_2_1
example : ¬ regBound (.codeBufferWrite 1 2:HolProg 1) 2 := by simp [regBound]

-- rb_prog_69_3_1
example : regBound (.codeBufferWrite 1 2:HolProg 1) 3 := by simp [regBound]

-- rb_prog_70_2_1
example : ¬ regBound (.dataBufferWrite 1 2:HolProg 1) 2 := by simp [regBound]

-- rb_prog_70_3_1
example : regBound (.dataBufferWrite 1 2:HolProg 1) 3 := by simp [regBound]

-- rb_prog_71_0_1
example : regBound (.rawCall 999:HolProg 1) 0 := by simp [regBound]

-- rb_prog_71_100_1
example : regBound (.rawCall 999:HolProg 1) 100 := by simp [regBound]

-- rb_prog_72_0_1
example : regBound (.stackAlloc 999:HolProg 1) 0 := by simp [regBound]

-- rb_prog_72_100_1
example : regBound (.stackAlloc 999:HolProg 1) 100 := by simp [regBound]

-- rb_prog_73_0_1
example : regBound (.stackFree 999:HolProg 1) 0 := by simp [regBound]

-- rb_prog_73_100_1
example : regBound (.stackFree 999:HolProg 1) 100 := by simp [regBound]

-- rb_prog_74_1_1
example : ¬ regBound (.stackStore 1 999:HolProg 1) 1 := by simp [regBound]

-- rb_prog_74_2_1
example : regBound (.stackStore 1 999:HolProg 1) 2 := by simp [regBound]

-- rb_prog_75_999_1
example : ¬ regBound (.stackStore 999 1:HolProg 1) 999 := by simp [regBound]

-- rb_prog_75_1000_1
example : regBound (.stackStore 999 1:HolProg 1) 1000 := by simp [regBound]

-- rb_prog_76_1_1
example : ¬ regBound (.stackLoad 1 999:HolProg 1) 1 := by simp [regBound]

-- rb_prog_76_2_1
example : regBound (.stackLoad 1 999:HolProg 1) 2 := by simp [regBound]

-- rb_prog_77_999_1
example : ¬ regBound (.stackLoad 999 1:HolProg 1) 999 := by simp [regBound]

-- rb_prog_77_1000_1
example : regBound (.stackLoad 999 1:HolProg 1) 1000 := by simp [regBound]

-- rb_prog_78_2_1
example : ¬ regBound (.stackStoreAny 1 2:HolProg 1) 2 := by simp [regBound]

-- rb_prog_78_3_1
example : regBound (.stackStoreAny 1 2:HolProg 1) 3 := by simp [regBound]

-- rb_prog_79_2_1
example : ¬ regBound (.stackLoadAny 1 2:HolProg 1) 2 := by simp [regBound]

-- rb_prog_79_3_1
example : regBound (.stackLoadAny 1 2:HolProg 1) 3 := by simp [regBound]

-- rb_prog_80_1_1
example : ¬ regBound (.stackGetSize 1:HolProg 1) 1 := by simp [regBound]

-- rb_prog_80_2_1
example : regBound (.stackGetSize 1:HolProg 1) 2 := by simp [regBound]

-- rb_prog_81_1_1
example : ¬ regBound (.stackSetSize 1:HolProg 1) 1 := by simp [regBound]

-- rb_prog_81_2_1
example : regBound (.stackSetSize 1:HolProg 1) 2 := by simp [regBound]

-- rb_prog_82_2_1
example : ¬ regBound (.bitmapLoad 1 2:HolProg 1) 2 := by simp [regBound]

-- rb_prog_82_3_1
example : regBound (.bitmapLoad 1 2:HolProg 1) 3 := by simp [regBound]

-- rb_prog_83_1_1
example : ¬ regBound (.halt 1:HolProg 1) 1 := by simp [regBound]

-- rb_prog_83_2_1
example : regBound (.halt 1:HolProg 1) 2 := by simp [regBound]

-- rb_exp_0_3_64
example : ¬ regBoundExp (.var 3:WordLangExpHOL (BitVec 64)) 3 := by simp [regBoundExp]

-- rb_exp_0_4_64
example : regBoundExp (.var 3:WordLangExpHOL (BitVec 64)) 4 := by simp [regBoundExp]

-- rb_exp_1_0_64
example : regBoundExp (.const 255:WordLangExpHOL (BitVec 64)) 0 := by simp [regBoundExp]

-- rb_exp_1_100_64
example : regBoundExp (.const 255:WordLangExpHOL (BitVec 64)) 100 := by simp [regBoundExp]

-- rb_exp_2_0_64
example : ¬ regBoundExp (.lookup .currHeap:WordLangExpHOL (BitVec 64)) 0 := by simp [regBoundExp]

-- rb_exp_2_100_64
example : ¬ regBoundExp (.lookup .currHeap:WordLangExpHOL (BitVec 64)) 100 := by simp [regBoundExp]

-- rb_exp_3_3_64
example : ¬ regBoundExp (.load (.var 3):WordLangExpHOL (BitVec 64)) 3 := by simp [regBoundExp]

-- rb_exp_3_4_64
example : regBoundExp (.load (.var 3):WordLangExpHOL (BitVec 64)) 4 := by simp [regBoundExp]

-- rb_exp_4_5_64
example : ¬ regBoundExp (.shift .lsl (.var 3) (.var 5):WordLangExpHOL (BitVec 64)) 5 := by simp [regBoundExp]

-- rb_exp_4_6_64
example : regBoundExp (.shift .lsl (.var 3) (.var 5):WordLangExpHOL (BitVec 64)) 6 := by simp [regBoundExp]

-- rb_exp_5_0_64
example : regBoundExp (.op .add []:WordLangExpHOL (BitVec 64)) 0 := by simp [regBoundExp]

-- rb_exp_5_100_64
example : regBoundExp (.op .add []:WordLangExpHOL (BitVec 64)) 100 := by simp [regBoundExp]

-- rb_exp_6_9_64
example : ¬ regBoundExp (.op .add [.var 1,.load (.var 9)]:WordLangExpHOL (BitVec 64)) 9 := by simp [regBoundExp]

-- rb_exp_6_10_64
example : regBoundExp (.op .add [.var 1,.load (.var 9)]:WordLangExpHOL (BitVec 64)) 10 := by simp [regBoundExp]

-- rb_exp_7_0_64
example : ¬ regBoundExp (.op .xor [.lookup .currHeap,.const 255]:WordLangExpHOL (BitVec 64)) 0 := by simp [regBoundExp]

-- rb_exp_7_100_64
example : ¬ regBoundExp (.op .xor [.lookup .currHeap,.const 255]:WordLangExpHOL (BitVec 64)) 100 := by simp [regBoundExp]

-- rb_inst_8_0_64
example : regBoundInst (.skip:HolInst 64) 0 := by simp [regBoundInst]

-- rb_inst_8_100_64
example : regBoundInst (.skip:HolInst 64) 100 := by simp [regBoundInst]

-- rb_inst_9_1_64
example : ¬ regBoundInst (.const 1 255:HolInst 64) 1 := by simp [regBoundInst]

-- rb_inst_9_2_64
example : regBoundInst (.const 1 255:HolInst 64) 2 := by simp [regBoundInst]

-- rb_inst_10_2_64
example : ¬ regBoundInst (.mem .load 1 (.addr 2 255):HolInst 64) 2 := by simp [regBoundInst]

-- rb_inst_10_3_64
example : regBoundInst (.mem .load 1 (.addr 2 255):HolInst 64) 3 := by simp [regBoundInst]

-- rb_inst_11_2_64
example : ¬ regBoundInst (.mem .load8 1 (.addr 2 255):HolInst 64) 2 := by simp [regBoundInst]

-- rb_inst_11_3_64
example : regBoundInst (.mem .load8 1 (.addr 2 255):HolInst 64) 3 := by simp [regBoundInst]

-- rb_inst_12_2_64
example : ¬ regBoundInst (.mem .load16 1 (.addr 2 255):HolInst 64) 2 := by simp [regBoundInst]

-- rb_inst_12_3_64
example : regBoundInst (.mem .load16 1 (.addr 2 255):HolInst 64) 3 := by simp [regBoundInst]

-- rb_inst_13_2_64
example : ¬ regBoundInst (.mem .load32 1 (.addr 2 255):HolInst 64) 2 := by simp [regBoundInst]

-- rb_inst_13_3_64
example : regBoundInst (.mem .load32 1 (.addr 2 255):HolInst 64) 3 := by simp [regBoundInst]

-- rb_inst_14_2_64
example : ¬ regBoundInst (.mem .store 1 (.addr 2 255):HolInst 64) 2 := by simp [regBoundInst]

-- rb_inst_14_3_64
example : regBoundInst (.mem .store 1 (.addr 2 255):HolInst 64) 3 := by simp [regBoundInst]

-- rb_inst_15_2_64
example : ¬ regBoundInst (.mem .store8 1 (.addr 2 255):HolInst 64) 2 := by simp [regBoundInst]

-- rb_inst_15_3_64
example : regBoundInst (.mem .store8 1 (.addr 2 255):HolInst 64) 3 := by simp [regBoundInst]

-- rb_inst_16_2_64
example : ¬ regBoundInst (.mem .store16 1 (.addr 2 255):HolInst 64) 2 := by simp [regBoundInst]

-- rb_inst_16_3_64
example : regBoundInst (.mem .store16 1 (.addr 2 255):HolInst 64) 3 := by simp [regBoundInst]

-- rb_inst_17_2_64
example : ¬ regBoundInst (.mem .store32 1 (.addr 2 255):HolInst 64) 2 := by simp [regBoundInst]

-- rb_inst_17_3_64
example : regBoundInst (.mem .store32 1 (.addr 2 255):HolInst 64) 3 := by simp [regBoundInst]

-- rb_inst_18_3_64
example : ¬ regBoundInst (.arith (.binop .add 1 2 (.reg 3)):HolInst 64) 3 := by simp [regBoundInst]

-- rb_inst_18_4_64
example : regBoundInst (.arith (.binop .add 1 2 (.reg 3)):HolInst 64) 4 := by simp [regBoundInst]

-- rb_inst_19_2_64
example : ¬ regBoundInst (.arith (.binop .and 1 2 (.imm 255)):HolInst 64) 2 := by simp [regBoundInst]

-- rb_inst_19_3_64
example : regBoundInst (.arith (.binop .and 1 2 (.imm 255)):HolInst 64) 3 := by simp [regBoundInst]

-- rb_inst_20_3_64
example : ¬ regBoundInst (.arith (.shift .lsl 1 2 (.reg 3)):HolInst 64) 3 := by simp [regBoundInst]

-- rb_inst_20_4_64
example : regBoundInst (.arith (.shift .lsl 1 2 (.reg 3)):HolInst 64) 4 := by simp [regBoundInst]

-- rb_inst_21_2_64
example : ¬ regBoundInst (.arith (.shift .ror 1 2 (.imm 255)):HolInst 64) 2 := by simp [regBoundInst]

-- rb_inst_21_3_64
example : regBoundInst (.arith (.shift .ror 1 2 (.imm 255)):HolInst 64) 3 := by simp [regBoundInst]

-- rb_inst_22_3_64
example : ¬ regBoundInst (.arith (.div 1 2 3):HolInst 64) 3 := by simp [regBoundInst]

-- rb_inst_22_4_64
example : regBoundInst (.arith (.div 1 2 3):HolInst 64) 4 := by simp [regBoundInst]

-- rb_inst_23_4_64
example : ¬ regBoundInst (.arith (.longMul 1 2 3 4):HolInst 64) 4 := by simp [regBoundInst]

-- rb_inst_23_5_64
example : regBoundInst (.arith (.longMul 1 2 3 4):HolInst 64) 5 := by simp [regBoundInst]

-- rb_inst_24_5_64
example : ¬ regBoundInst (.arith (.longDiv 1 2 3 4 5):HolInst 64) 5 := by simp [regBoundInst]

-- rb_inst_24_6_64
example : regBoundInst (.arith (.longDiv 1 2 3 4 5):HolInst 64) 6 := by simp [regBoundInst]

-- rb_inst_25_4_64
example : ¬ regBoundInst (.arith (.addCarry 1 2 3 4):HolInst 64) 4 := by simp [regBoundInst]

-- rb_inst_25_5_64
example : regBoundInst (.arith (.addCarry 1 2 3 4):HolInst 64) 5 := by simp [regBoundInst]

-- rb_inst_26_4_64
example : ¬ regBoundInst (.arith (.addOverflow 1 2 3 4):HolInst 64) 4 := by simp [regBoundInst]

-- rb_inst_26_5_64
example : regBoundInst (.arith (.addOverflow 1 2 3 4):HolInst 64) 5 := by simp [regBoundInst]

-- rb_inst_27_4_64
example : ¬ regBoundInst (.arith (.subOverflow 1 2 3 4):HolInst 64) 4 := by simp [regBoundInst]

-- rb_inst_27_5_64
example : regBoundInst (.arith (.subOverflow 1 2 3 4):HolInst 64) 5 := by simp [regBoundInst]

-- rb_inst_28_1_64
example : ¬ regBoundInst (.fp (.fpLess 1 99 100):HolInst 64) 1 := by simp [regBoundInst]

-- rb_inst_28_2_64
example : regBoundInst (.fp (.fpLess 1 99 100):HolInst 64) 2 := by simp [regBoundInst]

-- rb_inst_29_1_64
example : ¬ regBoundInst (.fp (.fpLessEqual 1 99 100):HolInst 64) 1 := by simp [regBoundInst]

-- rb_inst_29_2_64
example : regBoundInst (.fp (.fpLessEqual 1 99 100):HolInst 64) 2 := by simp [regBoundInst]

-- rb_inst_30_1_64
example : ¬ regBoundInst (.fp (.fpEqual 1 99 100):HolInst 64) 1 := by simp [regBoundInst]

-- rb_inst_30_2_64
example : regBoundInst (.fp (.fpEqual 1 99 100):HolInst 64) 2 := by simp [regBoundInst]

-- rb_inst_31_0_64
example : regBoundInst (.fp (.fpAbs 100 100):HolInst 64) 0 := by simp [regBoundInst]

-- rb_inst_31_100_64
example : regBoundInst (.fp (.fpAbs 100 100):HolInst 64) 100 := by simp [regBoundInst]

-- rb_inst_32_0_64
example : regBoundInst (.fp (.fpNeg 100 100):HolInst 64) 0 := by simp [regBoundInst]

-- rb_inst_32_100_64
example : regBoundInst (.fp (.fpNeg 100 100):HolInst 64) 100 := by simp [regBoundInst]

-- rb_inst_33_0_64
example : regBoundInst (.fp (.fpSqrt 100 100):HolInst 64) 0 := by simp [regBoundInst]

-- rb_inst_33_100_64
example : regBoundInst (.fp (.fpSqrt 100 100):HolInst 64) 100 := by simp [regBoundInst]

-- rb_inst_34_0_64
example : regBoundInst (.fp (.fpAdd 100 100 100):HolInst 64) 0 := by simp [regBoundInst]

-- rb_inst_34_100_64
example : regBoundInst (.fp (.fpAdd 100 100 100):HolInst 64) 100 := by simp [regBoundInst]

-- rb_inst_35_0_64
example : regBoundInst (.fp (.fpSub 100 100 100):HolInst 64) 0 := by simp [regBoundInst]

-- rb_inst_35_100_64
example : regBoundInst (.fp (.fpSub 100 100 100):HolInst 64) 100 := by simp [regBoundInst]

-- rb_inst_36_0_64
example : regBoundInst (.fp (.fpMul 100 100 100):HolInst 64) 0 := by simp [regBoundInst]

-- rb_inst_36_100_64
example : regBoundInst (.fp (.fpMul 100 100 100):HolInst 64) 100 := by simp [regBoundInst]

-- rb_inst_37_0_64
example : regBoundInst (.fp (.fpDiv 100 100 100):HolInst 64) 0 := by simp [regBoundInst]

-- rb_inst_37_100_64
example : regBoundInst (.fp (.fpDiv 100 100 100):HolInst 64) 100 := by simp [regBoundInst]

-- rb_inst_38_0_64
example : regBoundInst (.fp (.fpFma 100 100 100):HolInst 64) 0 := by simp [regBoundInst]

-- rb_inst_38_100_64
example : regBoundInst (.fp (.fpFma 100 100 100):HolInst 64) 100 := by simp [regBoundInst]

-- rb_inst_39_0_64
example : regBoundInst (.fp (.fpMov 100 100):HolInst 64) 0 := by simp [regBoundInst]

-- rb_inst_39_100_64
example : regBoundInst (.fp (.fpMov 100 100):HolInst 64) 100 := by simp [regBoundInst]

-- rb_inst_40_0_64
example : regBoundInst (.fp (.fpToInt 100 100):HolInst 64) 0 := by simp [regBoundInst]

-- rb_inst_40_100_64
example : regBoundInst (.fp (.fpToInt 100 100):HolInst 64) 100 := by simp [regBoundInst]

-- rb_inst_41_0_64
example : regBoundInst (.fp (.fpFromInt 100 100):HolInst 64) 0 := by simp [regBoundInst]

-- rb_inst_41_100_64
example : regBoundInst (.fp (.fpFromInt 100 100):HolInst 64) 100 := by simp [regBoundInst]

-- rb_inst_42_2_64
example : ¬ regBoundInst (.fp (.fpMovToReg 1 2 100):HolInst 64) 2 := by simp [regBoundInst]

-- rb_inst_42_3_64
example : regBoundInst (.fp (.fpMovToReg 1 2 100):HolInst 64) 3 := by simp [regBoundInst]

-- rb_inst_43_2_64
example : ¬ regBoundInst (.fp (.fpMovFromReg 100 1 2):HolInst 64) 2 := by simp [regBoundInst]

-- rb_inst_43_3_64
example : regBoundInst (.fp (.fpMovFromReg 100 1 2):HolInst 64) 3 := by simp [regBoundInst]

-- rb_prog_44_0_64
example : regBound (.skip:HolProg 64) 0 := by simp [regBound]

-- rb_prog_44_100_64
example : regBound (.skip:HolProg 64) 100 := by simp [regBound]

-- rb_prog_45_1_64
example : ¬ regBound (.inst (.const 1 255):HolProg 64) 1 := by simp [regBound, regBoundInst]

-- rb_prog_45_2_64
example : regBound (.inst (.const 1 255):HolProg 64) 2 := by simp [regBound, regBoundInst]

-- rb_prog_46_1_64
example : ¬ regBound (.get 1 .currHeap:HolProg 64) 1 := by simp [regBound]

-- rb_prog_46_2_64
example : regBound (.get 1 .currHeap:HolProg 64) 2 := by simp [regBound]

-- rb_prog_47_1_64
example : ¬ regBound (.set .currHeap 1:HolProg 64) 1 := by simp [regBound]

-- rb_prog_47_2_64
example : regBound (.set .currHeap 1:HolProg 64) 2 := by simp [regBound]

-- rb_prog_48_0_64
example : ¬ regBound (.set .bitmapBase 1:HolProg 64) 0 := by simp [regBound]

-- rb_prog_48_100_64
example : ¬ regBound (.set .bitmapBase 1:HolProg 64) 100 := by simp [regBound]

-- rb_prog_49_2_64
example : ¬ regBound (.opCurrHeap .add 1 2:HolProg 64) 2 := by simp [regBound]

-- rb_prog_49_3_64
example : regBound (.opCurrHeap .add 1 2:HolProg 64) 3 := by simp [regBound]

-- rb_prog_50_0_64
example : regBound (.call none (.inl 999) (some (.halt 100,999,999)):HolProg 64) 0 := by simp [regBound]

-- rb_prog_50_100_64
example : regBound (.call none (.inl 999) (some (.halt 100,999,999)):HolProg 64) 100 := by simp [regBound]

-- rb_prog_51_2_64
example : ¬ regBound (.call none (.inr 2) none:HolProg 64) 2 := by simp [regBound]

-- rb_prog_51_3_64
example : regBound (.call none (.inr 2) none:HolProg 64) 3 := by simp [regBound]

-- rb_prog_52_3_64
example : ¬ regBound (.call (some (.halt 1,2,999,999)) (.inl 999) (some (.halt 3,999,999)):HolProg 64) 3 := by simp [regBound]

-- rb_prog_52_4_64
example : regBound (.call (some (.halt 1,2,999,999)) (.inl 999) (some (.halt 3,999,999)):HolProg 64) 4 := by simp [regBound]

-- rb_prog_53_2_64
example : ¬ regBound (.seq (.halt 1) (.halt 2):HolProg 64) 2 := by simp [regBound]

-- rb_prog_53_3_64
example : regBound (.seq (.halt 1) (.halt 2):HolProg 64) 3 := by simp [regBound]

-- rb_prog_54_3_64
example : ¬ regBound (.ite .equal 1 (.reg 2) .skip (.halt 3):HolProg 64) 3 := by simp [regBound]

-- rb_prog_54_4_64
example : regBound (.ite .equal 1 (.reg 2) .skip (.halt 3):HolProg 64) 4 := by simp [regBound]

-- rb_prog_55_1_64
example : ¬ regBound (.ite .equal 1 (.imm 255) .skip .skip:HolProg 64) 1 := by simp [regBound]

-- rb_prog_55_2_64
example : regBound (.ite .equal 1 (.imm 255) .skip .skip:HolProg 64) 2 := by simp [regBound]

-- rb_prog_56_2_64
example : ¬ regBound (.loop (.halt 2):HolProg 64) 2 := by simp [regBound]

-- rb_prog_56_3_64
example : regBound (.loop (.halt 2):HolProg 64) 3 := by simp [regBound]

-- rb_prog_57_2_64
example : ¬ regBound (.jumpLower 1 2 999:HolProg 64) 2 := by simp [regBound]

-- rb_prog_57_3_64
example : regBound (.jumpLower 1 2 999:HolProg 64) 3 := by simp [regBound]

-- rb_prog_58_0_64
example : regBound (.alloc 999:HolProg 64) 0 := by simp [regBound]

-- rb_prog_58_100_64
example : regBound (.alloc 999:HolProg 64) 100 := by simp [regBound]

-- rb_prog_59_3_64
example : ¬ regBound (.storeConsts 0 0 (some 999):HolProg 64) 3 := by simp [regBound]

-- rb_prog_59_4_64
example : regBound (.storeConsts 0 0 (some 999):HolProg 64) 4 := by simp [regBound]

-- rb_prog_60_1_64
example : ¬ regBound (.raise 1:HolProg 64) 1 := by simp [regBound]

-- rb_prog_60_2_64
example : regBound (.raise 1:HolProg 64) 2 := by simp [regBound]

-- rb_prog_61_1_64
example : ¬ regBound (.ret 1:HolProg 64) 1 := by simp [regBound]

-- rb_prog_61_2_64
example : regBound (.ret 1:HolProg 64) 2 := by simp [regBound]

-- rb_prog_62_0_64
example : regBound (.break 999:HolProg 64) 0 := by simp [regBound]

-- rb_prog_62_100_64
example : regBound (.break 999:HolProg 64) 100 := by simp [regBound]

-- rb_prog_63_0_64
example : regBound (.continue 999:HolProg 64) 0 := by simp [regBound]

-- rb_prog_63_100_64
example : regBound (.continue 999:HolProg 64) 100 := by simp [regBound]

-- rb_prog_64_5_64
example : ¬ regBound (.ffi (Flapjack.Basis.Pure.MlString.ofString "x") 1 2 3 4 5:HolProg 64) 5 := by simp [regBound]

-- rb_prog_64_6_64
example : regBound (.ffi (Flapjack.Basis.Pure.MlString.ofString "x") 1 2 3 4 5:HolProg 64) 6 := by simp [regBound]

-- rb_prog_65_0_64
example : regBound (.tick:HolProg 64) 0 := by simp [regBound]

-- rb_prog_65_100_64
example : regBound (.tick:HolProg 64) 100 := by simp [regBound]

-- rb_prog_66_1_64
example : ¬ regBound (.locValue 1 999 999:HolProg 64) 1 := by simp [regBound]

-- rb_prog_66_2_64
example : regBound (.locValue 1 999 999:HolProg 64) 2 := by simp [regBound]

-- rb_prog_67_5_64
example : ¬ regBound (.install 1 2 3 4 5:HolProg 64) 5 := by simp [regBound]

-- rb_prog_67_6_64
example : regBound (.install 1 2 3 4 5:HolProg 64) 6 := by simp [regBound]

-- rb_prog_68_2_64
example : ¬ regBound (.shMemOp .load16 1 (.addr 2 255):HolProg 64) 2 := by simp [regBound]

-- rb_prog_68_3_64
example : regBound (.shMemOp .load16 1 (.addr 2 255):HolProg 64) 3 := by simp [regBound]

-- rb_prog_69_2_64
example : ¬ regBound (.codeBufferWrite 1 2:HolProg 64) 2 := by simp [regBound]

-- rb_prog_69_3_64
example : regBound (.codeBufferWrite 1 2:HolProg 64) 3 := by simp [regBound]

-- rb_prog_70_2_64
example : ¬ regBound (.dataBufferWrite 1 2:HolProg 64) 2 := by simp [regBound]

-- rb_prog_70_3_64
example : regBound (.dataBufferWrite 1 2:HolProg 64) 3 := by simp [regBound]

-- rb_prog_71_0_64
example : regBound (.rawCall 999:HolProg 64) 0 := by simp [regBound]

-- rb_prog_71_100_64
example : regBound (.rawCall 999:HolProg 64) 100 := by simp [regBound]

-- rb_prog_72_0_64
example : regBound (.stackAlloc 999:HolProg 64) 0 := by simp [regBound]

-- rb_prog_72_100_64
example : regBound (.stackAlloc 999:HolProg 64) 100 := by simp [regBound]

-- rb_prog_73_0_64
example : regBound (.stackFree 999:HolProg 64) 0 := by simp [regBound]

-- rb_prog_73_100_64
example : regBound (.stackFree 999:HolProg 64) 100 := by simp [regBound]

-- rb_prog_74_1_64
example : ¬ regBound (.stackStore 1 999:HolProg 64) 1 := by simp [regBound]

-- rb_prog_74_2_64
example : regBound (.stackStore 1 999:HolProg 64) 2 := by simp [regBound]

-- rb_prog_75_999_64
example : ¬ regBound (.stackStore 999 1:HolProg 64) 999 := by simp [regBound]

-- rb_prog_75_1000_64
example : regBound (.stackStore 999 1:HolProg 64) 1000 := by simp [regBound]

-- rb_prog_76_1_64
example : ¬ regBound (.stackLoad 1 999:HolProg 64) 1 := by simp [regBound]

-- rb_prog_76_2_64
example : regBound (.stackLoad 1 999:HolProg 64) 2 := by simp [regBound]

-- rb_prog_77_999_64
example : ¬ regBound (.stackLoad 999 1:HolProg 64) 999 := by simp [regBound]

-- rb_prog_77_1000_64
example : regBound (.stackLoad 999 1:HolProg 64) 1000 := by simp [regBound]

-- rb_prog_78_2_64
example : ¬ regBound (.stackStoreAny 1 2:HolProg 64) 2 := by simp [regBound]

-- rb_prog_78_3_64
example : regBound (.stackStoreAny 1 2:HolProg 64) 3 := by simp [regBound]

-- rb_prog_79_2_64
example : ¬ regBound (.stackLoadAny 1 2:HolProg 64) 2 := by simp [regBound]

-- rb_prog_79_3_64
example : regBound (.stackLoadAny 1 2:HolProg 64) 3 := by simp [regBound]

-- rb_prog_80_1_64
example : ¬ regBound (.stackGetSize 1:HolProg 64) 1 := by simp [regBound]

-- rb_prog_80_2_64
example : regBound (.stackGetSize 1:HolProg 64) 2 := by simp [regBound]

-- rb_prog_81_1_64
example : ¬ regBound (.stackSetSize 1:HolProg 64) 1 := by simp [regBound]

-- rb_prog_81_2_64
example : regBound (.stackSetSize 1:HolProg 64) 2 := by simp [regBound]

-- rb_prog_82_2_64
example : ¬ regBound (.bitmapLoad 1 2:HolProg 64) 2 := by simp [regBound]

-- rb_prog_82_3_64
example : regBound (.bitmapLoad 1 2:HolProg 64) 3 := by simp [regBound]

-- rb_prog_83_1_64
example : ¬ regBound (.halt 1:HolProg 64) 1 := by simp [regBound]

-- rb_prog_83_2_64
example : regBound (.halt 1:HolProg 64) 2 := by simp [regBound]

-- rb_exp_0_3_80
example : ¬ regBoundExp (.var 3:WordLangExpHOL (BitVec 80)) 3 := by simp [regBoundExp]

-- rb_exp_0_4_80
example : regBoundExp (.var 3:WordLangExpHOL (BitVec 80)) 4 := by simp [regBoundExp]

-- rb_exp_1_0_80
example : regBoundExp (.const 255:WordLangExpHOL (BitVec 80)) 0 := by simp [regBoundExp]

-- rb_exp_1_100_80
example : regBoundExp (.const 255:WordLangExpHOL (BitVec 80)) 100 := by simp [regBoundExp]

-- rb_exp_2_0_80
example : ¬ regBoundExp (.lookup .currHeap:WordLangExpHOL (BitVec 80)) 0 := by simp [regBoundExp]

-- rb_exp_2_100_80
example : ¬ regBoundExp (.lookup .currHeap:WordLangExpHOL (BitVec 80)) 100 := by simp [regBoundExp]

-- rb_exp_3_3_80
example : ¬ regBoundExp (.load (.var 3):WordLangExpHOL (BitVec 80)) 3 := by simp [regBoundExp]

-- rb_exp_3_4_80
example : regBoundExp (.load (.var 3):WordLangExpHOL (BitVec 80)) 4 := by simp [regBoundExp]

-- rb_exp_4_5_80
example : ¬ regBoundExp (.shift .lsl (.var 3) (.var 5):WordLangExpHOL (BitVec 80)) 5 := by simp [regBoundExp]

-- rb_exp_4_6_80
example : regBoundExp (.shift .lsl (.var 3) (.var 5):WordLangExpHOL (BitVec 80)) 6 := by simp [regBoundExp]

-- rb_exp_5_0_80
example : regBoundExp (.op .add []:WordLangExpHOL (BitVec 80)) 0 := by simp [regBoundExp]

-- rb_exp_5_100_80
example : regBoundExp (.op .add []:WordLangExpHOL (BitVec 80)) 100 := by simp [regBoundExp]

-- rb_exp_6_9_80
example : ¬ regBoundExp (.op .add [.var 1,.load (.var 9)]:WordLangExpHOL (BitVec 80)) 9 := by simp [regBoundExp]

-- rb_exp_6_10_80
example : regBoundExp (.op .add [.var 1,.load (.var 9)]:WordLangExpHOL (BitVec 80)) 10 := by simp [regBoundExp]

-- rb_exp_7_0_80
example : ¬ regBoundExp (.op .xor [.lookup .currHeap,.const 255]:WordLangExpHOL (BitVec 80)) 0 := by simp [regBoundExp]

-- rb_exp_7_100_80
example : ¬ regBoundExp (.op .xor [.lookup .currHeap,.const 255]:WordLangExpHOL (BitVec 80)) 100 := by simp [regBoundExp]

-- rb_inst_8_0_80
example : regBoundInst (.skip:HolInst 80) 0 := by simp [regBoundInst]

-- rb_inst_8_100_80
example : regBoundInst (.skip:HolInst 80) 100 := by simp [regBoundInst]

-- rb_inst_9_1_80
example : ¬ regBoundInst (.const 1 255:HolInst 80) 1 := by simp [regBoundInst]

-- rb_inst_9_2_80
example : regBoundInst (.const 1 255:HolInst 80) 2 := by simp [regBoundInst]

-- rb_inst_10_2_80
example : ¬ regBoundInst (.mem .load 1 (.addr 2 255):HolInst 80) 2 := by simp [regBoundInst]

-- rb_inst_10_3_80
example : regBoundInst (.mem .load 1 (.addr 2 255):HolInst 80) 3 := by simp [regBoundInst]

-- rb_inst_11_2_80
example : ¬ regBoundInst (.mem .load8 1 (.addr 2 255):HolInst 80) 2 := by simp [regBoundInst]

-- rb_inst_11_3_80
example : regBoundInst (.mem .load8 1 (.addr 2 255):HolInst 80) 3 := by simp [regBoundInst]

-- rb_inst_12_2_80
example : ¬ regBoundInst (.mem .load16 1 (.addr 2 255):HolInst 80) 2 := by simp [regBoundInst]

-- rb_inst_12_3_80
example : regBoundInst (.mem .load16 1 (.addr 2 255):HolInst 80) 3 := by simp [regBoundInst]

-- rb_inst_13_2_80
example : ¬ regBoundInst (.mem .load32 1 (.addr 2 255):HolInst 80) 2 := by simp [regBoundInst]

-- rb_inst_13_3_80
example : regBoundInst (.mem .load32 1 (.addr 2 255):HolInst 80) 3 := by simp [regBoundInst]

-- rb_inst_14_2_80
example : ¬ regBoundInst (.mem .store 1 (.addr 2 255):HolInst 80) 2 := by simp [regBoundInst]

-- rb_inst_14_3_80
example : regBoundInst (.mem .store 1 (.addr 2 255):HolInst 80) 3 := by simp [regBoundInst]

-- rb_inst_15_2_80
example : ¬ regBoundInst (.mem .store8 1 (.addr 2 255):HolInst 80) 2 := by simp [regBoundInst]

-- rb_inst_15_3_80
example : regBoundInst (.mem .store8 1 (.addr 2 255):HolInst 80) 3 := by simp [regBoundInst]

-- rb_inst_16_2_80
example : ¬ regBoundInst (.mem .store16 1 (.addr 2 255):HolInst 80) 2 := by simp [regBoundInst]

-- rb_inst_16_3_80
example : regBoundInst (.mem .store16 1 (.addr 2 255):HolInst 80) 3 := by simp [regBoundInst]

-- rb_inst_17_2_80
example : ¬ regBoundInst (.mem .store32 1 (.addr 2 255):HolInst 80) 2 := by simp [regBoundInst]

-- rb_inst_17_3_80
example : regBoundInst (.mem .store32 1 (.addr 2 255):HolInst 80) 3 := by simp [regBoundInst]

-- rb_inst_18_3_80
example : ¬ regBoundInst (.arith (.binop .add 1 2 (.reg 3)):HolInst 80) 3 := by simp [regBoundInst]

-- rb_inst_18_4_80
example : regBoundInst (.arith (.binop .add 1 2 (.reg 3)):HolInst 80) 4 := by simp [regBoundInst]

-- rb_inst_19_2_80
example : ¬ regBoundInst (.arith (.binop .and 1 2 (.imm 255)):HolInst 80) 2 := by simp [regBoundInst]

-- rb_inst_19_3_80
example : regBoundInst (.arith (.binop .and 1 2 (.imm 255)):HolInst 80) 3 := by simp [regBoundInst]

-- rb_inst_20_3_80
example : ¬ regBoundInst (.arith (.shift .lsl 1 2 (.reg 3)):HolInst 80) 3 := by simp [regBoundInst]

-- rb_inst_20_4_80
example : regBoundInst (.arith (.shift .lsl 1 2 (.reg 3)):HolInst 80) 4 := by simp [regBoundInst]

-- rb_inst_21_2_80
example : ¬ regBoundInst (.arith (.shift .ror 1 2 (.imm 255)):HolInst 80) 2 := by simp [regBoundInst]

-- rb_inst_21_3_80
example : regBoundInst (.arith (.shift .ror 1 2 (.imm 255)):HolInst 80) 3 := by simp [regBoundInst]

-- rb_inst_22_3_80
example : ¬ regBoundInst (.arith (.div 1 2 3):HolInst 80) 3 := by simp [regBoundInst]

-- rb_inst_22_4_80
example : regBoundInst (.arith (.div 1 2 3):HolInst 80) 4 := by simp [regBoundInst]

-- rb_inst_23_4_80
example : ¬ regBoundInst (.arith (.longMul 1 2 3 4):HolInst 80) 4 := by simp [regBoundInst]

-- rb_inst_23_5_80
example : regBoundInst (.arith (.longMul 1 2 3 4):HolInst 80) 5 := by simp [regBoundInst]

-- rb_inst_24_5_80
example : ¬ regBoundInst (.arith (.longDiv 1 2 3 4 5):HolInst 80) 5 := by simp [regBoundInst]

-- rb_inst_24_6_80
example : regBoundInst (.arith (.longDiv 1 2 3 4 5):HolInst 80) 6 := by simp [regBoundInst]

-- rb_inst_25_4_80
example : ¬ regBoundInst (.arith (.addCarry 1 2 3 4):HolInst 80) 4 := by simp [regBoundInst]

-- rb_inst_25_5_80
example : regBoundInst (.arith (.addCarry 1 2 3 4):HolInst 80) 5 := by simp [regBoundInst]

-- rb_inst_26_4_80
example : ¬ regBoundInst (.arith (.addOverflow 1 2 3 4):HolInst 80) 4 := by simp [regBoundInst]

-- rb_inst_26_5_80
example : regBoundInst (.arith (.addOverflow 1 2 3 4):HolInst 80) 5 := by simp [regBoundInst]

-- rb_inst_27_4_80
example : ¬ regBoundInst (.arith (.subOverflow 1 2 3 4):HolInst 80) 4 := by simp [regBoundInst]

-- rb_inst_27_5_80
example : regBoundInst (.arith (.subOverflow 1 2 3 4):HolInst 80) 5 := by simp [regBoundInst]

-- rb_inst_28_1_80
example : ¬ regBoundInst (.fp (.fpLess 1 99 100):HolInst 80) 1 := by simp [regBoundInst]

-- rb_inst_28_2_80
example : regBoundInst (.fp (.fpLess 1 99 100):HolInst 80) 2 := by simp [regBoundInst]

-- rb_inst_29_1_80
example : ¬ regBoundInst (.fp (.fpLessEqual 1 99 100):HolInst 80) 1 := by simp [regBoundInst]

-- rb_inst_29_2_80
example : regBoundInst (.fp (.fpLessEqual 1 99 100):HolInst 80) 2 := by simp [regBoundInst]

-- rb_inst_30_1_80
example : ¬ regBoundInst (.fp (.fpEqual 1 99 100):HolInst 80) 1 := by simp [regBoundInst]

-- rb_inst_30_2_80
example : regBoundInst (.fp (.fpEqual 1 99 100):HolInst 80) 2 := by simp [regBoundInst]

-- rb_inst_31_0_80
example : regBoundInst (.fp (.fpAbs 100 100):HolInst 80) 0 := by simp [regBoundInst]

-- rb_inst_31_100_80
example : regBoundInst (.fp (.fpAbs 100 100):HolInst 80) 100 := by simp [regBoundInst]

-- rb_inst_32_0_80
example : regBoundInst (.fp (.fpNeg 100 100):HolInst 80) 0 := by simp [regBoundInst]

-- rb_inst_32_100_80
example : regBoundInst (.fp (.fpNeg 100 100):HolInst 80) 100 := by simp [regBoundInst]

-- rb_inst_33_0_80
example : regBoundInst (.fp (.fpSqrt 100 100):HolInst 80) 0 := by simp [regBoundInst]

-- rb_inst_33_100_80
example : regBoundInst (.fp (.fpSqrt 100 100):HolInst 80) 100 := by simp [regBoundInst]

-- rb_inst_34_0_80
example : regBoundInst (.fp (.fpAdd 100 100 100):HolInst 80) 0 := by simp [regBoundInst]

-- rb_inst_34_100_80
example : regBoundInst (.fp (.fpAdd 100 100 100):HolInst 80) 100 := by simp [regBoundInst]

-- rb_inst_35_0_80
example : regBoundInst (.fp (.fpSub 100 100 100):HolInst 80) 0 := by simp [regBoundInst]

-- rb_inst_35_100_80
example : regBoundInst (.fp (.fpSub 100 100 100):HolInst 80) 100 := by simp [regBoundInst]

-- rb_inst_36_0_80
example : regBoundInst (.fp (.fpMul 100 100 100):HolInst 80) 0 := by simp [regBoundInst]

-- rb_inst_36_100_80
example : regBoundInst (.fp (.fpMul 100 100 100):HolInst 80) 100 := by simp [regBoundInst]

-- rb_inst_37_0_80
example : regBoundInst (.fp (.fpDiv 100 100 100):HolInst 80) 0 := by simp [regBoundInst]

-- rb_inst_37_100_80
example : regBoundInst (.fp (.fpDiv 100 100 100):HolInst 80) 100 := by simp [regBoundInst]

-- rb_inst_38_0_80
example : regBoundInst (.fp (.fpFma 100 100 100):HolInst 80) 0 := by simp [regBoundInst]

-- rb_inst_38_100_80
example : regBoundInst (.fp (.fpFma 100 100 100):HolInst 80) 100 := by simp [regBoundInst]

-- rb_inst_39_0_80
example : regBoundInst (.fp (.fpMov 100 100):HolInst 80) 0 := by simp [regBoundInst]

-- rb_inst_39_100_80
example : regBoundInst (.fp (.fpMov 100 100):HolInst 80) 100 := by simp [regBoundInst]

-- rb_inst_40_0_80
example : regBoundInst (.fp (.fpToInt 100 100):HolInst 80) 0 := by simp [regBoundInst]

-- rb_inst_40_100_80
example : regBoundInst (.fp (.fpToInt 100 100):HolInst 80) 100 := by simp [regBoundInst]

-- rb_inst_41_0_80
example : regBoundInst (.fp (.fpFromInt 100 100):HolInst 80) 0 := by simp [regBoundInst]

-- rb_inst_41_100_80
example : regBoundInst (.fp (.fpFromInt 100 100):HolInst 80) 100 := by simp [regBoundInst]

-- rb_inst_42_2_80
example : ¬ regBoundInst (.fp (.fpMovToReg 1 2 100):HolInst 80) 2 := by simp [regBoundInst]

-- rb_inst_42_3_80
example : regBoundInst (.fp (.fpMovToReg 1 2 100):HolInst 80) 3 := by simp [regBoundInst]

-- rb_inst_43_2_80
example : ¬ regBoundInst (.fp (.fpMovFromReg 100 1 2):HolInst 80) 2 := by simp [regBoundInst]

-- rb_inst_43_3_80
example : regBoundInst (.fp (.fpMovFromReg 100 1 2):HolInst 80) 3 := by simp [regBoundInst]

-- rb_prog_44_0_80
example : regBound (.skip:HolProg 80) 0 := by simp [regBound]

-- rb_prog_44_100_80
example : regBound (.skip:HolProg 80) 100 := by simp [regBound]

-- rb_prog_45_1_80
example : ¬ regBound (.inst (.const 1 255):HolProg 80) 1 := by simp [regBound, regBoundInst]

-- rb_prog_45_2_80
example : regBound (.inst (.const 1 255):HolProg 80) 2 := by simp [regBound, regBoundInst]

-- rb_prog_46_1_80
example : ¬ regBound (.get 1 .currHeap:HolProg 80) 1 := by simp [regBound]

-- rb_prog_46_2_80
example : regBound (.get 1 .currHeap:HolProg 80) 2 := by simp [regBound]

-- rb_prog_47_1_80
example : ¬ regBound (.set .currHeap 1:HolProg 80) 1 := by simp [regBound]

-- rb_prog_47_2_80
example : regBound (.set .currHeap 1:HolProg 80) 2 := by simp [regBound]

-- rb_prog_48_0_80
example : ¬ regBound (.set .bitmapBase 1:HolProg 80) 0 := by simp [regBound]

-- rb_prog_48_100_80
example : ¬ regBound (.set .bitmapBase 1:HolProg 80) 100 := by simp [regBound]

-- rb_prog_49_2_80
example : ¬ regBound (.opCurrHeap .add 1 2:HolProg 80) 2 := by simp [regBound]

-- rb_prog_49_3_80
example : regBound (.opCurrHeap .add 1 2:HolProg 80) 3 := by simp [regBound]

-- rb_prog_50_0_80
example : regBound (.call none (.inl 999) (some (.halt 100,999,999)):HolProg 80) 0 := by simp [regBound]

-- rb_prog_50_100_80
example : regBound (.call none (.inl 999) (some (.halt 100,999,999)):HolProg 80) 100 := by simp [regBound]

-- rb_prog_51_2_80
example : ¬ regBound (.call none (.inr 2) none:HolProg 80) 2 := by simp [regBound]

-- rb_prog_51_3_80
example : regBound (.call none (.inr 2) none:HolProg 80) 3 := by simp [regBound]

-- rb_prog_52_3_80
example : ¬ regBound (.call (some (.halt 1,2,999,999)) (.inl 999) (some (.halt 3,999,999)):HolProg 80) 3 := by simp [regBound]

-- rb_prog_52_4_80
example : regBound (.call (some (.halt 1,2,999,999)) (.inl 999) (some (.halt 3,999,999)):HolProg 80) 4 := by simp [regBound]

-- rb_prog_53_2_80
example : ¬ regBound (.seq (.halt 1) (.halt 2):HolProg 80) 2 := by simp [regBound]

-- rb_prog_53_3_80
example : regBound (.seq (.halt 1) (.halt 2):HolProg 80) 3 := by simp [regBound]

-- rb_prog_54_3_80
example : ¬ regBound (.ite .equal 1 (.reg 2) .skip (.halt 3):HolProg 80) 3 := by simp [regBound]

-- rb_prog_54_4_80
example : regBound (.ite .equal 1 (.reg 2) .skip (.halt 3):HolProg 80) 4 := by simp [regBound]

-- rb_prog_55_1_80
example : ¬ regBound (.ite .equal 1 (.imm 255) .skip .skip:HolProg 80) 1 := by simp [regBound]

-- rb_prog_55_2_80
example : regBound (.ite .equal 1 (.imm 255) .skip .skip:HolProg 80) 2 := by simp [regBound]

-- rb_prog_56_2_80
example : ¬ regBound (.loop (.halt 2):HolProg 80) 2 := by simp [regBound]

-- rb_prog_56_3_80
example : regBound (.loop (.halt 2):HolProg 80) 3 := by simp [regBound]

-- rb_prog_57_2_80
example : ¬ regBound (.jumpLower 1 2 999:HolProg 80) 2 := by simp [regBound]

-- rb_prog_57_3_80
example : regBound (.jumpLower 1 2 999:HolProg 80) 3 := by simp [regBound]

-- rb_prog_58_0_80
example : regBound (.alloc 999:HolProg 80) 0 := by simp [regBound]

-- rb_prog_58_100_80
example : regBound (.alloc 999:HolProg 80) 100 := by simp [regBound]

-- rb_prog_59_3_80
example : ¬ regBound (.storeConsts 0 0 (some 999):HolProg 80) 3 := by simp [regBound]

-- rb_prog_59_4_80
example : regBound (.storeConsts 0 0 (some 999):HolProg 80) 4 := by simp [regBound]

-- rb_prog_60_1_80
example : ¬ regBound (.raise 1:HolProg 80) 1 := by simp [regBound]

-- rb_prog_60_2_80
example : regBound (.raise 1:HolProg 80) 2 := by simp [regBound]

-- rb_prog_61_1_80
example : ¬ regBound (.ret 1:HolProg 80) 1 := by simp [regBound]

-- rb_prog_61_2_80
example : regBound (.ret 1:HolProg 80) 2 := by simp [regBound]

-- rb_prog_62_0_80
example : regBound (.break 999:HolProg 80) 0 := by simp [regBound]

-- rb_prog_62_100_80
example : regBound (.break 999:HolProg 80) 100 := by simp [regBound]

-- rb_prog_63_0_80
example : regBound (.continue 999:HolProg 80) 0 := by simp [regBound]

-- rb_prog_63_100_80
example : regBound (.continue 999:HolProg 80) 100 := by simp [regBound]

-- rb_prog_64_5_80
example : ¬ regBound (.ffi (Flapjack.Basis.Pure.MlString.ofString "x") 1 2 3 4 5:HolProg 80) 5 := by simp [regBound]

-- rb_prog_64_6_80
example : regBound (.ffi (Flapjack.Basis.Pure.MlString.ofString "x") 1 2 3 4 5:HolProg 80) 6 := by simp [regBound]

-- rb_prog_65_0_80
example : regBound (.tick:HolProg 80) 0 := by simp [regBound]

-- rb_prog_65_100_80
example : regBound (.tick:HolProg 80) 100 := by simp [regBound]

-- rb_prog_66_1_80
example : ¬ regBound (.locValue 1 999 999:HolProg 80) 1 := by simp [regBound]

-- rb_prog_66_2_80
example : regBound (.locValue 1 999 999:HolProg 80) 2 := by simp [regBound]

-- rb_prog_67_5_80
example : ¬ regBound (.install 1 2 3 4 5:HolProg 80) 5 := by simp [regBound]

-- rb_prog_67_6_80
example : regBound (.install 1 2 3 4 5:HolProg 80) 6 := by simp [regBound]

-- rb_prog_68_2_80
example : ¬ regBound (.shMemOp .load16 1 (.addr 2 255):HolProg 80) 2 := by simp [regBound]

-- rb_prog_68_3_80
example : regBound (.shMemOp .load16 1 (.addr 2 255):HolProg 80) 3 := by simp [regBound]

-- rb_prog_69_2_80
example : ¬ regBound (.codeBufferWrite 1 2:HolProg 80) 2 := by simp [regBound]

-- rb_prog_69_3_80
example : regBound (.codeBufferWrite 1 2:HolProg 80) 3 := by simp [regBound]

-- rb_prog_70_2_80
example : ¬ regBound (.dataBufferWrite 1 2:HolProg 80) 2 := by simp [regBound]

-- rb_prog_70_3_80
example : regBound (.dataBufferWrite 1 2:HolProg 80) 3 := by simp [regBound]

-- rb_prog_71_0_80
example : regBound (.rawCall 999:HolProg 80) 0 := by simp [regBound]

-- rb_prog_71_100_80
example : regBound (.rawCall 999:HolProg 80) 100 := by simp [regBound]

-- rb_prog_72_0_80
example : regBound (.stackAlloc 999:HolProg 80) 0 := by simp [regBound]

-- rb_prog_72_100_80
example : regBound (.stackAlloc 999:HolProg 80) 100 := by simp [regBound]

-- rb_prog_73_0_80
example : regBound (.stackFree 999:HolProg 80) 0 := by simp [regBound]

-- rb_prog_73_100_80
example : regBound (.stackFree 999:HolProg 80) 100 := by simp [regBound]

-- rb_prog_74_1_80
example : ¬ regBound (.stackStore 1 999:HolProg 80) 1 := by simp [regBound]

-- rb_prog_74_2_80
example : regBound (.stackStore 1 999:HolProg 80) 2 := by simp [regBound]

-- rb_prog_75_999_80
example : ¬ regBound (.stackStore 999 1:HolProg 80) 999 := by simp [regBound]

-- rb_prog_75_1000_80
example : regBound (.stackStore 999 1:HolProg 80) 1000 := by simp [regBound]

-- rb_prog_76_1_80
example : ¬ regBound (.stackLoad 1 999:HolProg 80) 1 := by simp [regBound]

-- rb_prog_76_2_80
example : regBound (.stackLoad 1 999:HolProg 80) 2 := by simp [regBound]

-- rb_prog_77_999_80
example : ¬ regBound (.stackLoad 999 1:HolProg 80) 999 := by simp [regBound]

-- rb_prog_77_1000_80
example : regBound (.stackLoad 999 1:HolProg 80) 1000 := by simp [regBound]

-- rb_prog_78_2_80
example : ¬ regBound (.stackStoreAny 1 2:HolProg 80) 2 := by simp [regBound]

-- rb_prog_78_3_80
example : regBound (.stackStoreAny 1 2:HolProg 80) 3 := by simp [regBound]

-- rb_prog_79_2_80
example : ¬ regBound (.stackLoadAny 1 2:HolProg 80) 2 := by simp [regBound]

-- rb_prog_79_3_80
example : regBound (.stackLoadAny 1 2:HolProg 80) 3 := by simp [regBound]

-- rb_prog_80_1_80
example : ¬ regBound (.stackGetSize 1:HolProg 80) 1 := by simp [regBound]

-- rb_prog_80_2_80
example : regBound (.stackGetSize 1:HolProg 80) 2 := by simp [regBound]

-- rb_prog_81_1_80
example : ¬ regBound (.stackSetSize 1:HolProg 80) 1 := by simp [regBound]

-- rb_prog_81_2_80
example : regBound (.stackSetSize 1:HolProg 80) 2 := by simp [regBound]

-- rb_prog_82_2_80
example : ¬ regBound (.bitmapLoad 1 2:HolProg 80) 2 := by simp [regBound]

-- rb_prog_82_3_80
example : regBound (.bitmapLoad 1 2:HolProg 80) 3 := by simp [regBound]

-- rb_prog_83_1_80
example : ¬ regBound (.halt 1:HolProg 80) 1 := by simp [regBound]

-- rb_prog_83_2_80
example : regBound (.halt 1:HolProg 80) 2 := by simp [regBound]

example {width : Nat} [NeZero width] (handler : Option (HolProg width × Nat × Nat)) (label bound : Nat) :
    regBound (.call none (.inl label) handler : HolProg width) bound ↔ True := by simp [regBound]
example {width : Nat} [NeZero width] (first second bound : Nat) :
    regBound (.stackLoad first second : HolProg width) bound ↔ first < bound := Iff.rfl
example {width : Nat} [NeZero width] (value : BitVec width) (bound : Nat) :
    regBoundExp (.const value) bound ↔ True := by simp [regBoundExp]

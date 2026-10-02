import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocArgs.Instructions

namespace Flapjack.Test.WordToStackAllocInstructionsParity

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps

open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm

open Flapjack.WordToStackProofs.AllocArgs

/- Fresh original regression boundary: word_to_stack_alloc_instructions_probe.out. Not cross-language equivalence. -/

-- aai_1_0_skip
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_const
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.const 999 5)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_binop_imm
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.binop .add 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_binop_reg
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.binop .xor 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_shift_imm
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.shift .lsl 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_shift_reg
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.shift .lsr 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_div
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.div 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_long_mul
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.longMul 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_long_div
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.longDiv 999 7 3 5 8))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_carry
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.addCarry 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_add_overflow
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.addOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_sub_overflow
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.subOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_load
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.mem .load 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_load8
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.mem .load8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_load16
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.mem .load16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_load32
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.mem .load32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_store
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.mem .store 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_store8
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.mem .store8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_store16
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.mem .store16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_store32
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.mem .store32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpless
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpLess 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fplessequal
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpLessEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpequal
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpabs
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpAbs 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpneg
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpNeg 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpsqrt
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpSqrt 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpadd
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpAdd 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpsub
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpSub 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpmul
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMul 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpdiv
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpDiv 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpfma
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpFma 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpmov
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMov 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpmovtoreg
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpmovfromreg
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fptoint
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpToInt 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpfromint
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpFromInt 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpmovtoreg1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpmovfromreg1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpmovtoreg32
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpmovfromreg32
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpmovtoreg80
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_fpmovfromreg80
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Load_0
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Load_1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Load_2
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Load8_0
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Load8_1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Load8_2
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Load16_0
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Load16_1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Load16_2
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Load32_0
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Load32_1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Load32_2
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Store_0
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Store_1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Store_2
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Store8_0
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Store8_1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Store8_2
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Store16_0
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Store16_1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Store16_2
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Store32_0
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Store32_1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_0_share_Store32_2
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_skip
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_const
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.const 999 5)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_binop_imm
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.binop .add 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_binop_reg
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.binop .xor 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_shift_imm
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.shift .lsl 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_shift_reg
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.shift .lsr 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_div
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.div 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_long_mul
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.longMul 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_long_div
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.longDiv 999 7 3 5 8))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_carry
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.addCarry 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_add_overflow
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.addOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_sub_overflow
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.arith (.subOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_load
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.mem .load 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_load8
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.mem .load8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_load16
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.mem .load16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_load32
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.mem .load32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_store
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.mem .store 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_store8
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.mem .store8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_store16
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.mem .store16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_store32
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.mem .store32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpless
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpLess 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fplessequal
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpLessEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpequal
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpabs
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpAbs 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpneg
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpNeg 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpsqrt
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpSqrt 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpadd
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpAdd 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpsub
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpSub 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpmul
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMul 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpdiv
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpDiv 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpfma
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpFma 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpmov
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMov 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpmovtoreg
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpmovfromreg
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fptoint
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpToInt 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpfromint
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpFromInt 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpmovtoreg1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpmovfromreg1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpmovtoreg32
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpmovfromreg32
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpmovtoreg80
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_fpmovfromreg80
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Load_0
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Load_1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Load_2
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Load8_0
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Load8_1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Load8_2
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Load16_0
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Load16_1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Load16_2
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Load32_0
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Load32_1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Load32_2
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Store_0
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Store_1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Store_2
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Store8_0
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Store8_1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Store8_2
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Store16_0
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Store16_1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Store16_2
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Store32_0
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Store32_1
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_1_1_share_Store32_2
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_skip
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_const
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.const 999 5)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_binop_imm
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.binop .add 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_binop_reg
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.binop .xor 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_shift_imm
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.shift .lsl 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_shift_reg
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.shift .lsr 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_div
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.div 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_long_mul
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.longMul 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_long_div
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.longDiv 999 7 3 5 8))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_carry
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.addCarry 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_add_overflow
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.addOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_sub_overflow
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.subOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_load
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.mem .load 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_load8
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.mem .load8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_load16
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.mem .load16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_load32
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.mem .load32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_store
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.mem .store 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_store8
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.mem .store8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_store16
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.mem .store16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_store32
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.mem .store32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpless
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpLess 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fplessequal
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpLessEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpequal
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpabs
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpAbs 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpneg
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpNeg 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpsqrt
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpSqrt 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpadd
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpAdd 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpsub
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpSub 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpmul
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMul 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpdiv
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpDiv 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpfma
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpFma 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpmov
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMov 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpmovtoreg
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpmovfromreg
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fptoint
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpToInt 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpfromint
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpFromInt 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpmovtoreg1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpmovfromreg1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpmovtoreg32
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpmovfromreg32
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpmovtoreg80
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_fpmovfromreg80
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Load_0
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Load_1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Load_2
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Load8_0
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Load8_1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Load8_2
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Load16_0
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Load16_1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Load16_2
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Load32_0
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Load32_1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Load32_2
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Store_0
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Store_1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Store_2
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Store8_0
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Store8_1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Store8_2
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Store16_0
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Store16_1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Store16_2
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Store32_0
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Store32_1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_0_share_Store32_2
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_skip
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_const
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.const 999 5)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_binop_imm
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.binop .add 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_binop_reg
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.binop .xor 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_shift_imm
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.shift .lsl 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_shift_reg
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.shift .lsr 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_div
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.div 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_long_mul
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.longMul 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_long_div
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.longDiv 999 7 3 5 8))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_carry
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.addCarry 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_add_overflow
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.addOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_sub_overflow
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.arith (.subOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_load
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.mem .load 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_load8
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.mem .load8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_load16
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.mem .load16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_load32
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.mem .load32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_store
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.mem .store 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_store8
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.mem .store8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_store16
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.mem .store16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_store32
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.mem .store32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpless
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpLess 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fplessequal
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpLessEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpequal
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpabs
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpAbs 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpneg
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpNeg 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpsqrt
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpSqrt 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpadd
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpAdd 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpsub
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpSub 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpmul
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMul 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpdiv
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpDiv 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpfma
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpFma 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpmov
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMov 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpmovtoreg
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpmovfromreg
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fptoint
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpToInt 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpfromint
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpFromInt 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpmovtoreg1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpmovfromreg1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpmovtoreg32
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpmovfromreg32
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpmovtoreg80
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_fpmovfromreg80
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Load_0
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Load_1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Load_2
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Load8_0
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Load8_1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Load8_2
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Load16_0
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Load16_1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Load16_2
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Load32_0
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Load32_1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Load32_2
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Store_0
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Store_1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Store_2
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Store8_0
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Store8_1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Store8_2
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Store16_0
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Store16_1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Store16_2
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Store32_0
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Store32_1
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_2_1_share_Store32_2
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_skip
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_const
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.const 999 5)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_binop_imm
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.binop .add 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_binop_reg
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.binop .xor 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_shift_imm
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.shift .lsl 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_shift_reg
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.shift .lsr 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_div
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.div 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_long_mul
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.longMul 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_long_div
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.longDiv 999 7 3 5 8))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_carry
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.addCarry 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_add_overflow
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.addOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_sub_overflow
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.subOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_load
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.mem .load 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_load8
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.mem .load8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_load16
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.mem .load16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_load32
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.mem .load32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_store
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.mem .store 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_store8
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.mem .store8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_store16
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.mem .store16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_store32
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.mem .store32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpless
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpLess 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fplessequal
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpLessEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpequal
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpabs
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpAbs 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpneg
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpNeg 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpsqrt
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpSqrt 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpadd
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpAdd 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpsub
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpSub 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpmul
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMul 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpdiv
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpDiv 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpfma
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpFma 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpmov
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMov 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpmovtoreg
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpmovfromreg
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fptoint
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpToInt 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpfromint
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpFromInt 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpmovtoreg1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpmovfromreg1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpmovtoreg32
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpmovfromreg32
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpmovtoreg80
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_fpmovfromreg80
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Load_0
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Load_1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Load_2
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Load8_0
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Load8_1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Load8_2
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Load16_0
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Load16_1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Load16_2
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Load32_0
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Load32_1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Load32_2
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Store_0
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Store_1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Store_2
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Store8_0
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Store8_1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Store8_2
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Store16_0
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Store16_1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Store16_2
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Store32_0
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Store32_1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_0_share_Store32_2
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_skip
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_const
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.const 999 5)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_binop_imm
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.binop .add 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_binop_reg
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.binop .xor 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_shift_imm
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.shift .lsl 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_shift_reg
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.shift .lsr 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_div
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.div 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_long_mul
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.longMul 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_long_div
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.longDiv 999 7 3 5 8))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_carry
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.addCarry 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_add_overflow
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.addOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_sub_overflow
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.arith (.subOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_load
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.mem .load 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_load8
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.mem .load8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_load16
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.mem .load16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_load32
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.mem .load32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_store
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.mem .store 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_store8
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.mem .store8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_store16
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.mem .store16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_store32
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.mem .store32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpless
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpLess 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fplessequal
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpLessEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpequal
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpabs
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpAbs 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpneg
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpNeg 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpsqrt
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpSqrt 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpadd
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpAdd 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpsub
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpSub 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpmul
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMul 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpdiv
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpDiv 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpfma
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpFma 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpmov
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMov 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpmovtoreg
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpmovfromreg
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fptoint
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpToInt 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpfromint
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpFromInt 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpmovtoreg1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpmovfromreg1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpmovtoreg32
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpmovfromreg32
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpmovtoreg80
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_fpmovfromreg80
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Load_0
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Load_1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Load_2
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Load8_0
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Load8_1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Load8_2
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Load16_0
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Load16_1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Load16_2
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Load32_0
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Load32_1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Load32_2
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Store_0
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Store_1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Store_2
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Store8_0
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Store8_1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Store8_2
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Store16_0
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Store16_1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Store16_2
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Store32_0
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Store32_1
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_8_1_share_Store32_2
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_skip
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_const
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.const 999 5)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_binop_imm
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.binop .add 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_binop_reg
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.binop .xor 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_shift_imm
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.shift .lsl 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_shift_reg
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.shift .lsr 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_div
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.div 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_long_mul
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.longMul 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_long_div
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.longDiv 999 7 3 5 8))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_carry
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.addCarry 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_add_overflow
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.addOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_sub_overflow
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.subOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_load
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.mem .load 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_load8
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.mem .load8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_load16
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.mem .load16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_load32
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.mem .load32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_store
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.mem .store 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_store8
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.mem .store8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_store16
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.mem .store16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_store32
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.mem .store32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpless
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpLess 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fplessequal
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpLessEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpequal
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpabs
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpAbs 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpneg
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpNeg 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpsqrt
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpSqrt 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpadd
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpAdd 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpsub
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpSub 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpmul
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMul 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpdiv
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpDiv 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpfma
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpFma 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpmov
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMov 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpmovtoreg
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpmovfromreg
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fptoint
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpToInt 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpfromint
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpFromInt 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpmovtoreg1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpmovfromreg1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpmovtoreg32
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpmovfromreg32
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpmovtoreg80
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_fpmovfromreg80
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Load_0
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Load_1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Load_2
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Load8_0
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Load8_1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Load8_2
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Load16_0
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Load16_1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Load16_2
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Load32_0
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Load32_1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Load32_2
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Store_0
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Store_1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Store_2
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Store8_0
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Store8_1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Store8_2
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Store16_0
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Store16_1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Store16_2
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Store32_0
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Store32_1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_0_share_Store32_2
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_skip
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_const
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.const 999 5)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_binop_imm
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.binop .add 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_binop_reg
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.binop .xor 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_shift_imm
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.shift .lsl 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_shift_reg
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.shift .lsr 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_div
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.div 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_long_mul
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.longMul 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_long_div
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.longDiv 999 7 3 5 8))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_carry
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.addCarry 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_add_overflow
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.addOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_sub_overflow
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.arith (.subOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_load
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.mem .load 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_load8
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.mem .load8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_load16
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.mem .load16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_load32
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.mem .load32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_store
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.mem .store 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_store8
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.mem .store8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_store16
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.mem .store16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_store32
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.mem .store32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpless
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpLess 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fplessequal
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpLessEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpequal
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpabs
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpAbs 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpneg
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpNeg 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpsqrt
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpSqrt 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpadd
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpAdd 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpsub
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpSub 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpmul
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMul 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpdiv
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpDiv 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpfma
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpFma 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpmov
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMov 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpmovtoreg
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpmovfromreg
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fptoint
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpToInt 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpfromint
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpFromInt 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpmovtoreg1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpmovfromreg1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpmovtoreg32
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpmovfromreg32
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpmovtoreg80
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_fpmovfromreg80
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Load_0
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Load_1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Load_2
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Load8_0
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Load8_1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Load8_2
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Load16_0
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Load16_1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Load16_2
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Load32_0
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Load32_1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Load32_2
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Store_0
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Store_1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Store_2
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Store8_0
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Store8_1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Store8_2
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Store16_0
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Store16_1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Store16_2
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Store32_0
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Store32_1
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_64_1_share_Store32_2
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_skip
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_const
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.const 999 5)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_binop_imm
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.binop .add 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_binop_reg
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.binop .xor 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_shift_imm
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.shift .lsl 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_shift_reg
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.shift .lsr 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_div
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.div 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_long_mul
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.longMul 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_long_div
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.longDiv 999 7 3 5 8))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_carry
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.addCarry 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_add_overflow
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.addOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_sub_overflow
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.subOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_load
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.mem .load 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_load8
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.mem .load8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_load16
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.mem .load16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_load32
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.mem .load32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_store
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.mem .store 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_store8
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.mem .store8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_store16
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.mem .store16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_store32
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.mem .store32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpless
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpLess 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fplessequal
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpLessEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpequal
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpabs
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpAbs 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpneg
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpNeg 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpsqrt
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpSqrt 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpadd
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpAdd 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpsub
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpSub 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpmul
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMul 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpdiv
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpDiv 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpfma
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpFma 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpmov
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMov 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpmovtoreg
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpmovfromreg
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fptoint
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpToInt 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpfromint
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpFromInt 999 3))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpmovtoreg1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpmovfromreg1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpmovtoreg32
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpmovfromreg32
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpmovtoreg80
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_fpmovfromreg80
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Load_0
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Load_1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Load_2
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Load8_0
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Load8_1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Load8_2
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Load16_0
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Load16_1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Load16_2
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Load32_0
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Load32_1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Load32_2
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Store_0
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Store_1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Store_2
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Store8_0
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Store8_1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Store8_2
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Store16_0
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Store16_1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Store16_2
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Store32_0
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Store32_1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_0_share_Store32_2
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_skip
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_const
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.const 999 5)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_binop_imm
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.binop .add 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_binop_reg
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.binop .xor 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_shift_imm
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.shift .lsl 999 3 (.imm 9)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_shift_reg
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.shift .lsr 999 3 (.reg 5)))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_div
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.div 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_long_mul
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.longMul 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_long_div
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.longDiv 999 7 3 5 8))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_carry
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.addCarry 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_add_overflow
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.addOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_sub_overflow
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.arith (.subOverflow 999 7 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_load
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.mem .load 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_load8
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.mem .load8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_load16
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.mem .load16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_load32
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.mem .load32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_store
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.mem .store 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_store8
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.mem .store8 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_store16
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.mem .store16 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_store32
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.mem .store32 999 (.addr 3 9))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpless
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpLess 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fplessequal
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpLessEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpequal
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpEqual 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpabs
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpAbs 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpneg
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpNeg 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpsqrt
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpSqrt 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpadd
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpAdd 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpsub
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpSub 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpmul
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMul 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpdiv
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpDiv 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpfma
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpFma 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpmov
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMov 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpmovtoreg
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpmovfromreg
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fptoint
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpToInt 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpfromint
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpFromInt 999 3))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpmovtoreg1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpmovfromreg1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpmovtoreg32
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpmovfromreg32
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpmovtoreg80
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMovToReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_fpmovfromreg80
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.inst (.fp (.fpMovFromReg 999 3 5))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Load_0
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Load_1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Load_2
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Load8_0
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Load8_1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Load8_2
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Load16_0
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Load16_1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Load16_2
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Load32_0
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Load32_1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Load32_2
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .load32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Store_0
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Store_1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Store_2
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Store8_0
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Store8_1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Store8_2
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store8 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Store16_0
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Store16_1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Store16_2
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store16 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Store32_0
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Store32_1
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.op .add [.var 999,.const 9])) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aai_80_1_share_Store32_2
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.shareInst .store32 1180591620717411303427 (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

example {width : Nat} [NeZero width] (conf : AsmConfigExact width) (perf : Bool) (i : WordLangInst (BitVec width)) (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat) (h : perf=false) : allocArg (compNative conf perf (.inst i) bs frame).1 := wordToStackAllocArgInst conf perf i bs frame h

example {width : Nat} [NeZero width] (conf : AsmConfigExact width) (perf : Bool) (op : HolMemop) (v : Nat) (exp : WordLangExpHOL (BitVec width)) (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat) (h : perf=false) : allocArg (compNative conf perf (.shareInst op v exp) bs frame).1 := wordToStackAllocArgShareInst conf perf op v exp bs frame h

end Flapjack.Test.WordToStackAllocInstructionsParity

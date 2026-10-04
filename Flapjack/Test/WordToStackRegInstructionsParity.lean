import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundInstructions

namespace Flapjack.Test.WordToStackRegInstructionsParity
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open Flapjack.WordToStackProofs.RegisterBoundInstructions
/- Same-input original guard and direct target EVAL observations from
word_to_stack_reg_instructions_probe.out. Regression evidence, not equivalence. -/

-- rbi_1_0_skip_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.skip)) = true := by cbv
-- rbi_1_0_skip_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_const_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.const 998 4)) = true := by cbv
-- rbi_1_0_const_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.const 998 4)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_binop_imm_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.arith (.binop .add 998 2 (.imm 8)))) = true := by cbv
-- rbi_1_0_binop_imm_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.binop .add 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_binop_reg_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.arith (.binop .xor 998 2 (.reg 4)))) = true := by cbv
-- rbi_1_0_binop_reg_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.binop .xor 998 2 (.reg 4)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_shift_imm_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) = true := by cbv
-- rbi_1_0_shift_imm_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_shift_reg_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) = true := by cbv
-- rbi_1_0_shift_reg_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_div_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.arith (.div 998 2 4))) = true := by cbv
-- rbi_1_0_div_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.div 998 2 4))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_long_mul_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.arith (.longMul 6 0 0 4))) = true := by cbv
-- rbi_1_0_long_mul_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.longMul 6 0 0 4))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_long_div_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.arith (.longDiv 0 6 6 0 8))) = true := by cbv
-- rbi_1_0_long_div_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.longDiv 0 6 6 0 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_carry_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.arith (.addCarry 998 6 2 0))) = true := by cbv
-- rbi_1_0_carry_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.addCarry 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_add_overflow_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.arith (.addOverflow 998 6 2 0))) = true := by cbv
-- rbi_1_0_add_overflow_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.addOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_sub_overflow_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.arith (.subOverflow 998 6 2 0))) = true := by cbv
-- rbi_1_0_sub_overflow_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.subOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_load_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.mem .load 998 (.addr 2 8))) = true := by cbv
-- rbi_1_0_load_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.mem .load 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_load8_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.mem .load8 998 (.addr 2 8))) = true := by cbv
-- rbi_1_0_load8_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.mem .load8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_load16_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.mem .load16 998 (.addr 2 8))) = true := by cbv
-- rbi_1_0_load16_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.mem .load16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_load32_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.mem .load32 998 (.addr 2 8))) = true := by cbv
-- rbi_1_0_load32_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.mem .load32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_store_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.mem .store 998 (.addr 2 8))) = true := by cbv
-- rbi_1_0_store_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.mem .store 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_store8_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.mem .store8 998 (.addr 2 8))) = true := by cbv
-- rbi_1_0_store8_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.mem .store8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_store16_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.mem .store16 998 (.addr 2 8))) = true := by cbv
-- rbi_1_0_store16_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.mem .store16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_store32_guard
example : postAllocConventionsHOL (width := 1) 4 (.inst (.mem .store32 998 (.addr 2 8))) = true := by cbv
-- rbi_1_0_store32_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.mem .store32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_0_fpless_guard


-- rbi_1_0_fplessequal_guard


-- rbi_1_0_fpequal_guard


-- rbi_1_0_fpabs_guard


-- rbi_1_0_fpneg_guard


-- rbi_1_0_fpsqrt_guard


-- rbi_1_0_fpadd_guard


-- rbi_1_0_fpsub_guard


-- rbi_1_0_fpmul_guard


-- rbi_1_0_fpdiv_guard


-- rbi_1_0_fpfma_guard


-- rbi_1_0_fpmov_guard


-- rbi_1_0_fpmovtoreg_guard


-- rbi_1_0_fpmovfromreg_guard


-- rbi_1_0_fptoint_guard


-- rbi_1_0_fpfromint_guard


-- rbi_1_0_fpmovtoreg1_guard


-- rbi_1_0_fpmovfromreg1_guard


-- rbi_1_0_fpmovtoreg32_guard


-- rbi_1_0_fpmovfromreg32_guard


-- rbi_1_0_fpmovtoreg80_guard


-- rbi_1_0_fpmovfromreg80_guard


-- rbi_1_0_share_Load_0_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .load 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_1_0_share_Load_0_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Load_1_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_1_0_share_Load_1_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Load_2_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .load 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_1_0_share_Load_2_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Load8_0_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .load8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_1_0_share_Load8_0_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Load8_1_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_1_0_share_Load8_1_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Load8_2_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .load8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_1_0_share_Load8_2_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Load16_0_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .load16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_1_0_share_Load16_0_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Load16_1_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_1_0_share_Load16_1_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Load16_2_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .load16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_1_0_share_Load16_2_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Load32_0_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .load32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_1_0_share_Load32_0_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Load32_1_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_1_0_share_Load32_1_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Load32_2_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .load32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_1_0_share_Load32_2_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Store_0_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .store 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_1_0_share_Store_0_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Store_1_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_1_0_share_Store_1_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Store_2_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .store 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_1_0_share_Store_2_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Store8_0_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .store8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_1_0_share_Store8_0_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Store8_1_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_1_0_share_Store8_1_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Store8_2_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .store8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_1_0_share_Store8_2_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Store16_0_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .store16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_1_0_share_Store16_0_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Store16_1_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_1_0_share_Store16_1_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Store16_2_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .store16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_1_0_share_Store16_2_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Store32_0_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .store32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_1_0_share_Store32_0_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Store32_1_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_1_0_share_Store32_1_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_0_share_Store32_2_guard
example : postAllocConventionsHOL (width := 1) 4 (.shareInst .store32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_1_0_share_Store32_2_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_skip_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.skip)) = true := by cbv
-- rbi_1_1_skip_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_const_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.const 998 4)) = true := by cbv
-- rbi_1_1_const_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.const 998 4)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_binop_imm_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.arith (.binop .add 998 2 (.imm 8)))) = true := by cbv
-- rbi_1_1_binop_imm_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.binop .add 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_binop_reg_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.arith (.binop .xor 998 2 (.reg 4)))) = true := by cbv
-- rbi_1_1_binop_reg_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.binop .xor 998 2 (.reg 4)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_shift_imm_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) = true := by cbv
-- rbi_1_1_shift_imm_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_shift_reg_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) = true := by cbv
-- rbi_1_1_shift_reg_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_div_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.arith (.div 998 2 4))) = true := by cbv
-- rbi_1_1_div_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.div 998 2 4))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_long_mul_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.arith (.longMul 6 0 0 4))) = true := by cbv
-- rbi_1_1_long_mul_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.longMul 6 0 0 4))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_long_div_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.arith (.longDiv 0 6 6 0 8))) = true := by cbv
-- rbi_1_1_long_div_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.longDiv 0 6 6 0 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_carry_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.arith (.addCarry 998 6 2 0))) = true := by cbv
-- rbi_1_1_carry_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.addCarry 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_add_overflow_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.arith (.addOverflow 998 6 2 0))) = true := by cbv
-- rbi_1_1_add_overflow_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.addOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_sub_overflow_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.arith (.subOverflow 998 6 2 0))) = true := by cbv
-- rbi_1_1_sub_overflow_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.arith (.subOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_load_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.mem .load 998 (.addr 2 8))) = true := by cbv
-- rbi_1_1_load_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.mem .load 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_load8_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.mem .load8 998 (.addr 2 8))) = true := by cbv
-- rbi_1_1_load8_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.mem .load8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_load16_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.mem .load16 998 (.addr 2 8))) = true := by cbv
-- rbi_1_1_load16_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.mem .load16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_load32_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.mem .load32 998 (.addr 2 8))) = true := by cbv
-- rbi_1_1_load32_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.mem .load32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_store_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.mem .store 998 (.addr 2 8))) = true := by cbv
-- rbi_1_1_store_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.mem .store 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_store8_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.mem .store8 998 (.addr 2 8))) = true := by cbv
-- rbi_1_1_store8_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.mem .store8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_store16_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.mem .store16 998 (.addr 2 8))) = true := by cbv
-- rbi_1_1_store16_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.mem .store16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_store32_guard
example : postAllocConventionsHOL (width := 1) 8 (.inst (.mem .store32 998 (.addr 2 8))) = true := by cbv
-- rbi_1_1_store32_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.inst (.mem .store32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_1_1_fpless_guard


-- rbi_1_1_fplessequal_guard


-- rbi_1_1_fpequal_guard


-- rbi_1_1_fpabs_guard


-- rbi_1_1_fpneg_guard


-- rbi_1_1_fpsqrt_guard


-- rbi_1_1_fpadd_guard


-- rbi_1_1_fpsub_guard


-- rbi_1_1_fpmul_guard


-- rbi_1_1_fpdiv_guard


-- rbi_1_1_fpfma_guard


-- rbi_1_1_fpmov_guard


-- rbi_1_1_fpmovtoreg_guard


-- rbi_1_1_fpmovfromreg_guard


-- rbi_1_1_fptoint_guard


-- rbi_1_1_fpfromint_guard


-- rbi_1_1_fpmovtoreg1_guard


-- rbi_1_1_fpmovfromreg1_guard


-- rbi_1_1_fpmovtoreg32_guard


-- rbi_1_1_fpmovfromreg32_guard


-- rbi_1_1_fpmovtoreg80_guard


-- rbi_1_1_fpmovfromreg80_guard


-- rbi_1_1_share_Load_0_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .load 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_1_1_share_Load_0_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Load_1_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_1_1_share_Load_1_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Load_2_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .load 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_1_1_share_Load_2_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Load8_0_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .load8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_1_1_share_Load8_0_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Load8_1_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_1_1_share_Load8_1_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Load8_2_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .load8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_1_1_share_Load8_2_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Load16_0_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .load16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_1_1_share_Load16_0_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Load16_1_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_1_1_share_Load16_1_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Load16_2_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .load16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_1_1_share_Load16_2_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Load32_0_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .load32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_1_1_share_Load32_0_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Load32_1_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_1_1_share_Load32_1_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Load32_2_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .load32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_1_1_share_Load32_2_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Store_0_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .store 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_1_1_share_Store_0_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Store_1_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_1_1_share_Store_1_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Store_2_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .store 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_1_1_share_Store_2_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Store8_0_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .store8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_1_1_share_Store8_0_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Store8_1_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_1_1_share_Store8_1_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Store8_2_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .store8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_1_1_share_Store8_2_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Store16_0_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .store16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_1_1_share_Store16_0_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Store16_1_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_1_1_share_Store16_1_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Store16_2_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .store16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_1_1_share_Store16_2_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Store32_0_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .store32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_1_1_share_Store32_0_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Store32_1_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_1_1_share_Store32_1_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_1_1_share_Store32_2_guard
example : postAllocConventionsHOL (width := 1) 8 (.shareInst .store32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_1_1_share_Store32_2_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_skip_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.skip)) = true := by cbv
-- rbi_2_0_skip_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_const_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.const 998 4)) = true := by cbv
-- rbi_2_0_const_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.const 998 4)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_binop_imm_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.arith (.binop .add 998 2 (.imm 8)))) = true := by cbv
-- rbi_2_0_binop_imm_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.binop .add 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_binop_reg_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.arith (.binop .xor 998 2 (.reg 4)))) = true := by cbv
-- rbi_2_0_binop_reg_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.binop .xor 998 2 (.reg 4)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_shift_imm_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) = true := by cbv
-- rbi_2_0_shift_imm_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_shift_reg_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) = true := by cbv
-- rbi_2_0_shift_reg_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_div_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.arith (.div 998 2 4))) = true := by cbv
-- rbi_2_0_div_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.div 998 2 4))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_long_mul_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.arith (.longMul 6 0 0 4))) = true := by cbv
-- rbi_2_0_long_mul_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.longMul 6 0 0 4))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_long_div_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.arith (.longDiv 0 6 6 0 8))) = true := by cbv
-- rbi_2_0_long_div_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.longDiv 0 6 6 0 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_carry_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.arith (.addCarry 998 6 2 0))) = true := by cbv
-- rbi_2_0_carry_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.addCarry 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_add_overflow_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.arith (.addOverflow 998 6 2 0))) = true := by cbv
-- rbi_2_0_add_overflow_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.addOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_sub_overflow_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.arith (.subOverflow 998 6 2 0))) = true := by cbv
-- rbi_2_0_sub_overflow_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.subOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_load_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.mem .load 998 (.addr 2 8))) = true := by cbv
-- rbi_2_0_load_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.mem .load 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_load8_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.mem .load8 998 (.addr 2 8))) = true := by cbv
-- rbi_2_0_load8_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.mem .load8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_load16_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.mem .load16 998 (.addr 2 8))) = true := by cbv
-- rbi_2_0_load16_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.mem .load16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_load32_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.mem .load32 998 (.addr 2 8))) = true := by cbv
-- rbi_2_0_load32_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.mem .load32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_store_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.mem .store 998 (.addr 2 8))) = true := by cbv
-- rbi_2_0_store_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.mem .store 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_store8_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.mem .store8 998 (.addr 2 8))) = true := by cbv
-- rbi_2_0_store8_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.mem .store8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_store16_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.mem .store16 998 (.addr 2 8))) = true := by cbv
-- rbi_2_0_store16_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.mem .store16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_store32_guard
example : postAllocConventionsHOL (width := 2) 4 (.inst (.mem .store32 998 (.addr 2 8))) = true := by cbv
-- rbi_2_0_store32_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.mem .store32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_0_fpless_guard


-- rbi_2_0_fplessequal_guard


-- rbi_2_0_fpequal_guard


-- rbi_2_0_fpabs_guard


-- rbi_2_0_fpneg_guard


-- rbi_2_0_fpsqrt_guard


-- rbi_2_0_fpadd_guard


-- rbi_2_0_fpsub_guard


-- rbi_2_0_fpmul_guard


-- rbi_2_0_fpdiv_guard


-- rbi_2_0_fpfma_guard


-- rbi_2_0_fpmov_guard


-- rbi_2_0_fpmovtoreg_guard


-- rbi_2_0_fpmovfromreg_guard


-- rbi_2_0_fptoint_guard


-- rbi_2_0_fpfromint_guard


-- rbi_2_0_fpmovtoreg1_guard


-- rbi_2_0_fpmovfromreg1_guard


-- rbi_2_0_fpmovtoreg32_guard


-- rbi_2_0_fpmovfromreg32_guard


-- rbi_2_0_fpmovtoreg80_guard


-- rbi_2_0_fpmovfromreg80_guard


-- rbi_2_0_share_Load_0_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .load 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_2_0_share_Load_0_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Load_1_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_2_0_share_Load_1_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Load_2_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .load 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_2_0_share_Load_2_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Load8_0_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .load8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_2_0_share_Load8_0_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Load8_1_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_2_0_share_Load8_1_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Load8_2_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .load8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_2_0_share_Load8_2_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Load16_0_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .load16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_2_0_share_Load16_0_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Load16_1_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_2_0_share_Load16_1_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Load16_2_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .load16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_2_0_share_Load16_2_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Load32_0_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .load32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_2_0_share_Load32_0_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Load32_1_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_2_0_share_Load32_1_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Load32_2_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .load32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_2_0_share_Load32_2_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Store_0_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .store 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_2_0_share_Store_0_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Store_1_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_2_0_share_Store_1_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Store_2_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .store 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_2_0_share_Store_2_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Store8_0_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .store8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_2_0_share_Store8_0_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Store8_1_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_2_0_share_Store8_1_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Store8_2_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .store8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_2_0_share_Store8_2_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Store16_0_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .store16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_2_0_share_Store16_0_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Store16_1_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_2_0_share_Store16_1_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Store16_2_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .store16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_2_0_share_Store16_2_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Store32_0_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .store32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_2_0_share_Store32_0_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Store32_1_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_2_0_share_Store32_1_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_0_share_Store32_2_guard
example : postAllocConventionsHOL (width := 2) 4 (.shareInst .store32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_2_0_share_Store32_2_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_skip_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.skip)) = true := by cbv
-- rbi_2_1_skip_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_const_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.const 998 4)) = true := by cbv
-- rbi_2_1_const_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.const 998 4)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_binop_imm_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.arith (.binop .add 998 2 (.imm 8)))) = true := by cbv
-- rbi_2_1_binop_imm_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.binop .add 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_binop_reg_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.arith (.binop .xor 998 2 (.reg 4)))) = true := by cbv
-- rbi_2_1_binop_reg_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.binop .xor 998 2 (.reg 4)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_shift_imm_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) = true := by cbv
-- rbi_2_1_shift_imm_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_shift_reg_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) = true := by cbv
-- rbi_2_1_shift_reg_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_div_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.arith (.div 998 2 4))) = true := by cbv
-- rbi_2_1_div_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.div 998 2 4))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_long_mul_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.arith (.longMul 6 0 0 4))) = true := by cbv
-- rbi_2_1_long_mul_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.longMul 6 0 0 4))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_long_div_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.arith (.longDiv 0 6 6 0 8))) = true := by cbv
-- rbi_2_1_long_div_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.longDiv 0 6 6 0 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_carry_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.arith (.addCarry 998 6 2 0))) = true := by cbv
-- rbi_2_1_carry_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.addCarry 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_add_overflow_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.arith (.addOverflow 998 6 2 0))) = true := by cbv
-- rbi_2_1_add_overflow_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.addOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_sub_overflow_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.arith (.subOverflow 998 6 2 0))) = true := by cbv
-- rbi_2_1_sub_overflow_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.arith (.subOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_load_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.mem .load 998 (.addr 2 8))) = true := by cbv
-- rbi_2_1_load_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.mem .load 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_load8_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.mem .load8 998 (.addr 2 8))) = true := by cbv
-- rbi_2_1_load8_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.mem .load8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_load16_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.mem .load16 998 (.addr 2 8))) = true := by cbv
-- rbi_2_1_load16_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.mem .load16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_load32_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.mem .load32 998 (.addr 2 8))) = true := by cbv
-- rbi_2_1_load32_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.mem .load32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_store_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.mem .store 998 (.addr 2 8))) = true := by cbv
-- rbi_2_1_store_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.mem .store 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_store8_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.mem .store8 998 (.addr 2 8))) = true := by cbv
-- rbi_2_1_store8_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.mem .store8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_store16_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.mem .store16 998 (.addr 2 8))) = true := by cbv
-- rbi_2_1_store16_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.mem .store16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_store32_guard
example : postAllocConventionsHOL (width := 2) 8 (.inst (.mem .store32 998 (.addr 2 8))) = true := by cbv
-- rbi_2_1_store32_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.inst (.mem .store32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_2_1_fpless_guard


-- rbi_2_1_fplessequal_guard


-- rbi_2_1_fpequal_guard


-- rbi_2_1_fpabs_guard


-- rbi_2_1_fpneg_guard


-- rbi_2_1_fpsqrt_guard


-- rbi_2_1_fpadd_guard


-- rbi_2_1_fpsub_guard


-- rbi_2_1_fpmul_guard


-- rbi_2_1_fpdiv_guard


-- rbi_2_1_fpfma_guard


-- rbi_2_1_fpmov_guard


-- rbi_2_1_fpmovtoreg_guard


-- rbi_2_1_fpmovfromreg_guard


-- rbi_2_1_fptoint_guard


-- rbi_2_1_fpfromint_guard


-- rbi_2_1_fpmovtoreg1_guard


-- rbi_2_1_fpmovfromreg1_guard


-- rbi_2_1_fpmovtoreg32_guard


-- rbi_2_1_fpmovfromreg32_guard


-- rbi_2_1_fpmovtoreg80_guard


-- rbi_2_1_fpmovfromreg80_guard


-- rbi_2_1_share_Load_0_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .load 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_2_1_share_Load_0_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Load_1_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_2_1_share_Load_1_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Load_2_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .load 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_2_1_share_Load_2_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Load8_0_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .load8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_2_1_share_Load8_0_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Load8_1_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_2_1_share_Load8_1_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Load8_2_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .load8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_2_1_share_Load8_2_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Load16_0_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .load16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_2_1_share_Load16_0_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Load16_1_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_2_1_share_Load16_1_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Load16_2_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .load16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_2_1_share_Load16_2_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Load32_0_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .load32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_2_1_share_Load32_0_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Load32_1_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_2_1_share_Load32_1_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Load32_2_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .load32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_2_1_share_Load32_2_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Store_0_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .store 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_2_1_share_Store_0_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Store_1_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_2_1_share_Store_1_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Store_2_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .store 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_2_1_share_Store_2_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Store8_0_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .store8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_2_1_share_Store8_0_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Store8_1_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_2_1_share_Store8_1_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Store8_2_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .store8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_2_1_share_Store8_2_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Store16_0_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .store16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_2_1_share_Store16_0_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Store16_1_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_2_1_share_Store16_1_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Store16_2_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .store16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_2_1_share_Store16_2_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Store32_0_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .store32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_2_1_share_Store32_0_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Store32_1_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_2_1_share_Store32_1_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_2_1_share_Store32_2_guard
example : postAllocConventionsHOL (width := 2) 8 (.shareInst .store32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_2_1_share_Store32_2_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_skip_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.skip)) = true := by cbv
-- rbi_8_0_skip_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_const_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.const 998 4)) = true := by cbv
-- rbi_8_0_const_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.const 998 4)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_binop_imm_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.arith (.binop .add 998 2 (.imm 8)))) = true := by cbv
-- rbi_8_0_binop_imm_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.binop .add 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_binop_reg_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.arith (.binop .xor 998 2 (.reg 4)))) = true := by cbv
-- rbi_8_0_binop_reg_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.binop .xor 998 2 (.reg 4)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_shift_imm_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) = true := by cbv
-- rbi_8_0_shift_imm_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_shift_reg_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) = true := by cbv
-- rbi_8_0_shift_reg_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_div_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.arith (.div 998 2 4))) = true := by cbv
-- rbi_8_0_div_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.div 998 2 4))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_long_mul_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.arith (.longMul 6 0 0 4))) = true := by cbv
-- rbi_8_0_long_mul_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.longMul 6 0 0 4))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_long_div_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.arith (.longDiv 0 6 6 0 8))) = true := by cbv
-- rbi_8_0_long_div_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.longDiv 0 6 6 0 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_carry_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.arith (.addCarry 998 6 2 0))) = true := by cbv
-- rbi_8_0_carry_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.addCarry 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_add_overflow_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.arith (.addOverflow 998 6 2 0))) = true := by cbv
-- rbi_8_0_add_overflow_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.addOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_sub_overflow_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.arith (.subOverflow 998 6 2 0))) = true := by cbv
-- rbi_8_0_sub_overflow_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.subOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_load_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.mem .load 998 (.addr 2 8))) = true := by cbv
-- rbi_8_0_load_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.mem .load 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_load8_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.mem .load8 998 (.addr 2 8))) = true := by cbv
-- rbi_8_0_load8_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.mem .load8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_load16_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.mem .load16 998 (.addr 2 8))) = true := by cbv
-- rbi_8_0_load16_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.mem .load16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_load32_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.mem .load32 998 (.addr 2 8))) = true := by cbv
-- rbi_8_0_load32_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.mem .load32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_store_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.mem .store 998 (.addr 2 8))) = true := by cbv
-- rbi_8_0_store_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.mem .store 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_store8_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.mem .store8 998 (.addr 2 8))) = true := by cbv
-- rbi_8_0_store8_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.mem .store8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_store16_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.mem .store16 998 (.addr 2 8))) = true := by cbv
-- rbi_8_0_store16_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.mem .store16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_store32_guard
example : postAllocConventionsHOL (width := 8) 4 (.inst (.mem .store32 998 (.addr 2 8))) = true := by cbv
-- rbi_8_0_store32_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.mem .store32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_0_fpless_guard


-- rbi_8_0_fplessequal_guard


-- rbi_8_0_fpequal_guard


-- rbi_8_0_fpabs_guard


-- rbi_8_0_fpneg_guard


-- rbi_8_0_fpsqrt_guard


-- rbi_8_0_fpadd_guard


-- rbi_8_0_fpsub_guard


-- rbi_8_0_fpmul_guard


-- rbi_8_0_fpdiv_guard


-- rbi_8_0_fpfma_guard


-- rbi_8_0_fpmov_guard


-- rbi_8_0_fpmovtoreg_guard


-- rbi_8_0_fpmovfromreg_guard


-- rbi_8_0_fptoint_guard


-- rbi_8_0_fpfromint_guard


-- rbi_8_0_fpmovtoreg1_guard


-- rbi_8_0_fpmovfromreg1_guard


-- rbi_8_0_fpmovtoreg32_guard


-- rbi_8_0_fpmovfromreg32_guard


-- rbi_8_0_fpmovtoreg80_guard


-- rbi_8_0_fpmovfromreg80_guard


-- rbi_8_0_share_Load_0_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .load 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_8_0_share_Load_0_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Load_1_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_8_0_share_Load_1_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Load_2_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .load 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_8_0_share_Load_2_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Load8_0_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .load8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_8_0_share_Load8_0_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Load8_1_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_8_0_share_Load8_1_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Load8_2_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .load8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_8_0_share_Load8_2_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Load16_0_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .load16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_8_0_share_Load16_0_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Load16_1_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_8_0_share_Load16_1_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Load16_2_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .load16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_8_0_share_Load16_2_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Load32_0_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .load32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_8_0_share_Load32_0_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Load32_1_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_8_0_share_Load32_1_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Load32_2_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .load32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_8_0_share_Load32_2_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Store_0_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .store 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_8_0_share_Store_0_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Store_1_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_8_0_share_Store_1_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Store_2_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .store 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_8_0_share_Store_2_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Store8_0_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .store8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_8_0_share_Store8_0_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Store8_1_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_8_0_share_Store8_1_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Store8_2_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .store8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_8_0_share_Store8_2_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Store16_0_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .store16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_8_0_share_Store16_0_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Store16_1_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_8_0_share_Store16_1_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Store16_2_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .store16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_8_0_share_Store16_2_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Store32_0_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .store32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_8_0_share_Store32_0_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Store32_1_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_8_0_share_Store32_1_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_0_share_Store32_2_guard
example : postAllocConventionsHOL (width := 8) 4 (.shareInst .store32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_8_0_share_Store32_2_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_skip_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.skip)) = true := by cbv
-- rbi_8_1_skip_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_const_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.const 998 4)) = true := by cbv
-- rbi_8_1_const_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.const 998 4)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_binop_imm_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.arith (.binop .add 998 2 (.imm 8)))) = true := by cbv
-- rbi_8_1_binop_imm_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.binop .add 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_binop_reg_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.arith (.binop .xor 998 2 (.reg 4)))) = true := by cbv
-- rbi_8_1_binop_reg_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.binop .xor 998 2 (.reg 4)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_shift_imm_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) = true := by cbv
-- rbi_8_1_shift_imm_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_shift_reg_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) = true := by cbv
-- rbi_8_1_shift_reg_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_div_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.arith (.div 998 2 4))) = true := by cbv
-- rbi_8_1_div_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.div 998 2 4))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_long_mul_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.arith (.longMul 6 0 0 4))) = true := by cbv
-- rbi_8_1_long_mul_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.longMul 6 0 0 4))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_long_div_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.arith (.longDiv 0 6 6 0 8))) = true := by cbv
-- rbi_8_1_long_div_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.longDiv 0 6 6 0 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_carry_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.arith (.addCarry 998 6 2 0))) = true := by cbv
-- rbi_8_1_carry_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.addCarry 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_add_overflow_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.arith (.addOverflow 998 6 2 0))) = true := by cbv
-- rbi_8_1_add_overflow_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.addOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_sub_overflow_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.arith (.subOverflow 998 6 2 0))) = true := by cbv
-- rbi_8_1_sub_overflow_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.arith (.subOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_load_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.mem .load 998 (.addr 2 8))) = true := by cbv
-- rbi_8_1_load_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.mem .load 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_load8_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.mem .load8 998 (.addr 2 8))) = true := by cbv
-- rbi_8_1_load8_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.mem .load8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_load16_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.mem .load16 998 (.addr 2 8))) = true := by cbv
-- rbi_8_1_load16_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.mem .load16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_load32_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.mem .load32 998 (.addr 2 8))) = true := by cbv
-- rbi_8_1_load32_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.mem .load32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_store_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.mem .store 998 (.addr 2 8))) = true := by cbv
-- rbi_8_1_store_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.mem .store 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_store8_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.mem .store8 998 (.addr 2 8))) = true := by cbv
-- rbi_8_1_store8_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.mem .store8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_store16_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.mem .store16 998 (.addr 2 8))) = true := by cbv
-- rbi_8_1_store16_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.mem .store16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_store32_guard
example : postAllocConventionsHOL (width := 8) 8 (.inst (.mem .store32 998 (.addr 2 8))) = true := by cbv
-- rbi_8_1_store32_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.inst (.mem .store32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_8_1_fpless_guard


-- rbi_8_1_fplessequal_guard


-- rbi_8_1_fpequal_guard


-- rbi_8_1_fpabs_guard


-- rbi_8_1_fpneg_guard


-- rbi_8_1_fpsqrt_guard


-- rbi_8_1_fpadd_guard


-- rbi_8_1_fpsub_guard


-- rbi_8_1_fpmul_guard


-- rbi_8_1_fpdiv_guard


-- rbi_8_1_fpfma_guard


-- rbi_8_1_fpmov_guard


-- rbi_8_1_fpmovtoreg_guard


-- rbi_8_1_fpmovfromreg_guard


-- rbi_8_1_fptoint_guard


-- rbi_8_1_fpfromint_guard


-- rbi_8_1_fpmovtoreg1_guard


-- rbi_8_1_fpmovfromreg1_guard


-- rbi_8_1_fpmovtoreg32_guard


-- rbi_8_1_fpmovfromreg32_guard


-- rbi_8_1_fpmovtoreg80_guard


-- rbi_8_1_fpmovfromreg80_guard


-- rbi_8_1_share_Load_0_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .load 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_8_1_share_Load_0_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Load_1_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_8_1_share_Load_1_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Load_2_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .load 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_8_1_share_Load_2_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Load8_0_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .load8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_8_1_share_Load8_0_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Load8_1_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_8_1_share_Load8_1_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Load8_2_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .load8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_8_1_share_Load8_2_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Load16_0_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .load16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_8_1_share_Load16_0_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Load16_1_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_8_1_share_Load16_1_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Load16_2_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .load16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_8_1_share_Load16_2_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Load32_0_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .load32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_8_1_share_Load32_0_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Load32_1_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_8_1_share_Load32_1_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Load32_2_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .load32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_8_1_share_Load32_2_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Store_0_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .store 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_8_1_share_Store_0_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Store_1_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_8_1_share_Store_1_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Store_2_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .store 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_8_1_share_Store_2_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Store8_0_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .store8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_8_1_share_Store8_0_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Store8_1_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_8_1_share_Store8_1_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Store8_2_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .store8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_8_1_share_Store8_2_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Store16_0_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .store16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_8_1_share_Store16_0_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Store16_1_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_8_1_share_Store16_1_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Store16_2_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .store16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_8_1_share_Store16_2_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Store32_0_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .store32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_8_1_share_Store32_0_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Store32_1_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_8_1_share_Store32_1_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_8_1_share_Store32_2_guard
example : postAllocConventionsHOL (width := 8) 8 (.shareInst .store32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_8_1_share_Store32_2_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_skip_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.skip)) = true := by cbv
-- rbi_64_0_skip_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_const_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.const 998 4)) = true := by cbv
-- rbi_64_0_const_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.const 998 4)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_binop_imm_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.arith (.binop .add 998 2 (.imm 8)))) = true := by cbv
-- rbi_64_0_binop_imm_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.binop .add 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_binop_reg_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.arith (.binop .xor 998 2 (.reg 4)))) = true := by cbv
-- rbi_64_0_binop_reg_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.binop .xor 998 2 (.reg 4)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_shift_imm_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) = true := by cbv
-- rbi_64_0_shift_imm_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_shift_reg_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) = true := by cbv
-- rbi_64_0_shift_reg_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_div_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.arith (.div 998 2 4))) = true := by cbv
-- rbi_64_0_div_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.div 998 2 4))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_long_mul_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.arith (.longMul 6 0 0 4))) = true := by cbv
-- rbi_64_0_long_mul_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.longMul 6 0 0 4))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_long_div_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.arith (.longDiv 0 6 6 0 8))) = true := by cbv
-- rbi_64_0_long_div_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.longDiv 0 6 6 0 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_carry_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.arith (.addCarry 998 6 2 0))) = true := by cbv
-- rbi_64_0_carry_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.addCarry 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_add_overflow_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.arith (.addOverflow 998 6 2 0))) = true := by cbv
-- rbi_64_0_add_overflow_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.addOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_sub_overflow_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.arith (.subOverflow 998 6 2 0))) = true := by cbv
-- rbi_64_0_sub_overflow_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.subOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_load_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.mem .load 998 (.addr 2 8))) = true := by cbv
-- rbi_64_0_load_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.mem .load 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_load8_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.mem .load8 998 (.addr 2 8))) = true := by cbv
-- rbi_64_0_load8_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.mem .load8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_load16_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.mem .load16 998 (.addr 2 8))) = true := by cbv
-- rbi_64_0_load16_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.mem .load16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_load32_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.mem .load32 998 (.addr 2 8))) = true := by cbv
-- rbi_64_0_load32_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.mem .load32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_store_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.mem .store 998 (.addr 2 8))) = true := by cbv
-- rbi_64_0_store_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.mem .store 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_store8_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.mem .store8 998 (.addr 2 8))) = true := by cbv
-- rbi_64_0_store8_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.mem .store8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_store16_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.mem .store16 998 (.addr 2 8))) = true := by cbv
-- rbi_64_0_store16_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.mem .store16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_store32_guard
example : postAllocConventionsHOL (width := 64) 4 (.inst (.mem .store32 998 (.addr 2 8))) = true := by cbv
-- rbi_64_0_store32_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.mem .store32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_0_fpless_guard


-- rbi_64_0_fplessequal_guard


-- rbi_64_0_fpequal_guard


-- rbi_64_0_fpabs_guard


-- rbi_64_0_fpneg_guard


-- rbi_64_0_fpsqrt_guard


-- rbi_64_0_fpadd_guard


-- rbi_64_0_fpsub_guard


-- rbi_64_0_fpmul_guard


-- rbi_64_0_fpdiv_guard


-- rbi_64_0_fpfma_guard


-- rbi_64_0_fpmov_guard


-- rbi_64_0_fpmovtoreg_guard


-- rbi_64_0_fpmovfromreg_guard


-- rbi_64_0_fptoint_guard


-- rbi_64_0_fpfromint_guard


-- rbi_64_0_fpmovtoreg1_guard


-- rbi_64_0_fpmovfromreg1_guard


-- rbi_64_0_fpmovtoreg32_guard


-- rbi_64_0_fpmovfromreg32_guard


-- rbi_64_0_fpmovtoreg80_guard


-- rbi_64_0_fpmovfromreg80_guard


-- rbi_64_0_share_Load_0_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .load 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_64_0_share_Load_0_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Load_1_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_64_0_share_Load_1_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Load_2_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .load 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_64_0_share_Load_2_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Load8_0_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .load8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_64_0_share_Load8_0_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Load8_1_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_64_0_share_Load8_1_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Load8_2_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .load8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_64_0_share_Load8_2_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Load16_0_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .load16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_64_0_share_Load16_0_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Load16_1_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_64_0_share_Load16_1_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Load16_2_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .load16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_64_0_share_Load16_2_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Load32_0_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .load32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_64_0_share_Load32_0_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Load32_1_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_64_0_share_Load32_1_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Load32_2_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .load32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_64_0_share_Load32_2_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Store_0_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .store 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_64_0_share_Store_0_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Store_1_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_64_0_share_Store_1_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Store_2_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .store 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_64_0_share_Store_2_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Store8_0_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .store8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_64_0_share_Store8_0_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Store8_1_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_64_0_share_Store8_1_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Store8_2_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .store8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_64_0_share_Store8_2_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Store16_0_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .store16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_64_0_share_Store16_0_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Store16_1_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_64_0_share_Store16_1_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Store16_2_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .store16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_64_0_share_Store16_2_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Store32_0_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .store32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_64_0_share_Store32_0_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Store32_1_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_64_0_share_Store32_1_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_0_share_Store32_2_guard
example : postAllocConventionsHOL (width := 64) 4 (.shareInst .store32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_64_0_share_Store32_2_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_skip_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.skip)) = true := by cbv
-- rbi_64_1_skip_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_const_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.const 998 4)) = true := by cbv
-- rbi_64_1_const_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.const 998 4)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_binop_imm_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.arith (.binop .add 998 2 (.imm 8)))) = true := by cbv
-- rbi_64_1_binop_imm_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.binop .add 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_binop_reg_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.arith (.binop .xor 998 2 (.reg 4)))) = true := by cbv
-- rbi_64_1_binop_reg_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.binop .xor 998 2 (.reg 4)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_shift_imm_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) = true := by cbv
-- rbi_64_1_shift_imm_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_shift_reg_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) = true := by cbv
-- rbi_64_1_shift_reg_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_div_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.arith (.div 998 2 4))) = true := by cbv
-- rbi_64_1_div_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.div 998 2 4))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_long_mul_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.arith (.longMul 6 0 0 4))) = true := by cbv
-- rbi_64_1_long_mul_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.longMul 6 0 0 4))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_long_div_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.arith (.longDiv 0 6 6 0 8))) = true := by cbv
-- rbi_64_1_long_div_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.longDiv 0 6 6 0 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_carry_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.arith (.addCarry 998 6 2 0))) = true := by cbv
-- rbi_64_1_carry_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.addCarry 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_add_overflow_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.arith (.addOverflow 998 6 2 0))) = true := by cbv
-- rbi_64_1_add_overflow_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.addOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_sub_overflow_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.arith (.subOverflow 998 6 2 0))) = true := by cbv
-- rbi_64_1_sub_overflow_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.arith (.subOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_load_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.mem .load 998 (.addr 2 8))) = true := by cbv
-- rbi_64_1_load_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.mem .load 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_load8_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.mem .load8 998 (.addr 2 8))) = true := by cbv
-- rbi_64_1_load8_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.mem .load8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_load16_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.mem .load16 998 (.addr 2 8))) = true := by cbv
-- rbi_64_1_load16_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.mem .load16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_load32_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.mem .load32 998 (.addr 2 8))) = true := by cbv
-- rbi_64_1_load32_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.mem .load32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_store_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.mem .store 998 (.addr 2 8))) = true := by cbv
-- rbi_64_1_store_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.mem .store 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_store8_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.mem .store8 998 (.addr 2 8))) = true := by cbv
-- rbi_64_1_store8_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.mem .store8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_store16_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.mem .store16 998 (.addr 2 8))) = true := by cbv
-- rbi_64_1_store16_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.mem .store16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_store32_guard
example : postAllocConventionsHOL (width := 64) 8 (.inst (.mem .store32 998 (.addr 2 8))) = true := by cbv
-- rbi_64_1_store32_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.inst (.mem .store32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_64_1_fpless_guard


-- rbi_64_1_fplessequal_guard


-- rbi_64_1_fpequal_guard


-- rbi_64_1_fpabs_guard


-- rbi_64_1_fpneg_guard


-- rbi_64_1_fpsqrt_guard


-- rbi_64_1_fpadd_guard


-- rbi_64_1_fpsub_guard


-- rbi_64_1_fpmul_guard


-- rbi_64_1_fpdiv_guard


-- rbi_64_1_fpfma_guard


-- rbi_64_1_fpmov_guard


-- rbi_64_1_fpmovtoreg_guard


-- rbi_64_1_fpmovfromreg_guard


-- rbi_64_1_fptoint_guard


-- rbi_64_1_fpfromint_guard


-- rbi_64_1_fpmovtoreg1_guard


-- rbi_64_1_fpmovfromreg1_guard


-- rbi_64_1_fpmovtoreg32_guard


-- rbi_64_1_fpmovfromreg32_guard


-- rbi_64_1_fpmovtoreg80_guard


-- rbi_64_1_fpmovfromreg80_guard


-- rbi_64_1_share_Load_0_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .load 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_64_1_share_Load_0_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Load_1_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_64_1_share_Load_1_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Load_2_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .load 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_64_1_share_Load_2_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Load8_0_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .load8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_64_1_share_Load8_0_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Load8_1_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_64_1_share_Load8_1_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Load8_2_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .load8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_64_1_share_Load8_2_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Load16_0_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .load16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_64_1_share_Load16_0_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Load16_1_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_64_1_share_Load16_1_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Load16_2_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .load16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_64_1_share_Load16_2_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Load32_0_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .load32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_64_1_share_Load32_0_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Load32_1_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_64_1_share_Load32_1_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Load32_2_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .load32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_64_1_share_Load32_2_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Store_0_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .store 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_64_1_share_Store_0_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Store_1_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_64_1_share_Store_1_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Store_2_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .store 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_64_1_share_Store_2_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Store8_0_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .store8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_64_1_share_Store8_0_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Store8_1_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_64_1_share_Store8_1_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Store8_2_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .store8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_64_1_share_Store8_2_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Store16_0_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .store16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_64_1_share_Store16_0_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Store16_1_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_64_1_share_Store16_1_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Store16_2_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .store16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_64_1_share_Store16_2_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Store32_0_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .store32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_64_1_share_Store32_0_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Store32_1_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_64_1_share_Store32_1_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_64_1_share_Store32_2_guard
example : postAllocConventionsHOL (width := 64) 8 (.shareInst .store32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_64_1_share_Store32_2_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_skip_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.skip)) = true := by cbv
-- rbi_80_0_skip_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_const_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.const 998 4)) = true := by cbv
-- rbi_80_0_const_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.const 998 4)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_binop_imm_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.arith (.binop .add 998 2 (.imm 8)))) = true := by cbv
-- rbi_80_0_binop_imm_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.binop .add 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_binop_reg_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.arith (.binop .xor 998 2 (.reg 4)))) = true := by cbv
-- rbi_80_0_binop_reg_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.binop .xor 998 2 (.reg 4)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_shift_imm_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) = true := by cbv
-- rbi_80_0_shift_imm_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_shift_reg_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) = true := by cbv
-- rbi_80_0_shift_reg_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_div_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.arith (.div 998 2 4))) = true := by cbv
-- rbi_80_0_div_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.div 998 2 4))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_long_mul_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.arith (.longMul 6 0 0 4))) = true := by cbv
-- rbi_80_0_long_mul_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.longMul 6 0 0 4))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_long_div_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.arith (.longDiv 0 6 6 0 8))) = true := by cbv
-- rbi_80_0_long_div_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.longDiv 0 6 6 0 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_carry_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.arith (.addCarry 998 6 2 0))) = true := by cbv
-- rbi_80_0_carry_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.addCarry 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_add_overflow_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.arith (.addOverflow 998 6 2 0))) = true := by cbv
-- rbi_80_0_add_overflow_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.addOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_sub_overflow_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.arith (.subOverflow 998 6 2 0))) = true := by cbv
-- rbi_80_0_sub_overflow_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.subOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_load_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.mem .load 998 (.addr 2 8))) = true := by cbv
-- rbi_80_0_load_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.mem .load 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_load8_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.mem .load8 998 (.addr 2 8))) = true := by cbv
-- rbi_80_0_load8_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.mem .load8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_load16_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.mem .load16 998 (.addr 2 8))) = true := by cbv
-- rbi_80_0_load16_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.mem .load16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_load32_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.mem .load32 998 (.addr 2 8))) = true := by cbv
-- rbi_80_0_load32_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.mem .load32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_store_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.mem .store 998 (.addr 2 8))) = true := by cbv
-- rbi_80_0_store_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.mem .store 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_store8_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.mem .store8 998 (.addr 2 8))) = true := by cbv
-- rbi_80_0_store8_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.mem .store8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_store16_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.mem .store16 998 (.addr 2 8))) = true := by cbv
-- rbi_80_0_store16_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.mem .store16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_store32_guard
example : postAllocConventionsHOL (width := 80) 4 (.inst (.mem .store32 998 (.addr 2 8))) = true := by cbv
-- rbi_80_0_store32_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.mem .store32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_0_fpless_guard


-- rbi_80_0_fplessequal_guard


-- rbi_80_0_fpequal_guard


-- rbi_80_0_fpabs_guard


-- rbi_80_0_fpneg_guard


-- rbi_80_0_fpsqrt_guard


-- rbi_80_0_fpadd_guard


-- rbi_80_0_fpsub_guard


-- rbi_80_0_fpmul_guard


-- rbi_80_0_fpdiv_guard


-- rbi_80_0_fpfma_guard


-- rbi_80_0_fpmov_guard


-- rbi_80_0_fpmovtoreg_guard


-- rbi_80_0_fpmovfromreg_guard


-- rbi_80_0_fptoint_guard


-- rbi_80_0_fpfromint_guard


-- rbi_80_0_fpmovtoreg1_guard


-- rbi_80_0_fpmovfromreg1_guard


-- rbi_80_0_fpmovtoreg32_guard


-- rbi_80_0_fpmovfromreg32_guard


-- rbi_80_0_fpmovtoreg80_guard


-- rbi_80_0_fpmovfromreg80_guard


-- rbi_80_0_share_Load_0_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .load 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_80_0_share_Load_0_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Load_1_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_80_0_share_Load_1_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Load_2_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .load 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_80_0_share_Load_2_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Load8_0_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .load8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_80_0_share_Load8_0_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Load8_1_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_80_0_share_Load8_1_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Load8_2_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .load8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_80_0_share_Load8_2_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Load16_0_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .load16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_80_0_share_Load16_0_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Load16_1_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_80_0_share_Load16_1_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Load16_2_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .load16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_80_0_share_Load16_2_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Load32_0_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .load32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_80_0_share_Load32_0_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Load32_1_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_80_0_share_Load32_1_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Load32_2_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .load32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_80_0_share_Load32_2_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Store_0_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .store 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_80_0_share_Store_0_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Store_1_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_80_0_share_Store_1_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Store_2_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .store 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_80_0_share_Store_2_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Store8_0_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .store8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_80_0_share_Store8_0_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Store8_1_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_80_0_share_Store8_1_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Store8_2_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .store8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_80_0_share_Store8_2_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Store16_0_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .store16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_80_0_share_Store16_0_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Store16_1_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_80_0_share_Store16_1_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Store16_2_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .store16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_80_0_share_Store16_2_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Store32_0_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .store32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_80_0_share_Store32_0_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Store32_1_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_80_0_share_Store32_1_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_0_share_Store32_2_guard
example : postAllocConventionsHOL (width := 80) 4 (.shareInst .store32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_80_0_share_Store32_2_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_skip_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.skip)) = true := by cbv
-- rbi_80_1_skip_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.skip)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_const_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.const 998 4)) = true := by cbv
-- rbi_80_1_const_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.const 998 4)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_binop_imm_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.arith (.binop .add 998 2 (.imm 8)))) = true := by cbv
-- rbi_80_1_binop_imm_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.binop .add 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_binop_reg_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.arith (.binop .xor 998 2 (.reg 4)))) = true := by cbv
-- rbi_80_1_binop_reg_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.binop .xor 998 2 (.reg 4)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_shift_imm_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) = true := by cbv
-- rbi_80_1_shift_imm_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.shift .lsl 998 2 (.imm 8)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_shift_reg_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) = true := by cbv
-- rbi_80_1_shift_reg_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.shift .lsr 998 2 (.reg 8)))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_div_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.arith (.div 998 2 4))) = true := by cbv
-- rbi_80_1_div_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.div 998 2 4))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_long_mul_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.arith (.longMul 6 0 0 4))) = true := by cbv
-- rbi_80_1_long_mul_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.longMul 6 0 0 4))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_long_div_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.arith (.longDiv 0 6 6 0 8))) = true := by cbv
-- rbi_80_1_long_div_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.longDiv 0 6 6 0 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_carry_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.arith (.addCarry 998 6 2 0))) = true := by cbv
-- rbi_80_1_carry_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.addCarry 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_add_overflow_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.arith (.addOverflow 998 6 2 0))) = true := by cbv
-- rbi_80_1_add_overflow_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.addOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_sub_overflow_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.arith (.subOverflow 998 6 2 0))) = true := by cbv
-- rbi_80_1_sub_overflow_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.arith (.subOverflow 998 6 2 0))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_load_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.mem .load 998 (.addr 2 8))) = true := by cbv
-- rbi_80_1_load_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.mem .load 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_load8_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.mem .load8 998 (.addr 2 8))) = true := by cbv
-- rbi_80_1_load8_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.mem .load8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_load16_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.mem .load16 998 (.addr 2 8))) = true := by cbv
-- rbi_80_1_load16_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.mem .load16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_load32_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.mem .load32 998 (.addr 2 8))) = true := by cbv
-- rbi_80_1_load32_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.mem .load32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_store_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.mem .store 998 (.addr 2 8))) = true := by cbv
-- rbi_80_1_store_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.mem .store 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_store8_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.mem .store8 998 (.addr 2 8))) = true := by cbv
-- rbi_80_1_store8_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.mem .store8 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_store16_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.mem .store16 998 (.addr 2 8))) = true := by cbv
-- rbi_80_1_store16_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.mem .store16 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_store32_guard
example : postAllocConventionsHOL (width := 80) 8 (.inst (.mem .store32 998 (.addr 2 8))) = true := by cbv
-- rbi_80_1_store32_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.inst (.mem .store32 998 (.addr 2 8))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInst <;> first | rfl | cbv

-- rbi_80_1_fpless_guard


-- rbi_80_1_fplessequal_guard


-- rbi_80_1_fpequal_guard


-- rbi_80_1_fpabs_guard


-- rbi_80_1_fpneg_guard


-- rbi_80_1_fpsqrt_guard


-- rbi_80_1_fpadd_guard


-- rbi_80_1_fpsub_guard


-- rbi_80_1_fpmul_guard


-- rbi_80_1_fpdiv_guard


-- rbi_80_1_fpfma_guard


-- rbi_80_1_fpmov_guard


-- rbi_80_1_fpmovtoreg_guard


-- rbi_80_1_fpmovfromreg_guard


-- rbi_80_1_fptoint_guard


-- rbi_80_1_fpfromint_guard


-- rbi_80_1_fpmovtoreg1_guard


-- rbi_80_1_fpmovfromreg1_guard


-- rbi_80_1_fpmovtoreg32_guard


-- rbi_80_1_fpmovfromreg32_guard


-- rbi_80_1_fpmovtoreg80_guard


-- rbi_80_1_fpmovfromreg80_guard


-- rbi_80_1_share_Load_0_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .load 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_80_1_share_Load_0_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Load_1_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_80_1_share_Load_1_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Load_2_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .load 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_80_1_share_Load_2_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Load8_0_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .load8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_80_1_share_Load8_0_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Load8_1_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_80_1_share_Load8_1_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Load8_2_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .load8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_80_1_share_Load8_2_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Load16_0_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .load16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_80_1_share_Load16_0_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Load16_1_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_80_1_share_Load16_1_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Load16_2_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .load16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_80_1_share_Load16_2_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Load32_0_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .load32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_80_1_share_Load32_0_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Load32_1_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_80_1_share_Load32_1_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Load32_2_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .load32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_80_1_share_Load32_2_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .load32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Store_0_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .store 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_80_1_share_Store_0_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Store_1_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_80_1_share_Store_1_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Store_2_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .store 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_80_1_share_Store_2_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Store8_0_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .store8 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_80_1_share_Store8_0_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Store8_1_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_80_1_share_Store8_1_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Store8_2_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .store8 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_80_1_share_Store8_2_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store8 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Store16_0_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .store16 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_80_1_share_Store16_0_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Store16_1_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_80_1_share_Store16_1_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Store16_2_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .store16 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_80_1_share_Store16_2_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store16 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Store32_0_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .store32 1180591620717411303426 (.var 998)) = true := by cbv
-- rbi_80_1_share_Store32_0_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.var 998)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Store32_1_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) = true := by cbv
-- rbi_80_1_share_Store32_1_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.op .add [.var 998,.const 8])) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

-- rbi_80_1_share_Store32_2_guard
example : postAllocConventionsHOL (width := 80) 8 (.shareInst .store32 1180591620717411303426 (.load (.var 998))) = true := by cbv
-- rbi_80_1_share_Store32_2_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.shareInst .store32 1180591620717411303426 (.load (.var 998))) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundShareInst <;> first | rfl | cbv

end Flapjack.Test.WordToStackRegInstructionsParity

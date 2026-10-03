import Flapjack.RiscV.L3.Support
import Init.Data.BitVec.Bitblast

/-! Complete named word-bit rewrites from the original symbolic step theory.
HOL Boolean negation is rendered as equality to false; no input domain is restricted. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "word_bit_1_0"]
theorem word_bit_1_0 (x0 x1 x2 x3 x4 x5 x6 x7 : Bool) :
    (holV2w 8 [x0,x1,x2,x3,x4,x5,x6,x7]).getLsbD 1 = x6 ∧
    (holV2w 8 [x0,x1,x2,x3,x4,x5,x6,x7]).getLsbD 0 = x7 := by
  simp only [holV2w, Flapjack.getLsbD_holFcpWord]
  simp

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "word_bit_0_lemmas"]
theorem word_bit_0_lemmas (w v : BitVec 64) :
    ((0xFFFFFFFFFFFFFFFE#64) &&& w).getLsbD 0 = false ∧
    (((0xFFFFFFFFFFFFFFFE#64) &&& w) + v).getLsbD 0 = v.getLsbD 0 := by
  constructor
  · rw [BitVec.getLsbD_and]
    simp only [BitVec.getLsbD_ofNat]
    simp
  · rw [BitVec.getLsbD_add (by decide : 0 < 64)]
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, BitVec.carry_zero]
    simp

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "v2w_0_rwts"]
theorem v2w_0_rwts (b3 b2 b1 b0 : Bool) :
    holV2w 5 [false,false,false,false,true] = 1#5 ∧
    holV2w 5 [false,false,false,false,false] = 0#5 ∧
    decide (holV2w 5 [true,b3,b2,b1,b0] = 0#5) = false ∧
    decide (holV2w 5 [b3,true,b2,b1,b0] = 0#5) = false ∧
    decide (holV2w 5 [b3,b2,true,b1,b0] = 0#5) = false ∧
    decide (holV2w 5 [b3,b2,b1,true,b0] = 0#5) = false ∧
    decide (holV2w 5 [b3,b2,b1,b0,true] = 0#5) = false := by
  cases b3 <;> cases b2 <;> cases b1 <;> cases b0 <;> decide

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "word_bit_add_lsl_simp"]
theorem word_bit_add_lsl_simp (x w : BitVec 64) :
    (x + (w <<< 1)).getLsbD 0 = x.getLsbD 0 := by
  rw [BitVec.getLsbD_add (by decide : 0 < 64)]
  simp only [BitVec.getLsbD_shiftLeft, BitVec.carry_zero]
  simp

end Flapjack.RiscV.L3.Step

import Flapjack.Compiler.Backend.LabSem.FpUpdates
import Flapjack.Misc.BinaryIeeeArithFp64
import Flapjack.Misc.BinaryIeeeSqrtFp64

/-! Kernel replay of the identical symbolic-state direct original HOL fixtures
in scripts/hol-probes/labsem_fp_updates_probe.out. Finite regression coverage,
not full evaluator routing or a proof of cross-language IEEE correspondence. -/
namespace Flapjack.Test.LabSemFpUpdatesParity
open Flapjack.Compiler.Backend.LabSem
variable {C F : Type}

/-- Original HOL row `lab_fp_less_nan=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpLess 1 2 3) { s with fpRegs := fun _ => 0x7ff8000000000001 }).regs 1 = .word 0 := by
  have hvalue : holFp64LessThan 0x7ff8000000000001 0x7ff8000000000001 = false := by decide +kernel
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp only [hvalue]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_less_equal_zero=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpLessEqual 1 2 3) { s with fpRegs := (fun r => if r = 2 then 0x8000000000000000 else 0) }).regs 1 = .word 1 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_equal_nan=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpEqual 1 2 3) { s with fpRegs := fun _ => 0x7ff8000000000001 }).regs 1 = .word 0 := by
  have hvalue : holFp64Equal 0x7ff8000000000001 0x7ff8000000000001 = false := by decide +kernel
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp only [hvalue]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_equal_zero=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpEqual 1 2 3) { s with fpRegs := fun _ => 0 }).regs 1 = .word 1 := by
  have hvalue : holFp64Equal 0 0 = true := by decide +kernel
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp only [hvalue]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_mov_payload=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpMov 1 2) { s with fpRegs := fun _ => 0x7ff8000000000001 }).fpRegs 1 = 0x7ff8000000000001 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_abs_payload=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpAbs 1 2) { s with fpRegs := fun _ => 0xfff8000000000001 }).fpRegs 1 = 0x7ff8000000000001 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_neg_zero=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpNeg 1 2) { s with fpRegs := fun _ => 0x8000000000000000 }).fpRegs 1 = 0 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_sqrt_four=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpSqrt 1 2) { s with fpRegs := fun _ => 0x4010000000000000 }).fpRegs 1 = 0x4000000000000000 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  rw [holFp64Sqrt_rte]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_add_two=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpAdd 1 2 3) { s with fpRegs := fun _ => 0x3ff0000000000000 }).fpRegs 1 = 0x4000000000000000 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  rw [holFp64Add_rte]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_sub_zero=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpSub 1 2 3) { s with fpRegs := fun _ => 0x3ff0000000000000 }).fpRegs 1 = 0 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  rw [holFp64Sub_rte]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_mul_four=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpMul 1 2 3) { s with fpRegs := fun _ => 0x4000000000000000 }).fpRegs 1 = 0x4010000000000000 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  rw [holFp64Mul_rte]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_div_half=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpDiv 1 2 3) { s with fpRegs := (fun r => if r = 2 then 0x3ff0000000000000 else 0x4000000000000000) }).fpRegs 1 = 0x3fe0000000000000 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  rw [holFp64Div_rte]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_fma_order=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpFma 1 2 3) { s with fpRegs := (fun r => if r = 1 then 0x3ff0000000000000 else if r = 2 then 0x4000000000000000 else 0x4008000000000000) }).fpRegs 1 = 0x401c000000000000 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  rw [fpSemFpfma_rte]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_to_reg64=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpMovToReg 1 2 3) { s with fpRegs := fun _ => 0x7ff8000000000001 }).regs 1 = .word 0x7ff8000000000001 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_to_reg_alias32=T`. -/
example (s : State 32 C F) :
    (fpUpd (.fpMovToReg 1 1 3) { s with fpRegs := fun _ => 0x123456789abcdef0 }).regs 1 = .word 0x12345678 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_from_reg64=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpMovFromReg 1 2 3) { s with regs := fun _ => (.word 0x123456789abcdef0) }).fpRegs 1 = 0x123456789abcdef0 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_from_reg_loc_error=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpMovFromReg 1 2 3) { s with regs := fun _ => (.loc 4 5), failed := false }).failed = true := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_from_reg32=T`. -/
example (s : State 32 C F) :
    (fpUpd (.fpMovFromReg 1 2 3) { s with regs := (fun r => if r = 2 then .word 0x9abcdef0 else .word 0x12345678) }).fpRegs 1 = 0x123456789abcdef0 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_from_reg8=T`. -/
example (s : State 8 C F) :
    (fpUpd (.fpMovFromReg 1 2 3) { s with regs := (fun r => if r = 2 then .word 0x34 else .word 0x12) }).fpRegs 1 = 0x1234 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_to_int_tie_even=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpToInt 1 2) { s with fpRegs := fun _ => 0x4004000000000000 }).fpRegs 1 = 2 := by
  have hvalue : holFp64ToInt .roundTiesToEven 0x4004000000000000 = some 2 := by decide +kernel
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp only [hvalue]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_to_int_negative=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpToInt 1 2) { s with fpRegs := fun _ => 0xbff0000000000000 }).fpRegs 1 = 0xffffffff := by
  have hvalue : holFp64ToInt .roundTiesToEven 0xbff0000000000000 = some (-1) := by decide +kernel
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp only [hvalue]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_to_int_overflow_bits=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpToInt 1 2) { s with fpRegs := fun _ => 0x41e0000000000000, failed := false }).fpRegs 1 = 0x80000000 := by
  have hvalue : holFp64ToInt .roundTiesToEven 0x41e0000000000000 = some 2147483648 := by decide +kernel
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp only [hvalue]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_to_int_overflow_failed=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpToInt 1 2) { s with fpRegs := fun _ => 0x41e0000000000000, failed := false }).failed = true := by
  have hvalue : holFp64ToInt .roundTiesToEven 0x41e0000000000000 = some 2147483648 := by decide +kernel
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp only [hvalue]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_to_int_inf_error=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpToInt 1 2) { s with fpRegs := fun _ => 0x7ff0000000000000, failed := false }).failed = true := by
  have hvalue : holFp64ToInt .roundTiesToEven 0x7ff0000000000000 = none := by decide +kernel
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp only [hvalue]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_to_int_odd32=T`. -/
example (s : State 32 C F) :
    (fpUpd (.fpToInt 3 2) { s with fpRegs := (fun r => if r = 2 then 0x4000000000000000 else 0x123456789abcdef0) }).fpRegs 1 = 0x000000029abcdef0 := by
  have hvalue : holFp64ToInt .roundTiesToEven 0x4000000000000000 = some 2 := by decide +kernel
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  simp only [ite_true]
  simp only [hvalue]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_from_int64=T`. -/
example (s : State 64 C F) :
    (fpUpd (.fpFromInt 1 2) { s with fpRegs := fun _ => 0xffffffff }).fpRegs 1 = 0xbff0000000000000 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  rw [holIntToFp64_rte]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_from_int32=T`. -/
example (s : State 32 C F) :
    (fpUpd (.fpFromInt 1 3) { s with fpRegs := fun _ => 0xffffffff00000000 }).fpRegs 1 = 0xbff0000000000000 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  rw [holIntToFp64_rte]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_from_int8=T`. -/
example (s : State 8 C F) :
    (fpUpd (.fpFromInt 1 3) { s with fpRegs := fun _ => 0xffffffff00000000 }).fpRegs 1 = 0xbff0000000000000 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  rw [holIntToFp64_rte]
  simp <;> decide +kernel
/-- Original HOL row `lab_fp_from_int128=T`. -/
example (s : State 128 C F) :
    (fpUpd (.fpFromInt 1 2) { s with fpRegs := fun _ => 0xffffffff }).fpRegs 1 = 0x41efffffffe00000 := by
  dsimp only [fpUpd, readFpReg, updFpReg, updReg, assertState]
  rw [holIntToFp64_rte]
  simp <;> decide +kernel

end Flapjack.Test.LabSemFpUpdatesParity

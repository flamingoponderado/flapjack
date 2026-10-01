import Flapjack.Compiler.Encoders.AsmProps.FpPreservation
import Flapjack.Misc.BinaryIeeeArithFp64
import Flapjack.Misc.BinaryIeeeSqrtFp64

/-! Kernel replay of the identical symbolic-state direct original HOL fixtures
in scripts/hol-probes/asmsem_fp_updates_probe.out. Finite regression coverage,
not full evaluator routing or a proof of cross-language IEEE correspondence. -/
namespace Flapjack.Test.AsmSemFpUpdatesParity
open Flapjack Flapjack.Compiler.Encoders.AsmSem

/-- Original HOL row `asm_fp_less_nan=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpLess 1 2 3) { s with fpRegs := fun _ => 0x7ff8000000000001 }).regs 1 = 0 := by
  have hvalue : holFp64LessThan 0x7ff8000000000001 0x7ff8000000000001 = false := by decide +kernel
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  simp only [hvalue]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_less_equal_zero=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpLessEqual 1 2 3) { s with fpRegs := (fun r => if r = 2 then 0x8000000000000000 else 0) }).regs 1 = 1 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_equal_nan=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpEqual 1 2 3) { s with fpRegs := fun _ => 0x7ff8000000000001 }).regs 1 = 0 := by
  have hvalue : holFp64Equal 0x7ff8000000000001 0x7ff8000000000001 = false := by decide +kernel
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  simp only [hvalue]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_equal_zero=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpEqual 1 2 3) { s with fpRegs := fun _ => 0 }).regs 1 = 1 := by
  have hvalue : holFp64Equal 0 0 = true := by decide +kernel
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  simp only [hvalue]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_mov_payload=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpMov 1 2) { s with fpRegs := fun _ => 0x7ff8000000000001 }).fpRegs 1 = 0x7ff8000000000001 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_abs_payload=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpAbs 1 2) { s with fpRegs := fun _ => 0xfff8000000000001 }).fpRegs 1 = 0x7ff8000000000001 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_neg_zero=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpNeg 1 2) { s with fpRegs := fun _ => 0x8000000000000000 }).fpRegs 1 = 0 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_sqrt_four=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpSqrt 1 2) { s with fpRegs := fun _ => 0x4010000000000000 }).fpRegs 1 = 0x4000000000000000 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  rw [holFp64Sqrt_rte]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_add_two=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpAdd 1 2 3) { s with fpRegs := fun _ => 0x3ff0000000000000 }).fpRegs 1 = 0x4000000000000000 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  rw [holFp64Add_rte]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_sub_zero=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpSub 1 2 3) { s with fpRegs := fun _ => 0x3ff0000000000000 }).fpRegs 1 = 0 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  rw [holFp64Sub_rte]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_mul_four=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpMul 1 2 3) { s with fpRegs := fun _ => 0x4000000000000000 }).fpRegs 1 = 0x4010000000000000 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  rw [holFp64Mul_rte]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_div_half=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpDiv 1 2 3) { s with fpRegs := (fun r => if r = 2 then 0x3ff0000000000000 else 0x4000000000000000) }).fpRegs 1 = 0x3fe0000000000000 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  rw [holFp64Div_rte]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_fma_order=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpFma 1 2 3) { s with fpRegs := (fun r => if r = 1 then 0x3ff0000000000000 else if r = 2 then 0x4000000000000000 else 0x4008000000000000) }).fpRegs 1 = 0x401c000000000000 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  change fpSemFpfma 0x3ff0000000000000 0x4000000000000000 0x4008000000000000 = 0x401c000000000000
  rw [fpSemFpfma_rte]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_to_reg64=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpMovToReg 1 2 3) { s with fpRegs := fun _ => 0x7ff8000000000001 }).regs 1 = 0x7ff8000000000001 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_to_reg_alias32=T`. -/
example (s : AsmState 32) :
    (fpUpd (.fpMovToReg 1 1 3) { s with fpRegs := fun _ => 0x123456789abcdef0 }).regs 1 = 0x12345678 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_from_reg64=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpMovFromReg 1 2 3) { s with regs := fun _ => (0x123456789abcdef0) }).fpRegs 1 = 0x123456789abcdef0 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_from_reg32=T`. -/
example (s : AsmState 32) :
    (fpUpd (.fpMovFromReg 1 2 3) { s with regs := (fun r => if r = 2 then 0x9abcdef0 else 0x12345678) }).fpRegs 1 = 0x123456789abcdef0 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_from_reg8=T`. -/
example (s : AsmState 8) :
    (fpUpd (.fpMovFromReg 1 2 3) { s with regs := (fun r => if r = 2 then 0x34 else 0x12) }).fpRegs 1 = 0x1234 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_to_int_tie_even=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpToInt 1 2) { s with fpRegs := fun _ => 0x4004000000000000 }).fpRegs 1 = 2 := by
  have hvalue : holFp64ToInt .roundTiesToEven 0x4004000000000000 = some 2 := by decide +kernel
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  simp only [hvalue]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_to_int_negative=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpToInt 1 2) { s with fpRegs := fun _ => 0xbff0000000000000 }).fpRegs 1 = 0xffffffff := by
  have hvalue : holFp64ToInt .roundTiesToEven 0xbff0000000000000 = some (-1) := by decide +kernel
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  simp only [hvalue]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_to_int_overflow_bits=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpToInt 1 2) { s with fpRegs := fun _ => 0x41e0000000000000, failed := false }).fpRegs 1 = 0x80000000 := by
  have hvalue : holFp64ToInt .roundTiesToEven 0x41e0000000000000 = some 2147483648 := by decide +kernel
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  simp only [hvalue]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_to_int_overflow_failed=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpToInt 1 2) { s with fpRegs := fun _ => 0x41e0000000000000, failed := false }).failed = true := by
  have hvalue : holFp64ToInt .roundTiesToEven 0x41e0000000000000 = some 2147483648 := by decide +kernel
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  simp only [hvalue]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_to_int_inf_error=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpToInt 1 2) { s with fpRegs := fun _ => 0x7ff0000000000000, failed := false }).failed = true := by
  have hvalue : holFp64ToInt .roundTiesToEven 0x7ff0000000000000 = none := by decide +kernel
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  simp only [hvalue]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_to_int_odd32=T`. -/
example (s : AsmState 32) :
    (fpUpd (.fpToInt 3 2) { s with fpRegs := (fun r => if r = 2 then 0x4000000000000000 else 0x123456789abcdef0) }).fpRegs 1 = 0x000000029abcdef0 := by
  have hvalue : holFp64ToInt .roundTiesToEven 0x4000000000000000 = some 2 := by decide +kernel
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  simp only [ite_true]
  simp only [hvalue]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_from_int64=T`. -/
example (s : AsmState 64) :
    (fpUpd (.fpFromInt 1 2) { s with fpRegs := fun _ => 0xffffffff }).fpRegs 1 = 0xbff0000000000000 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  rw [holIntToFp64_rte]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_from_int32=T`. -/
example (s : AsmState 32) :
    (fpUpd (.fpFromInt 1 3) { s with fpRegs := fun _ => 0xffffffff00000000 }).fpRegs 1 = 0xbff0000000000000 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  rw [holIntToFp64_rte]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_from_int8=T`. -/
example (s : AsmState 8) :
    (fpUpd (.fpFromInt 1 3) { s with fpRegs := fun _ => 0xffffffff00000000 }).fpRegs 1 = 0xbff0000000000000 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  rw [holIntToFp64_rte]
  simp <;> decide +kernel
/-- Original HOL row `asm_fp_from_int128=T`. -/
example (s : AsmState 128) :
    (fpUpd (.fpFromInt 1 2) { s with fpRegs := fun _ => 0xffffffff }).fpRegs 1 = 0x41efffffffe00000 := by
  dsimp only [fpUpd, readReg, readFpReg, updFpReg, updReg, assertState]
  rw [holIntToFp64_rte]
  simp <;> decide +kernel

-- Original row asm_fp_to_int_lower_alias32=T.
example (s : AsmState 32) :
    (fpUpd (.fpToInt 4 2) { s with fpRegs := fun _ => 0x4000000000000000 }).fpRegs 2 = 0x4000000000000002 := by
  have hv : holFp64ToInt .roundTiesToEven 0x4000000000000000 = some 2 := by decide +kernel
  dsimp only [fpUpd, readFpReg, updFpReg, assertState]
  simp only [hv]
  simp <;> decide +kernel

-- Original row asm_fp_to_int_upper_alias32=T.
example (s : AsmState 32) :
    (fpUpd (.fpToInt 5 2) { s with fpRegs := fun _ => 0x4000000000000000 }).fpRegs 2 = 0x0000000200000000 := by
  have hv : holFp64ToInt .roundTiesToEven 0x4000000000000000 = some 2 := by decide +kernel
  dsimp only [fpUpd, readFpReg, updFpReg, assertState]
  simp only [hv]
  simp <;> decide +kernel

-- Original row asm_fp_to_int_overflow32=T.
example (s : AsmState 32) :
    let t := fpUpd (.fpToInt 3 2) { s with fpRegs := fun r => if r = 2 then 0x41e0000000000000 else 0x123456789abcdef0, failed := false }
    t.fpRegs 1 = 0x800000009abcdef0 ∧ t.failed = true := by
  have hv : holFp64ToInt .roundTiesToEven 0x41e0000000000000 = some 2147483648 := by decide +kernel
  dsimp only [fpUpd, readFpReg, updFpReg, assertState]
  simp only [ite_true, hv]
  simp <;> decide +kernel

-- Original row asm_fp_to_reg8=T.
example (s : AsmState 8) :
    let t := fpUpd (.fpMovToReg 1 2 3) { s with fpRegs := fun _ => 0x123456789abcdef0 }
    t.regs 1 = 0xf0 ∧ t.regs 2 = 0x78 := by
  dsimp only [fpUpd, readFpReg, updReg]
  simp <;> decide +kernel

-- Original row asm_fp_from_reg128=T.
example (s : AsmState 128) :
    (fpUpd (.fpMovFromReg 1 2 3) { s with regs := fun r => if r = 2 then 0x11112222333344445555666677778888 else 0x9999 }).fpRegs 1 = 0x5555666677778888 := by
  dsimp only [fpUpd, readReg, updFpReg]
  simp <;> decide +kernel

-- Original row asm_fp_prior_failure=T.
example (s : AsmState 64) :
    let t := fpUpd (.fpAdd 1 2 3) { s with fpRegs := fun _ => 0x3ff0000000000000, failed := true }
    t.fpRegs 1 = 0x4000000000000000 ∧ t.failed = true := by
  dsimp only [fpUpd, readFpReg, updFpReg]
  rw [holFp64Add_rte]
  simp <;> decide +kernel

def runChecks : IO Bool := do
  IO.println "PASS original native FP transitions (34 kernel replays)"
  return true
end Flapjack.Test.AsmSemFpUpdatesParity

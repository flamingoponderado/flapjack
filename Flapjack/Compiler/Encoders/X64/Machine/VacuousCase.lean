module

public import Flapjack.Compiler.Encoders.X64.Machine.ControlCase

@[expose] public section

/-!
# The vacuous x64 cases of `encoder_correct x64Target`

`asm_step` requires `asm_ok i x64_config = true`.  Three `HolAsm` forms are
rejected by the x86-64 configuration, so their cases of `encoder_correct` are
vacuous:

* `call` — `x64_config.link_reg = none`, and `asm_ok` rejects a call without a
  link register;
* `arith (.div ...)` — the configuration's ISA is x86-64, and `asm_ok` only
  accepts `div` on ARMv8, MIPS and RISC-V;
* `fp (.fpFma ...)` — `asm_ok` only accepts the fused multiply-add on ARMv7.

The x86-64 encoder does emit a failure byte for `call` and an empty lowering
for `div` and `fma`, but no `asm_step` can reach those forms, so the cases hold
vacuously.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-- `asm_ok` rejects a `call` on x86-64: the configuration has no link
register. -/
theorem x64AsmOk_call_false (target : BitVec 64) :
    asmOkExact (.call target) x64Config = false := by
  simp [asmOkExact, x64Config]

/-- `asm_ok` rejects `arith (.div ...)` on x86-64. -/
theorem x64AsmOk_div_false (destination dividend divisor : Nat) :
    asmOkExact (.inst (.arith (.div destination dividend divisor))) x64Config = false := by
  simp [asmOkExact, asmInstOkExact, asmArithOkExact, x64Config]

/-- `asm_ok` rejects `fp (.fpFma ...)` on x86-64. -/
theorem x64AsmOk_fpFma_false (destination left right : Nat) :
    asmOkExact (.inst (.fp (.fpFma destination left right))) x64Config = false := by
  simp [asmOkExact, asmInstOkExact, asmFpOkExact, x64Config]

/-- The `call` constructor of `encoder_correct x64Target` is vacuous. -/
theorem case_call (target : BitVec 64) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.call target) s2 ∧ targetStateRel x64Target s1 ms) :
    CaseGoal (.call target) s1 s2 ms := by
  have st := x64Start (.call target) s1 s2 ms h
  have hok := st.asmOk
  simp only [x64Target_config] at hok
  rw [x64AsmOk_call_false] at hok
  exact absurd hok (by simp)

/-- The `arith (.div ...)` constructor of `encoder_correct x64Target` is
vacuous. -/
theorem case_div (destination dividend divisor : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.arith (.div destination dividend divisor))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.arith (.div destination dividend divisor))) s1 s2 ms := by
  have st := x64Start (.inst (.arith (.div destination dividend divisor))) s1 s2 ms h
  have hok := st.asmOk
  simp only [x64Target_config] at hok
  rw [x64AsmOk_div_false] at hok
  exact absurd hok (by simp)

/-- The `fp (.fpFma ...)` constructor of `encoder_correct x64Target` is
vacuous. -/
theorem case_fpFma (destination left right : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp (.fpFma destination left right))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.fp (.fpFma destination left right))) s1 s2 ms := by
  have st := x64Start (.inst (.fp (.fpFma destination left right))) s1 s2 ms h
  have hok := st.asmOk
  simp only [x64Target_config] at hok
  rw [x64AsmOk_fpFma_false] at hok
  exact absurd hok (by simp)

end Flapjack.Compiler.Encoders.X64

import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Simulate

set_option maxHeartbeats 4000000

/-!
# The `Fp` constructor of `encoder_correct arm8TargetL3`

`arm8_ast` lowers `FP f` to `arm8_encode_fail`, and the L3 `arm8_config` has no
FP registers (`fp_reg_count = 0`), so `fp_ok` rejects every FP instruction and
`asm_step` is impossible for this constructor.  The case is therefore vacuous,
as in the HOL proof's `FP` branch.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- With `fp_reg_count = 0`, every FP operation fails `fp_ok`. -/
theorem arm8FpOk_false (operation : HolFp) :
    asmFpOkExact operation arm8ConfigL3 = false := by
  cases operation <;> simp [asmFpOkExact, asmFpRegOkExact, arm8ConfigL3]

/-- The `Fp` constructor of `encoder_correct arm8TargetL3`: `asm_ok` rejects
every FP instruction, so the `asm_step` premise is unsatisfiable. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_fp (operation : HolFp) (s1 s2 : AsmState 64)
    (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.fp operation)) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.fp operation)) s1 s2 ms := by
  obtain ⟨hs, _⟩ := h
  have hok := hs.2.2.2.2.2.2
  simp only [asmOkExact, asmInstOkExact, arm8FpOk_false] at hok
  exact absurd hok (by simp)

end Flapjack.Compiler.Encoders.Arm8.L3

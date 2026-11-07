import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Simulate

set_option maxHeartbeats 4000000

/-!
# The `longDiv` constructor of `encoder_correct arm8TargetL3`

`arm8_ast` lowers `LongDiv` to `arm8_encode_fail` (a `NoOperation`), but the
CakeML `arith_ok` admits `LongDiv` only on `x86_64`
(`cakeml/compiler/encoders/asm/asmScript.sml:214-216`).  The L3 `arm8_config`
has `ISA = ARMv8`, so `asm_ok` rejects every `LongDiv` and `asm_step` is
impossible for this constructor.  The case is therefore vacuous, as in the HOL
proof's `LongDiv` branch.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- `arith_ok` requires `ISA = x86_64` for `LongDiv`; the L3 config is ARMv8. -/
theorem arm8LongDivOk_false (destinationLeft destinationRight sourceLeft sourceRight
    quotient : Nat) :
    asmArithOkExact (.longDiv destinationLeft destinationRight sourceLeft sourceRight
      quotient) arm8ConfigL3 = false := by
  simp [asmArithOkExact, arm8ConfigL3]

/-- The `longDiv` constructor of `encoder_correct arm8TargetL3`: `asm_ok`
rejects every `LongDiv` on ARMv8, so the `asm_step` premise is unsatisfiable. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_longDiv (destinationLeft destinationRight sourceLeft
    sourceRight quotient : Nat) (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1
      (.inst (.arith (.longDiv destinationLeft destinationRight sourceLeft sourceRight
        quotient))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.longDiv destinationLeft destinationRight sourceLeft
      sourceRight quotient))) s1 s2 ms := by
  obtain ⟨hs, _⟩ := h
  have hok := hs.2.2.2.2.2.2
  simp only [asmOkExact, asmInstOkExact, arm8LongDivOk_false] at hok
  exact absurd hok (by simp)

end Flapjack.Compiler.Encoders.Arm8.L3

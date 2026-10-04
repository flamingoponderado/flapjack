import Flapjack.RiscV.CorrectnessEncoding.ShiftLslRegister
import Flapjack.RiscV.CorrectnessEncoding.ShiftLslImmediate
import Flapjack.RiscV.CorrectnessEncoding.ShiftLsrRegister
import Flapjack.RiscV.CorrectnessEncoding.ShiftLsrImmediate
import Flapjack.RiscV.CorrectnessEncoding.ShiftAsrRegister
import Flapjack.RiscV.CorrectnessEncoding.ShiftAsrImmediate
import Flapjack.RiscV.CorrectnessEncoding.ShiftRorRegister
import Flapjack.RiscV.CorrectnessEncoding.ShiftRorImmediate

namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target
set_option autoImplicit false

/-- Full original Shift constructor (source560-620), assembled over all four
operators and both Reg/Imm forms. Sole original source-step/initial relation
premise and complete existential all-environment assertions remain unchanged.
Each concrete case derives actual native Next from emitted bytes, including
zero-count Ror and legal aliases. Inherits reals_as_rational_cuts through native
state closure (SOUNDNESS item8). `CorrectnessEncoding.Complete`
assembles the full encoder correctness theorem. -/
@[hol "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml"
  "riscv_encoder_correct"]
theorem riscv_encoder_correct_shift (op : Flapjack.Shift) (rd rs1 : Nat) (right : HolRegImm 64) (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.inst (.arith (.shift op rd rs1 right))) s2 ∧
      targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.inst (.arith (.shift op rd rs1 right)))).length s1.pc
      asserts n (fun k s => env (n - k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  cases op <;> cases right
  · exact riscv_encoder_correct_shiftLslRegister rd rs1 _ s1 s2 ms h
  · exact riscv_encoder_correct_shiftLslImmediate rd rs1 _ s1 s2 ms h
  · exact riscv_encoder_correct_shiftLsrRegister rd rs1 _ s1 s2 ms h
  · exact riscv_encoder_correct_shiftLsrImmediate rd rs1 _ s1 s2 ms h
  · exact riscv_encoder_correct_shiftAsrRegister rd rs1 _ s1 s2 ms h
  · exact riscv_encoder_correct_shiftAsrImmediate rd rs1 _ s1 s2 ms h
  · exact riscv_encoder_correct_shiftRorRegister rd rs1 _ s1 s2 ms h
  · exact riscv_encoder_correct_shiftRorImmediate rd rs1 _ s1 s2 ms h

end Flapjack.RiscV.TargetProof

import Flapjack.RiscV.CorrectnessEncoding.TargetOk
import Flapjack.RiscV.CorrectnessEncoding.Skip
import Flapjack.RiscV.CorrectnessEncoding.ConstAssertions
import Flapjack.RiscV.CorrectnessEncoding.Binop
import Flapjack.RiscV.CorrectnessEncoding.Shift
import Flapjack.RiscV.CorrectnessEncoding.Div
import Flapjack.RiscV.CorrectnessEncoding.LongMul
import Flapjack.RiscV.CorrectnessEncoding.Rejected
import Flapjack.RiscV.CorrectnessEncoding.AddCarry
import Flapjack.RiscV.CorrectnessEncoding.AddOverflow
import Flapjack.RiscV.CorrectnessEncoding.SubOverflow
import Flapjack.RiscV.CorrectnessEncoding.MemoryAssertions
import Flapjack.RiscV.CorrectnessEncoding.Jump
import Flapjack.RiscV.CorrectnessEncoding.JumpCmp
import Flapjack.RiscV.CorrectnessEncoding.Call
import Flapjack.RiscV.CorrectnessEncoding.JumpReg
import Flapjack.RiscV.CorrectnessEncoding.Loc
import Flapjack.Compiler.Encoders.AsmProps.EncoderCorrect

/-! Full native encoder correctness for the original complete assembler carrier.
All seventeen HOL constructor groups are assembled without extra hypotheses.
The native model retains the reviewed reals_as_rational_cuts assurance limit
(SOUNDNESS section 8); this theorem does not establish production compiler
routing or the whole Pancake-to-RISC-V correctness result. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 Compiler.Encoders.Asm Compiler.Encoders.AsmProps
  Compiler.Encoders.RiscV.Target
set_option autoImplicit false

/-- Original unconditional encoder_correct riscv_target, including target_ok,
every source instruction, every interference environment and both assertions.
The component proofs derive native fetch/decode/Run/Next from the actual emitted
bytes. Inherits reals_as_rational_cuts (SOUNDNESS section 8). -/
@[hol "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml"
  "riscv_encoder_correct"]
theorem riscv_encoder_correct : encoderCorrect riscvTarget := by
  refine ⟨riscv_target_ok, ?_⟩
  intro s1 i s2 ms h
  cases i with
  | inst value =>
    cases value with
    | skip => exact riscv_encoder_correct_skip s1 s2 ms h
    | const r c => exact riscv_encoder_correct_const r c s1 s2 ms h
    | arith a =>
      cases a with
      | binop op r t right => exact riscv_encoder_correct_binop op r t right s1 s2 ms h
      | shift op r t right => exact riscv_encoder_correct_shift op r t right s1 s2 ms h
      | div r t u => exact riscv_encoder_correct_div r t u s1 s2 ms h
      | longMul r t u v => exact riscv_encoder_correct_longmul r t u v s1 s2 ms h
      | longDiv r t u v q => exact riscv_encoder_correct_longdiv r t u v q s1 s2 ms h
      | addCarry r t u v => exact riscv_encoder_correct_addcarry r t u v s1 s2 ms h
      | addOverflow r t u v => exact riscv_encoder_correct_addoverflow r t u v s1 s2 ms h
      | subOverflow r t u v => exact riscv_encoder_correct_suboverflow r t u v s1 s2 ms h
    | mem m r address =>
      cases address with
      | addr base w => exact riscv_encoder_correct_mem m r base w s1 s2 ms h
    | fp f => exact riscv_encoder_correct_fp f s1 s2 ms h
  | jump c => exact riscv_encoder_correct_jump c s1 s2 ms h
  | jumpCmp c r right a => exact riscv_encoder_correct_jumpCmp c r right a s1 s2 ms h
  | call c => exact riscv_encoder_correct_call c s1 s2 ms h
  | jumpReg r => exact riscv_encoder_correct_jumpReg r s1 s2 ms h
  | loc r c => exact riscv_encoder_correct_loc r c s1 s2 ms h

end Flapjack.RiscV.TargetProof

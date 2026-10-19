import Flapjack.Compiler.Encoders.Arm8.Machine.MemCaseFull
import Flapjack.Compiler.Encoders.Arm8.Machine.TargetProof

/-! # `encoder_correct arm8Target`

The ARM8 target satisfies CakeML's `encoder_correct`
(`asmPropsScript.sml`): `target_ok` and the simulation of every asm
instruction that the closed ARM8 subset can emit, under every
projection-preserving interference environment.

This is the obligation `mc_conf_ok` asks of a machine configuration, so it is
what instantiates the Pancake-to-target theorem at ARM8.  It is Flapjack
infrastructure: it is the analogue of HOL's `arm8_encoder_correct`
(`cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml`), which is
about the full L3 ARMv8 model, so it carries no `@[hol]` tag and no claim of an
L3 port.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-- `encoder_correct` for the closed ARM8 target: `target_ok` and every source
instruction, every interference environment, both assertions. -/
theorem arm8EncoderCorrect : encoderCorrect arm8Target := by
  refine ⟨arm8TargetOk, ?_⟩
  intro s1 i s2 ms h
  cases i with
  | inst v =>
    cases v with
    | skip => exact case_skip s1 s2 ms h
    | const r c => exact case_const r c s1 s2 ms h
    | arith a =>
      cases a with
      | binop op r t right =>
        cases right with
        | reg u => exact case_binop_reg op r t u s1 s2 ms h
        | imm w => exact case_binop_imm op r t w s1 s2 ms h
      | shift op r t right =>
        cases right with
        | reg u => exact case_shift_reg op r t u s1 s2 ms h
        | imm w => exact case_shift_imm op r t w s1 s2 ms h
      | div r t u => exact case_div r t u s1 s2 ms h
      | longMul r t u v => exact case_longMul r t u v s1 s2 ms h
      | longDiv r t u v q => exact case_longDiv r t u v q s1 s2 ms h
      | addCarry r t u v => exact case_addCarry r t u v s1 s2 ms h
      | addOverflow r t u v => exact case_addOverflow r t u v s1 s2 ms h
      | subOverflow r t u v => exact case_subOverflow r t u v s1 s2 ms h
    | mem m r address =>
      cases address with
      | addr base w =>
        cases m with
        | load => exact case_load r base w s1 s2 ms h
        | load8 => exact case_load8 r base w s1 s2 ms h
        | load16 => exact case_load16 r base w s1 s2 ms h
        | load32 => exact case_load32 r base w s1 s2 ms h
        | store => exact case_store r base w s1 s2 ms h
        | store8 => exact case_store8 r base w s1 s2 ms h
        | store16 => exact case_store16 r base w s1 s2 ms h
        | store32 => exact case_store32 r base w s1 s2 ms h
    | fp f => exact case_fp f s1 s2 ms h
  | jump a => exact case_jump a s1 s2 ms h
  | jumpCmp c r right a =>
    cases right with
    | reg u => exact case_jumpCmp_reg c r u a s1 s2 ms h
    | imm w => exact case_jumpCmp_imm c r w a s1 s2 ms h
  | call a => exact case_call a s1 s2 ms h
  | jumpReg r => exact case_jumpReg r s1 s2 ms h
  | loc r c => exact case_loc r c s1 s2 ms h

end Flapjack.Compiler.Encoders.Arm8

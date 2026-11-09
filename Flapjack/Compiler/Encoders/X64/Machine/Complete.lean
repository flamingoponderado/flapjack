module

public import Flapjack.Compiler.Encoders.X64.Machine.JumpCmpCase
public import Flapjack.Compiler.Encoders.X64.Machine.LocCase
public import Flapjack.Compiler.Encoders.X64.Machine.MemCase

@[expose] public section

/-!
# `encoder_correct x64Target`

The x86-64 target satisfies CakeML's `encoder_correct`
(`asmPropsScript.sml`): `target_ok` and the simulation of every asm
instruction that the closed x86-64 subset can emit, under every
projection-preserving interference environment.

Each constructor is proved in its own module under `Machine/`: the arithmetic,
memory, floating-point, control and conditional-branch cases, plus the vacuous
cases the backend never emits.  This is Flapjack infrastructure: it is the
analogue of HOL's per-target encoder-correctness theorems, which are about the
full L3 models, so it carries no `@[hol]` tag and no claim of an L3 port.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-- `encoder_correct` for the closed x86-64 target: `target_ok` and every source
instruction, every interference environment, both assertions. -/
theorem x64EncoderCorrect : encoderCorrect x64Target := by
  refine ⟨x64TargetOk, ?_⟩
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
        | reg u => exact case_binopRR op r t u s1 s2 ms h
        | imm w => exact case_binopRI op r t w s1 s2 ms h
      | shift op r t right =>
        cases right with
        | reg u => exact case_shiftReg op r t u s1 s2 ms h
        | imm w => exact case_shiftImm op r t w s1 s2 ms h
      | div r t u => exact case_div r t u s1 s2 ms h
      | longMul r1 r2 r3 r4 => exact case_longMul r1 r2 r3 r4 s1 s2 ms h
      | longDiv r1 r2 r3 r4 q => exact case_longDiv r1 r2 r3 r4 q s1 s2 ms h
      | addCarry r1 r2 r3 r4 => exact case_addCarry r1 r2 r3 r4 s1 s2 ms h
      | addOverflow d rc sl sr => exact case_addOverflow d rc sl sr s1 s2 ms h
      | subOverflow d rc sl sr => exact case_subOverflow d rc sl sr s1 s2 ms h
    | mem m r address =>
      cases address with
      | addr base off =>
        cases m with
        | load => exact case_load r base off s1 s2 ms h
        | load8 => exact case_load8 r base off s1 s2 ms h
        | load16 => exact case_load16 r base off s1 s2 ms h
        | load32 => exact case_load32 r base off s1 s2 ms h
        | store => exact case_store r base off s1 s2 ms h
        | store8 => exact case_store8 r base off s1 s2 ms h
        | store16 => exact case_store16 r base off s1 s2 ms h
        | store32 => exact case_store32 r base off s1 s2 ms h
    | fp f =>
      cases f with
      | fpLess n d1 d2 => exact case_fpLess n d1 d2 s1 s2 ms h
      | fpLessEqual n d1 d2 => exact case_fpLessEqual n d1 d2 s1 s2 ms h
      | fpEqual n d1 d2 => exact case_fpEqual n d1 d2 s1 s2 ms h
      | fpAbs d1 d2 => exact case_fpAbs d1 d2 s1 s2 ms h
      | fpNeg d1 d2 => exact case_fpNeg d1 d2 s1 s2 ms h
      | fpSqrt d1 d2 => exact case_fpSqrt d1 d2 s1 s2 ms h
      | fpAdd d l r => exact case_fpAdd d l r s1 s2 ms h
      | fpSub d l r => exact case_fpSub d l r s1 s2 ms h
      | fpMul d l r => exact case_fpMul d l r s1 s2 ms h
      | fpDiv d l r => exact case_fpDiv d l r s1 s2 ms h
      | fpFma d l r => exact case_fpFma d l r s1 s2 ms h
      | fpMov d1 d2 => exact case_fpMov d1 d2 s1 s2 ms h
      | fpMovToReg r1 r2 d => exact case_fpMovToReg r1 r2 d s1 s2 ms h
      | fpMovFromReg d r1 r2 => exact case_fpMovFromReg d r1 r2 s1 s2 ms h
      | fpToInt d1 d2 => exact case_fpToInt d1 d2 s1 s2 ms h
      | fpFromInt d1 d2 => exact case_fpFromInt d1 d2 s1 s2 ms h
  | jump a => exact case_jump a s1 s2 ms h
  | jumpCmp c r right a =>
    cases right with
    | reg u => exact case_jumpCmp_reg c r u a s1 s2 ms h
    | imm w => exact case_jumpCmp_imm c r w a s1 s2 ms h
  | call a => exact case_call a s1 s2 ms h
  | jumpReg r => exact case_jumpReg r s1 s2 ms h
  | loc r c => exact case_loc r c s1 s2 ms h

end Flapjack.Compiler.Encoders.X64

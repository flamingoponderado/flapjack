import Flapjack.Compiler.Encoders.X64.Encode
import Flapjack.Compiler.Encoders.AsmSem.Arithmetic
import Flapjack.HolRef

/-!
# x86-64 target lowering

This module ports `x64_ast`, `x64_encode` and `x64_enc` from
`cakeml/compiler/encoders/x64/x64_targetScript.sml`, restricted to the
instruction forms the CakeML x86-64 backend emits.  The lowering is compared
byte-for-byte with the original compiler by the parity fixtures; see
`docs/X64.md`.

`x64_ast` in HOL maps each `asm` instruction to a list of L3 `instruction`s;
`x64_encode` maps each to bytes, overriding the L3 encoder for conditional
jumps (the L3 encoder can choose short branches); `x64_enc` concatenates the
bytes, substituting `[0]` when the result is empty.

The declarations are not exact `@[hol]` ports: HOL's `x64_ast` ranges over the
full L3 `instruction` datatype, while `X64Insn` is the emitted subset.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem

/-- `x64_bop`: source binops to L3 `Zbinop_name`. -/
def x64Bop : BinOp → ZBinopName
  | .add => .zadd
  | .sub => .zsub
  | .and => .zand
  | .or => .zor
  | .xor => .zxor

/-- `x64_sh`: source shifts to L3 `Zbinop_name`. -/
def x64Sh : Shift → ZBinopName
  | .lsl => .zshl
  | .lsr => .zshr
  | .asr => .zsar
  | .ror => .zror

/-- `x64_cmp`: source comparisons to L3 `Zcond`. -/
def x64Cmp : Cmp → ZCond
  | .less => .zL
  | .lower => .zB
  | .equal => .zE
  | .test => .zE
  | .notLess => .zNL
  | .notLower => .zNB
  | .notEqual => .zNE
  | .notTest => .zNE

/-- `x64_ast` for the emitted `Inst` forms. -/
def x64Inst : HolInst 64 → List X64Insn
  | .skip => [.nop 1]
  | .const r i =>
      if i.toNat / 2 ^ 31 = 0 then
        if i = 0 then [.binopRR .zxor .z32 r (totalNum2Zreg r)]
        else [.movRI .z32 (totalNum2Zreg r) i]
      else
        if i = 0 then [.binopRR .zxor .z32 r (totalNum2Zreg r)]
        else [.movRI .z64 (totalNum2Zreg r) i]
  | .arith (.binop bop r1 r2 (.reg r3)) =>
      if bop = .or && r2 = r3 then
        [.movRR .z64 (totalNum2Zreg r1) (totalNum2Zreg r3)]
      else
        [.binopRR (x64Bop bop) .z64 (totalNum2Zreg r1) (totalNum2Zreg r3)]
  | .arith (.binop bop r _ (.imm i)) =>
      if bop = .xor && i = -1 then
        [.monop .znot .z64 (totalNum2Zreg r)]
      else
        [.binopRI (x64Bop bop) .z64 (totalNum2Zreg r) i]
  | .arith (.shift sh r _ (.imm i)) =>
      [.binopRI (x64Sh sh) .z64 (totalNum2Zreg r) i]
  | .arith (.shift sh r1 _ (.reg r2)) =>
      [.binopRR (x64Sh sh) .z64 (totalNum2Zreg r1) (totalNum2Zreg r2)]
  | .arith (.div _ _ _) => []
  | .arith (.longMul _ _ _ r) => [.mul .z64 (totalNum2Zreg r)]
  | .arith (.longDiv _ _ _ _ r) => [.div .z64 (totalNum2Zreg r)]
  | .arith (.addCarry r1 _ r3 r4) =>
      [.binopRI .zcmp .z64 (totalNum2Zreg r4) 1,
       .cmc,
       .binopRR .zadc .z64 (totalNum2Zreg r1) (totalNum2Zreg r3),
       .movRI .z32 (totalNum2Zreg r4) 0,
       .setcc .zB true (totalNum2Zreg r4)]
  | .arith (.addOverflow r1 _ r2 r3) =>
      [.binopRR .zadd .z64 (totalNum2Zreg r1) (totalNum2Zreg r2),
       .movRI .z32 (totalNum2Zreg r3) 0,
       .setcc .zO true (totalNum2Zreg r3)]
  | .arith (.subOverflow r1 _ r2 r3) =>
      [.binopRR .zsub .z64 (totalNum2Zreg r1) (totalNum2Zreg r2),
       .movRI .z32 (totalNum2Zreg r3) 0,
       .setcc .zO true (totalNum2Zreg r3)]
  | .mem .load r1 (.addr r2 a) =>
      [.movRM .z64 (totalNum2Zreg r1) (totalNum2Zreg r2) a]
  | .mem .load32 r1 (.addr r2 a) =>
      [.movRM .z32 (totalNum2Zreg r1) (totalNum2Zreg r2) a]
  | .mem .load16 r1 (.addr r2 a) =>
      [.movzxRM .z16 .z64 (totalNum2Zreg r1) (totalNum2Zreg r2) a]
  | .mem .load8 r1 (.addr r2 a) =>
      [.movzxRM (.z8 true) .z64 (totalNum2Zreg r1) (totalNum2Zreg r2) a]
  | .mem .store r1 (.addr r2 a) =>
      [.movMR .z64 (totalNum2Zreg r1) (totalNum2Zreg r2) a]
  | .mem .store32 r1 (.addr r2 a) =>
      [.movMR .z32 (totalNum2Zreg r1) (totalNum2Zreg r2) a]
  | .mem .store16 r1 (.addr r2 a) =>
      [.movMR .z16 (totalNum2Zreg r1) (totalNum2Zreg r2) a]
  | .mem .store8 r1 (.addr r2 a) =>
      [.movMR (.z8 (3 < r1)) (totalNum2Zreg r1) (totalNum2Zreg r2) a]
  | .fp (.fpLess n d1 d2) =>
      [.sse (.comisd (d1 % 8) (d2 % 8)),
       .movRI .z32 (totalNum2Zreg n) 0,
       .jcc .zP 4,
       .setcc .zB true (totalNum2Zreg n)]
  | .fp (.fpLessEqual n d1 d2) =>
      [.sse (.comisd (d1 % 8) (d2 % 8)),
       .movRI .z32 (totalNum2Zreg n) 0,
       .jcc .zP 4,
       .setcc .zNA true (totalNum2Zreg n)]
  | .fp (.fpEqual n d1 d2) =>
      [.sse (.comisd (d1 % 8) (d2 % 8)),
       .movRI .z32 (totalNum2Zreg n) 0,
       .jcc .zP 4,
       .setcc .zE true (totalNum2Zreg n)]
  | .fp (.fpMov d1 d2) => [.sse (.movsd (d1 % 8) (d2 % 8))]
  | .fp (.fpAbs d1 d2) =>
      [.sse (.pcmpeqq (d1 % 8) (d1 % 8)),
       .sse (.psrlqImm (d1 % 8) 1),
       .sse (.logicPD .sseAnd (d1 % 8) (d2 % 8))]
  | .fp (.fpNeg d1 d2) =>
      [.sse (.pcmpeqq (d1 % 8) (d1 % 8)),
       .sse (.psllqImm (d1 % 8) 63),
       .sse (.logicPD .sseXor (d1 % 8) (d2 % 8))]
  | .fp (.fpSqrt d1 d2) => [.sse (.sqrtsd (d1 % 8) (d2 % 8))]
  | .fp (.fpAdd d1 _ d2) => [.sse (.binSD .sseAdd (d1 % 8) (d2 % 8))]
  | .fp (.fpSub d1 _ d2) => [.sse (.binSD .sseSub (d1 % 8) (d2 % 8))]
  | .fp (.fpMul d1 _ d2) => [.sse (.binSD .sseMul (d1 % 8) (d2 % 8))]
  | .fp (.fpDiv d1 _ d2) => [.sse (.binSD .sseDiv (d1 % 8) (d2 % 8))]
  | .fp (.fpFma _ _ _) => [.nop 1]
  | .fp (.fpMovToReg r1 _ d) =>
      [.sse (.movDQ false true (d % 8) (.zr (totalNum2Zreg r1)))]
  | .fp (.fpMovFromReg d r1 _) =>
      [.sse (.movDQ true true (d % 8) (.zr (totalNum2Zreg r1)))]
  | .fp (.fpToInt d1 d2) =>
      [.sse (.cvtpd2dq false (d1 % 8) (d2 % 8)),
       .sse (.pslldq (d1 % 8) 12),
       .sse (.psrldq (d1 % 8) 12)]
  | .fp (.fpFromInt d1 d2) => [.sse (.cvtdq2pd (d1 % 8) (d2 % 8))]

/-- `x64_ast`: lower an `asm` instruction to x86-64 instruction forms. -/
def x64Ast : HolAsm 64 → List X64Insn
  | .inst instruction => x64Inst instruction
  | .jump target => [.jcc .zAlways (target - 5)]
  | .jumpCmp operator source (.reg right) target =>
      [.binopRR (if isTest operator then .ztest else .zcmp) .z64
          (totalNum2Zreg source) (totalNum2Zreg right),
       .jcc (x64Cmp operator) (target - 9)]
  | .jumpCmp operator source (.imm value) target =>
      let width :=
        if !isTest operator && -128 ≤ value.toInt && value.toInt ≤ 127 then 10
        else if source % 16 = 0 then 12
        else 13
      [.binopRI (if isTest operator then .ztest else .zcmp) .z64
          (totalNum2Zreg source) value,
       .jcc (x64Cmp operator) (target - BitVec.ofNat 64 width)]
  | .call _ => []
  | .jumpReg register => [.jmp (totalNum2Zreg register)]
  | .loc register offset =>
      [.lea .z64 (totalNum2Zreg register) (offset - 7)]

/-- `x64_enc`: lower and encode, concatenating the bytes of every instruction
in the list; an empty result becomes the one-byte failure encoding `[0]`. -/
def x64Enc (instruction : HolAsm 64) : List (BitVec 8) :=
  match (x64Ast instruction).flatMap encodeInsn with
  | [] => [0]
  | l => l

/-- The 32-bit signed range bounds as 64-bit words: `sw2sw INT_MINw` and
`sw2sw INT_MAXw`. -/
def x64Min32 : BitVec 64 := BitVec.ofInt 64 (-(2 ^ 31))
def x64Max32 : BitVec 64 := BitVec.ofInt 64 (2 ^ 31 - 1)

/-- `x64_config`: the x86-64 assembler configuration.  `encode` is the
emitted-subset encoder, so the record is not an exact `x64_config` port; every
bound is CakeML's. -/
def x64Config : AsmConfigExact 64 where
  isa := .x86_64
  encode := x64Enc
  regCount := 16
  fpRegCount := 8
  avoidRegs := [4, 5]
  linkReg := none
  twoRegArith := true
  bigEndian := false
  validImm := fun _ i =>
    decide (x64Min32.toInt ≤ i.toInt ∧ i.toInt ≤ x64Max32.toInt)
  addrOffset := (x64Min32, x64Max32)
  hwOffset := (x64Min32, x64Max32)
  byteOffset := (x64Min32, x64Max32)
  jumpOffset := (x64Min32 + 13, x64Max32 + 5)
  cjumpOffset := (x64Min32 + 13, x64Max32 + 5)
  locOffset := (x64Min32 + 7, x64Max32 + 7)
  codeAlignment := 0

/-- Derived projection of the whole source record. -/
theorem x64Config_encode : x64Config.encode = x64Enc := rfl

end Flapjack.Compiler.Encoders.X64

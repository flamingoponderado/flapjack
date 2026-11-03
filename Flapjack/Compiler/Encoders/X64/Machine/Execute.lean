import Flapjack.Compiler.Encoders.X64.Machine.Decode
import Flapjack.Compiler.Encoders.AsmSem.Step
import Flapjack.Compiler.Backend.Semantics.WordSem.Inst

/-!
# Executing the decoded x86-64 subset

The closed model's arithmetic, flag and memory semantics.  Integer operations
follow x86-64's architectural effects; floating-point operations use the same
`holFp64*` functions that `asmSem`'s `fp_upd` uses, so the model's FP results
agree with the source semantics by construction.  This is not a port of the L3
`x64$Run` function.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-- Parity of the low byte, in x86 `PF` form: true when the number of set bits
is even.  The XOR fold therefore starts from `true`, not `false`. -/
def parityByte (value : BitVec 64) : Bool :=
  (List.range 8).foldl (fun acc i => xor acc (value.toNat / 2 ^ i % 2 = 1)) true

/-- `PF` regression: a zero low byte has even parity, so `PF` is set. -/
theorem parityByte_zero : parityByte 0 = true := by decide

/-- `PF` regression: a low byte of `1` has odd parity, so `PF` is clear. -/
theorem parityByte_one : parityByte 1 = false := by decide

/-- The flags produced by an addition. -/
def addFlags (a b : BitVec 64) : X64Flags :=
  let r := a + b
  { cf := decide (2 ^ 64 ≤ a.toNat + b.toNat)
    pf := parityByte r
    af := decide (16 ≤ a.toNat % 16 + b.toNat % 16)
    zf := r = 0
    sf := r.msb
    of := decide (r.toInt ≠ a.toInt + b.toInt) }

/-- The flags produced by a subtraction. -/
def subFlags (a b : BitVec 64) : X64Flags :=
  let r := a - b
  { cf := decide (a.toNat < b.toNat)
    pf := parityByte r
    af := decide (a.toNat % 16 < b.toNat % 16)
    zf := r = 0
    sf := r.msb
    of := decide (r.toInt ≠ a.toInt - b.toInt) }

/-- The flags produced by a logical operation (`and`, `or`, `xor`, `test`). -/
def logicFlags (r : BitVec 64) : X64Flags :=
  { cf := false, pf := parityByte r, af := false, zf := r = 0, sf := r.msb, of := false }

/-- The flags produced by `inc`. -/
def incFlags (a : BitVec 64) (old : X64Flags) : X64Flags :=
  let r := a + 1
  { old with
    pf := parityByte r
    af := a.toNat % 16 = 15
    zf := r = 0
    sf := r.msb
    of := a = BitVec.ofNat 64 (2 ^ 63 - 1) }

/-- The flags produced by `dec`. -/
def decFlags (a : BitVec 64) (old : X64Flags) : X64Flags :=
  let r := a - 1
  { old with
    pf := parityByte r
    af := a.toNat % 16 = 0
    zf := r = 0
    sf := r.msb
    of := a = BitVec.ofInt 64 (-(2 ^ 63)) }

/-- The flags produced by `adc` with carry-in `cin`. -/
def adcFlags (a b : BitVec 64) (cin : Bool) : X64Flags :=
  let c : Nat := if cin then 1 else 0
  let r := a + b + BitVec.ofNat 64 c
  { cf := decide (2 ^ 64 ≤ a.toNat + b.toNat + c)
    pf := parityByte r
    af := decide (16 ≤ a.toNat % 16 + b.toNat % 16 + c)
    zf := r = 0
    sf := r.msb
    of := decide (r.toInt ≠ a.toInt + b.toInt + c) }

/-- Evaluate a condition code against the flags. -/
def evalCond (cond : ZCond) (f : X64Flags) : Bool :=
  match cond with
  | .zO => f.of
  | .zNO => !f.of
  | .zB => f.cf
  | .zNB => !f.cf
  | .zE => f.zf
  | .zNE => !f.zf
  | .zNA => f.cf || f.zf
  | .zA => !f.cf && !f.zf
  | .zS => f.sf
  | .zNS => !f.sf
  | .zP => f.pf
  | .zNP => !f.pf
  | .zL => f.sf ≠ f.of
  | .zNL => f.sf = f.of
  | .zNG => f.zf || f.sf ≠ f.of
  | .zG => !f.zf && f.sf = f.of
  | .zAlways => true

/-- The value written by an arithmetic or logical binop. -/
def binopValue (op : ZBinopName) (a b : BitVec 64) : BitVec 64 :=
  match op with
  | .zadd | .zadc => a + b
  | .zsbb | .zsub | .zcmp => a - b
  | .zand | .ztest => a &&& b
  | .zor => a ||| b
  | .zxor => a ^^^ b
  | .zshl => a <<< b.toNat
  | .zshr => a >>> b.toNat
  | .zsar => BitVec.sshiftRight a b.toNat
  | .zror => BitVec.rotateRight a b.toNat
  | .zrol => BitVec.rotateLeft a b.toNat
  | .zrcl | .zrcr => a

/-- The flags written by an arithmetic or logical binop. -/
def binopFlags (op : ZBinopName) (a b : BitVec 64) (old : X64Flags) : X64Flags :=
  match op with
  | .zadd => addFlags a b
  | .zadc => adcFlags a b old.cf
  | .zsbb | .zsub | .zcmp => subFlags a b
  | .zand | .zor | .zxor | .ztest => logicFlags (binopValue op a b)
  | .zshl | .zshr | .zsar | .zror | .zrol | .zrcl | .zrcr => old

/-- The size in bytes of a memory operand. -/
def sizeBytes : ZSize → Nat
  | .z8 _ => 1
  | .z16 => 2
  | .z32 => 4
  | .z64 => 8

/-- Write a register with x86-64's zero-extension for 32-bit writes and
partial writes for 16/8-bit writes. -/
def writeRegSized (sz : ZSize) (dst : Nat) (value : BitVec 64) (s : X64State) : X64State :=
  match sz with
  | .z64 => writeReg s dst value
  | .z32 => writeReg s dst (BitVec.setWidth 64 (BitVec.setWidth 32 value))
  | .z16 =>
      let old := readReg s dst
      writeReg s dst (((BitVec.setWidth 64 (BitVec.setWidth 16 value)) |||
        (old &&& BitVec.ofNat 64 (2 ^ 64 - 2 ^ 16))))
  | .z8 _ =>
      let old := readReg s dst
      writeReg s dst (((BitVec.setWidth 64 (BitVec.setWidth 8 value)) |||
        (old &&& BitVec.ofNat 64 (2 ^ 64 - 2 ^ 8))))

/-- The effective address of a memory operand. -/
def effectiveAddress (s : X64State) (len : Nat) (rm : ZRM) : Option (BitVec 64) :=
  match rm with
  | .zr _ => none
  | .zm index base disp =>
      match index, base with
      | none, .regBase r => some (readReg s r + disp)
      | none, .ripBase => some (s.pc + BitVec.ofNat 64 len + disp)
      | none, .noBase => some disp
      | _, _ => none

/-- Logical right shift of each 64-bit lane of a 128-bit XMM value.
`psrlq` operates on the two packed 64-bit quadwords independently, so the
low lane must not receive bits from the high lane. -/
def psrlqLanes (v : BitVec 128) (n : Nat) : BitVec 128 :=
  ((((v >>> 64).setWidth 64) >>> n).setWidth 128) <<< 64 |||
    (((v.setWidth 64) >>> n).setWidth 128)

/-- Logical left shift of each 64-bit lane of a 128-bit XMM value. -/
def psllqLanes (v : BitVec 128) (n : Nat) : BitVec 128 :=
  ((((v >>> 64).setWidth 64) <<< n).setWidth 128) <<< 64 |||
    (((v.setWidth 64) <<< n).setWidth 128)

/-- Execute one SSE instruction.  The floating-point operations use the same
`holFp64*` functions as `fp_upd`, so their results agree with the source
semantics.  `sseMin`/`sseMax` are not emitted by the backend and are modelled
as the first operand. -/
noncomputable def execSSE (op : X64SSE) (s : X64State) : X64State :=
  match op with
  | .comisd dst src =>
      let a := readXmm s dst
      let b := readXmm s src
      let unordered := holFp64IsNan a || holFp64IsNan b
      { s with flags :=
          { cf := !unordered && holFp64LessThan a b
            pf := unordered
            af := false
            zf := !unordered && holFp64Equal a b
            sf := false
            of := false } }
  | .movsd dst src => writeXmm s dst (readXmm s src)
  | .pcmpeqq dst src =>
      let a := readXmm s dst
      let b := readXmm s src
      let mask : BitVec 128 := if a == b then BitVec.ofNat 128 (2 ^ 128 - 1) else 0
      { s with xmm := fun r => if r = dst % 8 then mask else s.xmm r }
  | .psrlqImm dst imm =>
      { s with xmm := fun r =>
          if r = dst % 8 then psrlqLanes (s.xmm (dst % 8)) imm.toNat else s.xmm r }
  | .psllqImm dst imm =>
      { s with xmm := fun r =>
          if r = dst % 8 then psllqLanes (s.xmm (dst % 8)) imm.toNat else s.xmm r }
  | .logicPD op dst src =>
      let a := readXmm s dst
      let b := readXmm s src
      let v := match op with
        | .sseAnd => a &&& b
        | .sseAndn => (~~~a) &&& b
        | .sseOr => a ||| b
        | .sseXor => a ^^^ b
      writeXmm s dst v
  | .sqrtsd dst src => writeXmm s dst (holFp64Sqrt .roundTiesToEven (readXmm s src))
  | .binSD bop dst src =>
      let a := readXmm s dst
      let b := readXmm s src
      let v := match bop with
        | .sseAdd => holFp64Add .roundTiesToEven a b
        | .sseSub => holFp64Sub .roundTiesToEven a b
        | .sseMul => holFp64Mul .roundTiesToEven a b
        | .sseDiv => holFp64Div .roundTiesToEven a b
        | .sseMin => a
        | .sseMax => a
      writeXmm s dst v
  | .movDQ toXmm quad xmm rm =>
      match rm with
      | .zr reg =>
          if toXmm then writeXmm s xmm (readReg s reg)
          else writeRegSized (if quad then .z64 else .z32) reg (readXmm s xmm) s
      | .zm _ _ _ =>
          match effectiveAddress s 0 rm with
          | some addr =>
              if toXmm then writeXmm s xmm (readMemN s (if quad then 8 else 4) addr)
              else writeMemN s (if quad then 8 else 4) addr (readXmm s xmm)
          | none => { s with failed := true }
  | .cvtpd2dq _truncate dst src =>
      match holFp64ToInt .roundTiesToEven (readXmm s src) with
      | none => { s with failed := true }
      | some integer =>
          let v : BitVec 32 := BitVec.ofInt 32 integer
          if v.toInt ≠ integer then { s with failed := true }
          else writeXmm s dst (BitVec.setWidth 64 v)
  | .pslldq dst imm =>
      { s with xmm := fun r =>
          if r = dst % 8 then (s.xmm (dst % 8)) <<< (8 * imm.toNat) else s.xmm r }
  | .psrldq dst imm =>
      { s with xmm := fun r =>
          if r = dst % 8 then (s.xmm (dst % 8)) >>> (8 * imm.toNat) else s.xmm r }
  | .cvtdq2pd dst src =>
      let integer := BitVec.setWidth 32 (readXmm s src)
      writeXmm s dst (holIntToFp64 .roundTiesToEven integer.toInt)

/-- Execute one decoded instruction.  `len` is its encoded length, needed for
RIP-relative addressing.  The PC is advanced by `x64Next`, not here. -/
noncomputable def execInsn (i : X64Insn) (len : Nat) (s : X64State) : X64State :=
  match i with
  | .nop _ => s
  | .movRR sz dst src => writeRegSized sz dst (readReg s src) s
  | .movRI sz dst imm => writeRegSized sz dst imm s
  | .movRM sz dst base disp =>
      let addr := readReg s base + disp
      writeRegSized sz dst (readMemN s (sizeBytes sz) addr) s
  | .movMR sz src base disp =>
      let addr := readReg s base + disp
      writeMemN s (sizeBytes sz) addr (readReg s src)
  | .movzxRM sz1 _ dst base disp =>
      let addr := readReg s base + disp
      writeReg s dst (readMemN s (sizeBytes sz1) addr)
  | .binopRI op sz dst imm =>
      let a := readReg s dst
      -- `adc`/`sbb` include the incoming carry flag in the written value; the
      -- `adc` flags below already do so.  `sbb`'s flags still omit the borrow,
      -- but the backend never emits it.
      let r :=
        match op with
        | .zadc => a + imm + BitVec.ofNat 64 (if s.flags.cf then 1 else 0)
        | .zsbb => a - imm - BitVec.ofNat 64 (if s.flags.cf then 1 else 0)
        | _ => binopValue op a imm
      let flags := binopFlags op a imm s.flags
      match op with
      | .zcmp | .ztest => { s with flags := flags }
      | _ => { (writeRegSized sz dst r s) with flags := flags }
  | .binopRR op sz dst src =>
      let a := readReg s dst
      let b := readReg s src
      -- `adc`/`sbb` include the incoming carry flag in the written value; the
      -- `adc` flags below already do so.  `sbb`'s flags still omit the borrow,
      -- but the backend never emits it.
      let r :=
        match op with
        | .zadc => a + b + BitVec.ofNat 64 (if s.flags.cf then 1 else 0)
        | .zsbb => a - b - BitVec.ofNat 64 (if s.flags.cf then 1 else 0)
        | _ => binopValue op a b
      let flags := binopFlags op a b s.flags
      match op with
      | .zcmp | .ztest => { s with flags := flags }
      | _ => { (writeRegSized sz dst r s) with flags := flags }
  | .monop op sz dst =>
      let a := readReg s dst
      match op with
      | .znot => writeRegSized sz dst (~~~a) s
      | .zneg => { (writeRegSized sz dst (0 - a) s) with flags := subFlags 0 a }
      | .zinc => { (writeRegSized sz dst (a + 1) s) with flags := incFlags a s.flags }
      | .zdec => { (writeRegSized sz dst (a - 1) s) with flags := decFlags a s.flags }
  | .mul _ src =>
      let a := readReg s 0
      let b := readReg s src
      let p : BitVec 128 := (a.setWidth 128) * (b.setWidth 128)
      let hi : BitVec 64 := (p >>> 64).setWidth 64
      let s' := writeReg (writeReg s 0 (p.setWidth 64)) 2 hi
      { s' with flags := { s.flags with cf := hi ≠ 0, of := hi ≠ 0 } }
  | .div _ src =>
      let hi := readReg s 2
      let lo := readReg s 0
      let d := readReg s src
      if d = 0 then { s with failed := true }
      else
        let n := hi.toNat * 2 ^ 64 + lo.toNat
        let q := n / d.toNat
        if q ≥ 2 ^ 64 then { s with failed := true }
        else writeReg (writeReg s 0 (BitVec.ofNat 64 q)) 2
          (BitVec.ofNat 64 (n % d.toNat))
  | .cmc => { s with flags := { s.flags with cf := !s.flags.cf } }
  | .setcc cond haveRex dst =>
      let v : BitVec 64 := if evalCond cond s.flags then 1 else 0
      writeRegSized (.z8 haveRex) dst v s
  | .jcc cond imm =>
      if evalCond cond s.flags then { s with pc := s.pc + BitVec.ofNat 64 len + imm }
      else { s with pc := s.pc + BitVec.ofNat 64 len }
  | .jmp dst => { s with pc := readReg s dst }
  | .lea sz dst disp =>
      writeRegSized sz dst (s.pc + BitVec.ofNat 64 len + disp) s
  | .sse op => execSSE op s

/-- One closed-model step: fetch and decode at RIP, execute, and advance or
branch.  A failed decode sets `failed`; a failed state stays failed. -/
noncomputable def x64Next (s : X64State) : X64State :=
  if s.failed then s
  else
    match decode (fun i => s.mem (s.pc + BitVec.ofNat 64 i)) with
    | some (insn, len) =>
        let s' := execInsn insn len s
        match insn with
        | .jcc _ _ => s'
        | .jmp _ => s'
        | _ => { s' with pc := s.pc + BitVec.ofNat 64 len }
    | none => { s with failed := true }

end Flapjack.Compiler.Encoders.X64

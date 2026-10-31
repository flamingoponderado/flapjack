import Flapjack.Compiler.Encoders.X64.Machine.State
import Flapjack.Compiler.Encoders.X64.Encode

/-!
# Decoding the x86-64 machine-code subset

This is the inverse of `encodeInsn` on the instruction forms that `x64Ast`
emits.  It is not a decoder for the full L3 `Decode` function: prefixes other
than the emitted REX/mandatory SSE prefixes, segment overrides, and the many
instruction forms the backend never emits are rejected.  `DecodeProof` proves
the round-trip on every emitted form.
-/

namespace Flapjack.Compiler.Encoders.X64

/-- The `i`-th byte of a byte list, with a zero default past the end. -/
def byteListReader (bs : List (BitVec 8)) : Nat → BitVec 8 :=
  fun i => bs.getD i 0

/-- Zero-extended little-endian 32-bit immediate at byte offset `off`. -/
def le32 (r : Nat → BitVec 8) (off : Nat) : BitVec 32 :=
  (r off).setWidth 32 ||| ((r (off + 1)).setWidth 32 <<< 8) |||
    ((r (off + 2)).setWidth 32 <<< 16) ||| ((r (off + 3)).setWidth 32 <<< 24)

/-- Little-endian 64-bit immediate at byte offset `off`. -/
def le64 (r : Nat → BitVec 8) (off : Nat) : BitVec 64 :=
  (r off).setWidth 64 ||| ((r (off + 1)).setWidth 64 <<< 8) |||
    ((r (off + 2)).setWidth 64 <<< 16) ||| ((r (off + 3)).setWidth 64 <<< 24) |||
    ((r (off + 4)).setWidth 64 <<< 32) ||| ((r (off + 5)).setWidth 64 <<< 40) |||
    ((r (off + 6)).setWidth 64 <<< 48) ||| ((r (off + 7)).setWidth 64 <<< 56)

/-- Sign-extended 8-bit immediate at byte offset `off`. -/
def imm8 (r : Nat → BitVec 8) (off : Nat) : BitVec 64 :=
  BitVec.ofInt 64 (r off).toInt

/-- Sign-extended 32-bit immediate at byte offset `off`. -/
def imm32 (r : Nat → BitVec 8) (off : Nat) : BitVec 64 :=
  BitVec.ofInt 64 (le32 r off).toInt

/-- A parsed ModRM operand: its `mod` and `reg` fields, the decoded `rm`, and
the number of bytes consumed (ModRM, SIB and displacement). -/
structure ParsedRM where
  modBits : Nat
  regBits : Nat
  rm : ZRM
  len : Nat
  deriving Repr, DecidableEq

/-- The register number of a register operand (zero for memory operands). -/
def ZRM.regOf : ZRM → Nat
  | .zr reg => reg
  | .zm _ _ _ => 0

/-- Parse a ModRM operand at byte offset `off`.  Only the emitted forms are
recognized: register operands, base-register operands without an index, and
RIP-relative operands. -/
def parseRM (r : Nat → BitVec 8) (off : Nat) (rexB : Bool) : Option ParsedRM :=
  let m := (r off).toNat
  let modBits := m / 64
  let regBits := (m / 8) % 8
  let rmBits := m % 8
  let hi := if rexB then 8 else 0
  if modBits = 3 then
    some { modBits := 3, regBits := regBits, rm := .zr (hi + rmBits), len := 1 }
  else if rmBits = 4 then
    let sib := (r (off + 1)).toNat
    let indexBits := (sib / 8) % 8
    let baseBits := sib % 8
    if indexBits ≠ 4 then none
    else
      let baseReg := hi + baseBits
      if modBits = 0 && baseBits = 5 then
        some { modBits := modBits, regBits := regBits, rm := .zm none (.regBase baseReg) (imm32 r (off + 2)), len := 6 }
      else if modBits = 0 then
        some { modBits := modBits, regBits := regBits, rm := .zm none (.regBase baseReg) 0, len := 2 }
      else if modBits = 1 then
        some { modBits := modBits, regBits := regBits, rm := .zm none (.regBase baseReg) (imm8 r (off + 2)), len := 3 }
      else
        some { modBits := modBits, regBits := regBits, rm := .zm none (.regBase baseReg) (imm32 r (off + 2)), len := 6 }
  else if modBits = 0 && rmBits = 5 then
    some { modBits := modBits, regBits := regBits, rm := .zm none .ripBase (imm32 r (off + 1)), len := 5 }
  else
    let baseReg := hi + rmBits
    if modBits = 0 then
      some { modBits := modBits, regBits := regBits, rm := .zm none (.regBase baseReg) 0, len := 1 }
    else if modBits = 1 then
      some { modBits := modBits, regBits := regBits, rm := .zm none (.regBase baseReg) (imm8 r (off + 1)), len := 2 }
    else
      some { modBits := modBits, regBits := regBits, rm := .zm none (.regBase baseReg) (imm32 r (off + 1)), len := 5 }

/-- Decode the `Zbinop_name` of an ALU opcode byte. -/
def binopOfOpcode (opcode : Nat) : Option ZBinopName :=
  match opcode with
  | 0x01 => some .zadd
  | 0x09 => some .zor
  | 0x11 => some .zadc
  | 0x19 => some .zsbb
  | 0x21 => some .zand
  | 0x29 => some .zsub
  | 0x31 => some .zxor
  | 0x39 => some .zcmp
  | _ => none

/-- Decode the group-1 opcode-extension digit (`0x83`/`0x81`). -/
def binopOfExt (ext : Nat) : Option ZBinopName :=
  match ext with
  | 0 => some .zadd
  | 1 => some .zor
  | 2 => some .zadc
  | 3 => some .zsbb
  | 4 => some .zand
  | 5 => some .zsub
  | 6 => some .zxor
  | 7 => some .zcmp
  | _ => none

/-- Decode the shift opcode-extension digit. -/
def shiftOfExt (ext : Nat) : Option ZBinopName :=
  match ext with
  | 1 => some .zror
  | 4 => some .zshl
  | 5 => some .zshr
  | 7 => some .zsar
  | _ => none

/-- Decode the group-3 opcode-extension digit. -/
def group3OfExt (ext : Nat) (reg : Nat) : Option X64Insn :=
  match ext with
  | 2 => some (.monop .znot .z64 reg)
  | 3 => some (.monop .zneg .z64 reg)
  | 4 => some (.mul .z64 reg)
  | 6 => some (.div .z64 reg)
  | _ => none

/-- Decode the group-5 opcode-extension digit. -/
def group5OfExt (ext : Nat) (reg : Nat) : Option X64Insn :=
  match ext with
  | 0 => some (.monop .zinc .z64 reg)
  | 1 => some (.monop .zdec .z64 reg)
  | 4 => some (.jmp reg)
  | _ => none

/-- Decode a memory operand with a base register into a load/store operand. -/
def baseOfRM (rm : ZRM) : Option (Nat × BitVec 64) :=
  match rm with
  | .zm none (.regBase base) disp => some (base, disp)
  | _ => none

/-- Decode the SSE `sse_logic` selector. -/
def logicOfCode (code : Nat) : Option SSELogic :=
  match code with
  | 0 => some .sseAnd
  | 1 => some .sseAndn
  | 2 => some .sseOr
  | 3 => some .sseXor
  | _ => none

/-- Decode the SSE `sse_binop` selector. -/
def sseBinopOfCode (code : Nat) : Option SSEBinop :=
  match code with
  | 0 => some .sseAdd
  | 1 => some .sseMul
  | 4 => some .sseSub
  | 5 => some .sseMin
  | 6 => some .sseDiv
  | 7 => some .sseMax
  | _ => none

/-- Decode a conditional code (`0F 8x` / `0F 9x` / `7x`). -/
def condOfCode (code : Nat) : Option ZCond :=
  match code with
  | 0 => some .zO
  | 1 => some .zNO
  | 2 => some .zB
  | 3 => some .zNB
  | 4 => some .zE
  | 5 => some .zNE
  | 6 => some .zNA
  | 7 => some .zA
  | 8 => some .zS
  | 9 => some .zNS
  | 10 => some .zP
  | 11 => some .zNP
  | 12 => some .zL
  | 13 => some .zNL
  | 14 => some .zNG
  | 15 => some .zG
  | _ => none

/-- Decode the SSE forms after the mandatory prefix, an optional REX byte, and
the `0F` escape.  `off` is the offset of the byte after `0F`. -/
def decodeSSE (r : Nat → BitVec 8) (off : Nat) (mandatory : Nat)
    (hasRex rexW rexR rexB : Bool) : Option (X64Insn × Nat) :=
  let base := 3 + (if hasRex then 1 else 0)
  let op := (r off).toNat
  let regOf (p : ParsedRM) : Nat := (if rexR then 8 else 0) + p.regBits
  if mandatory = 0x66 then
    if op = 0x2F then
      match parseRM r (off + 1) rexB with
      | some p => some (.sse (.comisd (regOf p) p.rm.regOf), base + p.len)
      | none => none
    else if op = 0x38 then
      if (r (off + 1)).toNat = 0x29 then
        match parseRM r (off + 2) rexB with
        | some p => some (.sse (.pcmpeqq (regOf p) p.rm.regOf), base + 1 + p.len)
        | none => none
      else none
    else if op = 0x73 then
      match parseRM r (off + 1) rexB with
      | some p =>
          let imm := r (off + 1 + p.len)
          if p.modBits = 3 then
            if p.regBits = 2 then some (.sse (.psrlqImm p.rm.regOf imm), base + 1 + p.len)
            else if p.regBits = 6 then some (.sse (.psllqImm p.rm.regOf imm), base + 1 + p.len)
            else if p.regBits = 3 then some (.sse (.psrldq p.rm.regOf imm), base + 1 + p.len)
            else if p.regBits = 7 then some (.sse (.pslldq p.rm.regOf imm), base + 1 + p.len)
            else none
          else none
      | none => none
    else if 0x54 ≤ op && op ≤ 0x57 then
      match parseRM r (off + 1) rexB with
      | some p =>
          match logicOfCode (op - 0x54) with
          | some logic => some (.sse (.logicPD logic (regOf p) p.rm.regOf), base + p.len)
          | none => none
      | none => none
    else if op = 0x6E then
      match parseRM r (off + 1) rexB with
      | some p => some (.sse (.movDQ true rexW (regOf p) p.rm), base + p.len)
      | none => none
    else if op = 0x7E then
      match parseRM r (off + 1) rexB with
      | some p => some (.sse (.movDQ false rexW (regOf p) p.rm), base + p.len)
      | none => none
    else if op = 0xE6 then
      match parseRM r (off + 1) rexB with
      | some p => some (.sse (.cvtpd2dq true (regOf p) p.rm.regOf), base + p.len)
      | none => none
    else none
  else if mandatory = 0xF2 then
    if op = 0x10 then
      match parseRM r (off + 1) rexB with
      | some p => some (.sse (.movsd (regOf p) p.rm.regOf), base + p.len)
      | none => none
    else if op = 0x51 then
      match parseRM r (off + 1) rexB with
      | some p => some (.sse (.sqrtsd (regOf p) p.rm.regOf), base + p.len)
      | none => none
    else if 0x58 ≤ op && op ≤ 0x5F then
      match parseRM r (off + 1) rexB with
      | some p =>
          match sseBinopOfCode (op - 0x58) with
          | some bop => some (.sse (.binSD bop (regOf p) p.rm.regOf), base + p.len)
          | none => none
      | none => none
    else if op = 0xE6 then
      match parseRM r (off + 1) rexB with
      | some p => some (.sse (.cvtpd2dq false (regOf p) p.rm.regOf), base + p.len)
      | none => none
    else none
  else if mandatory = 0xF3 then
    if op = 0xE6 then
      match parseRM r (off + 1) rexB with
      | some p => some (.sse (.cvtdq2pd (regOf p) p.rm.regOf), base + p.len)
      | none => none
    else none
  else none

/-- Decode one instruction from a byte reader. -/
def decode (r : Nat → BitVec 8) : Option (X64Insn × Nat) :=
  let b0 := (r 0).toNat
  if b0 = 0x88 then
    match parseRM r 1 false with
    | some p =>
        if p.modBits = 3 then some (.movRR (.z8 false) p.rm.regOf p.regBits, 1 + p.len)
        else
          match baseOfRM p.rm with
          | some (base, disp) => some (.movMR (.z8 false) p.regBits base disp, 1 + p.len)
          | none => none
    | none => none
  else if b0 = 0x89 then
    match parseRM r 1 false with
    | some p =>
        if p.modBits = 3 then some (.movRR .z32 p.rm.regOf p.regBits, 1 + p.len)
        else
          match baseOfRM p.rm with
          | some (base, disp) => some (.movMR .z32 p.regBits base disp, 1 + p.len)
          | none => none
    | none => none
  else if b0 = 0x8B then
    match parseRM r 1 false with
    | some p =>
        if p.modBits = 3 then none
        else
          match baseOfRM p.rm with
          | some (base, disp) => some (.movRM .z32 p.regBits base disp, 1 + p.len)
          | none => none
    | none => none
  else if b0 = 0x01 || b0 = 0x09 || b0 = 0x11 || b0 = 0x19 || b0 = 0x21 ||
      b0 = 0x29 || b0 = 0x31 || b0 = 0x39 then
    match binopOfOpcode b0, parseRM r 1 false with
    | some bop, some p =>
        if p.modBits = 3 then some (.binopRR bop .z32 p.rm.regOf p.regBits, 1 + p.len)
        else none
    | _, _ => none
  else if b0 = 0x85 then
    match parseRM r 1 false with
    | some p =>
        if p.modBits = 3 then some (.binopRR .ztest .z32 p.rm.regOf p.regBits, 1 + p.len)
        else none
    | none => none
  else if b0 = 0x90 then some (.nop 1, 1)
  else if b0 = 0xF5 then some (.cmc, 1)
  else if b0 = 0xE9 then some (.jcc .zAlways (imm32 r 1), 5)
  else if b0 = 0x7A then some (.jcc .zP (imm8 r 1), 2)
  else if b0 = 0x05 || b0 = 0x0D || b0 = 0x15 || b0 = 0x1D || b0 = 0x25 ||
      b0 = 0x2D || b0 = 0x35 || b0 = 0x3D || b0 = 0xA9 then
    let bop := if b0 = 0x05 then .zadd else if b0 = 0x0D then .zor
      else if b0 = 0x15 then .zadc else if b0 = 0x1D then .zsbb
      else if b0 = 0x25 then .zand else if b0 = 0x2D then .zsub
      else if b0 = 0x35 then .zxor else if b0 = 0x3D then .zcmp else .ztest
    some (.binopRI bop .z64 0 (imm32 r 1), 5)
  else if 0xB8 ≤ b0 && b0 ≤ 0xBF then some (.movRI .z32 (b0 - 0xB8) (imm32 r 1), 5)
  else if 0x40 ≤ b0 && b0 ≤ 0x4F then
    let rexW := b0 % 16 ≥ 8
    let rexR := b0 % 8 ≥ 4
    let rexB := b0 % 2 = 1
    let op := (r 1).toNat
    if op = 0x05 || op = 0x0D || op = 0x15 || op = 0x1D || op = 0x25 ||
        op = 0x2D || op = 0x35 || op = 0x3D || op = 0xA9 then
      let bop := if op = 0x05 then .zadd else if op = 0x0D then .zor
        else if op = 0x15 then .zadc else if op = 0x1D then .zsbb
        else if op = 0x25 then .zand else if op = 0x2D then .zsub
        else if op = 0x35 then .zxor else if op = 0x3D then .zcmp else .ztest
      some (.binopRI bop .z64 0 (imm32 r 2), 6)
    else if op = 0x88 then
      match parseRM r 2 rexB with
      | some p =>
          if p.modBits = 3 then
            some (.movRR (.z8 true) p.rm.regOf ((if rexR then 8 else 0) + p.regBits), 2 + p.len)
          else
            match baseOfRM p.rm with
            | some (base, disp) =>
                some (.movMR (.z8 true) ((if rexR then 8 else 0) + p.regBits) base disp,
                  2 + p.len)
            | none => none
      | none => none
    else if op = 0x89 then
      let sz := if rexW then ZSize.z64 else ZSize.z32
      match parseRM r 2 rexB with
      | some p =>
          if p.modBits = 3 then
            some (.movRR sz p.rm.regOf ((if rexR then 8 else 0) + p.regBits), 2 + p.len)
          else
            match baseOfRM p.rm with
            | some (base, disp) =>
                some (.movMR sz ((if rexR then 8 else 0) + p.regBits) base disp, 2 + p.len)
            | none => none
      | none => none
    else if op = 0x8B then
      let sz := if rexW then ZSize.z64 else ZSize.z32
      match parseRM r 2 rexB with
      | some p =>
          if p.modBits = 3 then none
          else
            match baseOfRM p.rm with
            | some (base, disp) =>
                some (.movRM sz ((if rexR then 8 else 0) + p.regBits) base disp, 2 + p.len)
            | none => none
      | none => none
    else if op = 0x01 || op = 0x09 || op = 0x11 || op = 0x19 || op = 0x21 ||
        op = 0x29 || op = 0x31 || op = 0x39 then
      let sz := if rexW then ZSize.z64 else ZSize.z32
      match binopOfOpcode op, parseRM r 2 rexB with
      | some bop, some p =>
          if p.modBits = 3 then
            some (.binopRR bop sz p.rm.regOf ((if rexR then 8 else 0) + p.regBits), 2 + p.len)
          else none
      | _, _ => none
    else if op = 0x85 then
      let sz := if rexW then ZSize.z64 else ZSize.z32
      match parseRM r 2 rexB with
      | some p =>
          if p.modBits = 3 then
            some (.binopRR .ztest sz p.rm.regOf ((if rexR then 8 else 0) + p.regBits), 2 + p.len)
          else none
      | none => none
    else if op = 0x83 then
      match parseRM r 2 rexB with
      | some p =>
          match binopOfExt p.regBits with
          | some bop =>
              if p.modBits = 3 then
                some (.binopRI bop .z64 p.rm.regOf (imm8 r (2 + p.len)), 3 + p.len)
              else none
          | none => none
      | none => none
    else if op = 0x81 then
      match parseRM r 2 rexB with
      | some p =>
          match binopOfExt p.regBits with
          | some bop =>
              if p.modBits = 3 then
                some (.binopRI bop .z64 p.rm.regOf (imm32 r (2 + p.len)), 6 + p.len)
              else none
          | none => none
      | none => none
    else if op = 0xC1 then
      match parseRM r 2 rexB with
      | some p =>
          match shiftOfExt p.regBits with
          | some sh =>
              if p.modBits = 3 then
                some (.binopRI sh .z64 p.rm.regOf (imm8 r (2 + p.len)), 3 + p.len)
              else none
          | none => none
      | none => none
    else if op = 0xD1 then
      match parseRM r 2 rexB with
      | some p =>
          match shiftOfExt p.regBits with
          | some sh =>
              if p.modBits = 3 then some (.binopRI sh .z64 p.rm.regOf 1, 2 + p.len)
              else none
          | none => none
      | none => none
    else if op = 0xD3 then
      match parseRM r 2 rexB with
      | some p =>
          match shiftOfExt p.regBits with
          | some sh =>
              if p.modBits = 3 then some (.binopRR sh .z64 p.rm.regOf 1, 2 + p.len)
              else none
          | none => none
      | none => none
    else if op = 0xF7 then
      match parseRM r 2 rexB with
      | some p =>
          if p.modBits = 3 then
            if p.regBits = 0 then
              some (.binopRI .ztest .z64 p.rm.regOf (imm32 r (2 + p.len)), 6 + p.len)
            else
              match group3OfExt p.regBits p.rm.regOf with
              | some insn => some (insn, 2 + p.len)
              | none => none
          else none
      | none => none
    else if op = 0xFF then
      match parseRM r 2 rexB with
      | some p =>
          if p.modBits = 3 then
            match group5OfExt p.regBits p.rm.regOf with
            | some insn => some (insn, 2 + p.len)
            | none => none
          else none
      | none => none
    else if op = 0x8D then
      match parseRM r 2 rexB with
      | some p =>
          match p.rm with
          | .zm none .ripBase disp =>
              some (.lea .z64 ((if rexR then 8 else 0) + p.regBits) disp, 2 + p.len)
          | _ => none
      | none => none
    else if op = 0xB8 || op = 0xB9 || op = 0xBA || op = 0xBB ||
        op = 0xBC || op = 0xBD || op = 0xBE || op = 0xBF then
      let dst := (op - 0xB8) + (if rexB then 8 else 0)
      if rexW then some (.movRI .z64 dst (le64 r 2), 10)
      else some (.movRI .z32 dst (imm32 r 2), 6)
    else if op = 0x0F then
      let b2 := (r 2).toNat
      if 0x80 ≤ b2 && b2 ≤ 0x8F then
        match condOfCode (b2 - 0x80) with
        | some cond => some (.jcc cond (imm32 r 3), 6)
        | none => none
      else if 0x90 ≤ b2 && b2 ≤ 0x9F then
        match parseRM r 3 rexB with
        | some p =>
            match condOfCode (b2 - 0x90) with
            | some cond =>
                if p.modBits = 3 then some (.setcc cond true p.rm.regOf, 3 + p.len)
                else none
            | none => none
        | none => none
      else if b2 = 0xB6 then
        match parseRM r 3 rexB with
        | some p =>
            match baseOfRM p.rm with
            | some (base, disp) =>
                some (.movzxRM (.z8 true) .z64 ((if rexR then 8 else 0) + p.regBits) base disp,
                  3 + p.len)
            | none => none
        | none => none
      else if b2 = 0xB7 then
        match parseRM r 3 rexB with
        | some p =>
            match baseOfRM p.rm with
            | some (base, disp) =>
                some (.movzxRM .z16 .z64 ((if rexR then 8 else 0) + p.regBits) base disp,
                  3 + p.len)
            | none => none
        | none => none
      else none
    else none
  else if b0 = 0xFF then
    match parseRM r 1 false with
    | some p =>
        if p.modBits = 3 then
          match group5OfExt p.regBits p.rm.regOf with
          | some insn => some (insn, 1 + p.len)
          | none => none
        else none
    | none => none
  else if b0 = 0x66 then
    let b1 := (r 1).toNat
    if 0x40 ≤ b1 && b1 ≤ 0x4F then
      let rexW := b1 % 16 ≥ 8
      let rexR := b1 % 8 ≥ 4
      let rexB := b1 % 2 = 1
      let op := (r 2).toNat
      if op = 0x0F then decodeSSE r 3 b0 true rexW rexR rexB
      else if op = 0x89 then
        match parseRM r 3 rexB with
        | some p =>
            if p.modBits = 3 then
              some (.movRR .z16 p.rm.regOf ((if rexR then 8 else 0) + p.regBits), 3 + p.len)
            else
              match baseOfRM p.rm with
              | some (base, disp) =>
                  some (.movMR .z16 ((if rexR then 8 else 0) + p.regBits) base disp, 3 + p.len)
              | none => none
        | none => none
      else if op = 0x8B then
        match parseRM r 3 rexB with
        | some p =>
            if p.modBits = 3 then none
            else
              match baseOfRM p.rm with
              | some (base, disp) =>
                  some (.movRM .z16 ((if rexR then 8 else 0) + p.regBits) base disp, 3 + p.len)
              | none => none
        | none => none
      else none
    else if b1 = 0x0F then decodeSSE r 2 b0 false false false false
    else if b1 = 0x89 then
      match parseRM r 2 false with
      | some p =>
          if p.modBits = 3 then some (.movRR .z16 p.rm.regOf p.regBits, 2 + p.len)
          else
            match baseOfRM p.rm with
            | some (base, disp) => some (.movMR .z16 p.regBits base disp, 2 + p.len)
            | none => none
      | none => none
    else if b1 = 0x8B then
      match parseRM r 2 false with
      | some p =>
          if p.modBits = 3 then none
          else
            match baseOfRM p.rm with
            | some (base, disp) => some (.movRM .z16 p.regBits base disp, 2 + p.len)
            | none => none
      | none => none
    else none
  else if b0 = 0xF2 || b0 = 0xF3 then
    let b1 := (r 1).toNat
    if 0x40 ≤ b1 && b1 ≤ 0x4F then
      let rexW := b1 % 16 ≥ 8
      let rexR := b1 % 8 ≥ 4
      let rexB := b1 % 2 = 1
      if (r 2).toNat = 0x0F then decodeSSE r 3 b0 true rexW rexR rexB
      else none
    else if b1 = 0x0F then decodeSSE r 2 b0 false false false false
    else none
  else if b0 = 0x0F then
    let b1 := (r 1).toNat
    if 0x80 ≤ b1 && b1 ≤ 0x8F then
      match condOfCode (b1 - 0x80) with
      | some cond => some (.jcc cond (imm32 r 2), 6)
      | none => none
    else if 0x90 ≤ b1 && b1 ≤ 0x9F then
      match parseRM r 2 false with
      | some p =>
          match condOfCode (b1 - 0x90) with
          | some cond =>
              if p.modBits = 3 then some (.setcc cond false p.rm.regOf, 2 + p.len)
              else none
          | none => none
      | none => none
    else if b1 = 0xB6 then
      match parseRM r 2 false with
      | some p =>
          match baseOfRM p.rm with
          | some (base, disp) => some (.movzxRM (.z8 true) .z64 p.regBits base disp, 2 + p.len)
          | none => none
      | none => none
    else if b1 = 0xB7 then
      match parseRM r 2 false with
      | some p =>
          match baseOfRM p.rm with
          | some (base, disp) => some (.movzxRM .z16 .z64 p.regBits base disp, 2 + p.len)
          | none => none
      | none => none
    else none
  else none

end Flapjack.Compiler.Encoders.X64

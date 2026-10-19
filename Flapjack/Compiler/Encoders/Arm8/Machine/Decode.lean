import Flapjack.Compiler.Encoders.Arm8.Machine.State
import Flapjack.Compiler.Encoders.Arm8.Encode

/-!
# Decoding the ARMv8 machine-code subset

This is the inverse of the `encodeInsn` fragment of `Encode.lean` on the
instruction forms that `arm8Ast` emits.  It is not a decoder for the full L3
`Decode` function: system instructions, floating point, and instructions that
the backend never emits are rejected.  The Main module proves the round-trip on
every emitted form.
-/

namespace Flapjack.Compiler.Encoders.Arm8

/-- `n` bits of `w` starting at bit `lo`. -/
def part (w : BitVec 32) (lo len : Nat) : Nat :=
  ((w >>> lo).setWidth len).toNat

/-- Does `w` agree with `base` on every bit set in `mask`? -/
def bitMatches (w mask base : BitVec 32) : Bool :=
  (w &&& mask) = base

/-- Canonical decode of a two-bit logical opcode. -/
def decodeLogicalOp (opc : Nat) : Option (LogicalOp × Bool) :=
  match opc with
  | 0 => some (.and, false)
  | 1 => some (.orr, false)
  | 2 => some (.eor, false)
  | 3 => some (.and, true)
  | _ => none

/-- Canonical decode of a two-bit shift type. -/
def decodeShift (bits : Nat) : ShiftType :=
  match bits with
  | 0 => .lsl
  | 1 => .lsr
  | 2 => .asr
  | _ => .ror

/-- Canonical decode of a two-bit move-wide opcode. -/
def decodeMoveWideOp (bits : Nat) : Option MoveWideOp :=
  match bits with
  | 0 => some .n
  | 2 => some .z
  | 3 => some .k
  | _ => none

/-- Canonical decode of a two-bit bitfield opcode. -/
def decodeBitfieldOp (bits : Nat) : Option (Bool × Bool) :=
  match bits with
  | 0 => some (true, true)
  | 1 => some (false, false)
  | 2 => some (true, false)
  | _ => none

/-- Canonical decode of a branch-register opcode. -/
def decodeBranchKind (bits : Nat) : Option BranchKind :=
  match bits with
  | 0 => some .jmp
  | 1 => some .call
  | 2 => some .ret
  | _ => none

/-- Decode one 32-bit instruction word. -/
def decodeInsn32 (w : BitVec 32) : Option Insn :=
  let b := part w
  if bitMatches w 0xFFFFFFFF 0xD503201F then
    some .noOp
  else if bitMatches w 0x9F800000 0x92800000 then
    match decodeMoveWideOp (b 29 2) with
    | some op => some (.moveWide op (b 21 2) (b 5 16) (b 0 5))
    | none => none
  else if bitMatches w 0x9F800000 0x91000000 then
    let opcode21 := b 22 1
    let imm := if opcode21 = 0 then b 10 12 else (b 10 12) <<< 12
    some (.addSubImmediate (b 30 1 = 1) (b 29 1 = 1)
      (BitVec.ofNat 64 imm) (b 5 5) (b 0 5))
  else if bitMatches w 0x9F800000 0x92000000 then
    match decodeLogicalOp (b 29 2) with
    | some (op, sf) =>
        let n := b 22 1
        let immr := b 16 6
        let imms := b 10 6
        match decodeBitMasks n imms immr true with
        | some (imm, _) => some (.logicalImmediate op sf (BitVec.ofNat 64 imm)
            (b 5 5) (b 0 5))
        | none => none
    | none => none
  else if bitMatches w 0x9F000000 0x8A000000 then
    match decodeLogicalOp (b 29 2) with
    | some (op, sf) =>
        some (.logicalShiftedRegister op (b 21 1 = 1) sf
          (decodeShift (b 22 2)) (b 10 6) (b 16 5) (b 5 5) (b 0 5))
    | none => none
  else if bitMatches w 0x9F200000 0x8B000000 then
    some (.addSubShiftedRegister (b 30 1 = 1) (b 29 1 = 1)
      (decodeShift (b 22 2)) (b 16 5) (b 10 6) (b 5 5) (b 0 5))
  else if bitMatches w 0x9FE00000 0x93400000 then
    match decodeBitfieldOp (b 29 2) with
    | some (inzero, extend) =>
        some (.bitfieldMove inzero extend (b 16 6) (b 10 6) (b 5 5) (b 0 5))
    | none => none
  else if bitMatches w 0xFFE00000 0x93C00000 then
    some (.extractRegister (b 10 6) (b 16 5) (b 5 5) (b 0 5))
  else if bitMatches w 0xFFE0F000 0x9AC02000 then
    some (.shift (decodeShift (b 10 2)) (b 16 5) (b 5 5) (b 0 5))
  else if bitMatches w 0xFFE0F800 0x9AC00800 then
    some (.division (b 10 1 = 0) (b 16 5) (b 5 5) (b 0 5))
  else if bitMatches w 0x9B600000 0x9B400000 then
    some (.multiplyHigh (b 23 1 = 0) (b 16 5) (b 5 5) (b 0 5))
  else if bitMatches w 0xFFE00000 0x9B000000 then
    some (.multiplyAddSub (b 15 1 = 1) (b 16 5) (b 10 5) (b 5 5) (b 0 5))
  else if bitMatches w 0xBA400810 0xBA400800 then
    some (.conditionalCompareImmediate (b 30 1 = 1) (BitVec.ofNat 64 (b 16 5))
      (b 12 4) (b 3 1 = 1, b 2 1 = 1, b 1 1 = 1, b 0 1 = 1) (b 5 5))
  else if bitMatches w 0x9A800800 0x9A800000 then
    some (.conditionalSelect (b 30 1 = 1) (b 10 1 = 1) (b 12 4)
      (b 16 5) (b 5 5) (b 0 5))
  else if bitMatches w 0x9A000000 0x9A000000 then
    some (.addSubCarry (b 30 1 = 1) (b 29 1 = 1) (b 16 5) (b 5 5) (b 0 5))
  else if bitMatches w 0x3D000000 0x39000000 then
    let size := b 30 2
    let load := b 22 2 ≠ 0
    let off := (b 10 12) <<< size
    some (.loadStoreImmediate size false (if load then .load else .store) false true
      (BitVec.ofNat 64 off) (b 5 5) (b 0 5))
  else if bitMatches w 0x3F000000 0x38000000 then
    let size := b 30 2
    let load := b 22 2 ≠ 0
    let imm9 := b 12 9
    let signed := sextToWord 9 (BitVec.ofNat 64 imm9)
    some (.loadStoreImmediate size false (if load then .load else .store) false false
      signed (b 5 5) (b 0 5))
  else if bitMatches w 0x7C000000 0x14000000 then
    let imm26 := b 0 26
    let imm := BitVec.ofInt 64 (sextValue 28 (imm26 <<< 2))
    some (.branchImmediate imm (b 31 1 = 1))
  else if bitMatches w 0xFF000010 0x54000000 then
    let imm19 := b 5 19
    let imm := BitVec.ofInt 64 (sextValue 21 (imm19 <<< 2))
    some (.branchConditional imm (b 0 4))
  else if bitMatches w 0xFF9FFC1F 0xD61F0000 then
    match decodeBranchKind (b 21 2) with
    | some kind => some (.branchRegister (b 5 5) kind)
    | none => none
  else if bitMatches w 0x9F000000 0x10000000 then
    let imm := BitVec.ofInt 64 (sextValue 21 (b 5 19 <<< 2))
    some (.address false imm (b 0 5))
  else if bitMatches w 0x9F000000 0x90000000 then
    some (.address true (BitVec.ofNat 64 (b 29 2)) (b 0 5))
  else
    none

/-- Decode the low 32 bits of a 64-bit machine word. -/
def decodeInsn (w : W) : Option Insn :=
  decodeInsn32 (w.setWidth 32)

end Flapjack.Compiler.Encoders.Arm8

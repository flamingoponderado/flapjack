import Flapjack.Compiler.Encoders.Arm8.Machine.Decode

/-!
# Execution of the closed ARMv8 instruction subset

The rules below are the architectural behaviour of the instruction forms that
`arm8Ast` emits.  They follow the corresponding L3 `dfn'*` rules for the
subset, but the state carrier is the closed `Arm8State` above rather than the
full `arm8_state`; this file is not an exact port of the L3 `Run` function.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm

/-- Shift a 64-bit value by an amount reduced modulo 64. -/
def shiftValue (value : BitVec 64) (ty : ShiftType) (amount : Nat) : BitVec 64 :=
  match ty with
  | .lsl => value <<< (amount % 64)
  | .lsr => value >>> (amount % 64)
  | .asr => value.sshiftRight (amount % 64)
  | .ror => value.rotateRight (amount % 64)

/-- ARM `ROR` of a 64-bit value. -/
def ror64 (value : BitVec 64) (amount : Nat) : BitVec 64 :=
  value.rotateRight (amount % 64)

/-- `AddWithCarry` of the L3 ARM8 model, at 64 bits. -/
def addWithCarry (x y : BitVec 64) (carryIn : Bool) : BitVec 64 × Arm8Flags :=
  let unsignedSum : Nat := x.toNat + y.toNat + (if carryIn then 1 else 0)
  let result : BitVec 64 := BitVec.ofNat 64 unsignedSum
  let n := result.getLsbD 63
  let z := result = 0
  let c := result.toNat ≠ unsignedSum
  let v := result.toInt ≠ x.toInt + y.toInt + (if carryIn then 1 else 0)
  (result, (n, z, c, v))

/-- Condition-code test. -/
def conditionHolds (s : Arm8State) (cond : Nat) : Bool :=
  match cond with
  | 0 => s.z
  | 1 => !s.z
  | 2 => s.c
  | 3 => !s.c
  | 4 => s.n
  | 5 => !s.n
  | 6 => s.v
  | 7 => !s.v
  | 8 => s.c && !s.z
  | 9 => !s.c || s.z
  | 10 => s.n = s.v
  | 11 => s.n ≠ s.v
  | 12 => !s.z && s.n = s.v
  | 13 => s.z || s.n ≠ s.v
  | 14 => true
  | _ => false

/-- The bitfield `Replicate` used for sign-extending bitfield moves. -/
def replicateBit (b : Bool) : BitVec 64 := if b then 0xFFFFFFFFFFFFFFFF else 0

/-- ARM `BitfieldMove` for 64-bit registers. -/
def bitfieldMove (s : Arm8State) (inzero extend : Bool) (immr imms rn rd : Nat) : Arm8State :=
  let v := if inzero then 0 else s.regs rd
  let v0 := readReg s rn
  match decodeBitMasks 1 imms immr false with
  | none => s
  | some (wmask, tmask) =>
      let wmask := BitVec.ofNat 64 wmask
      let tmask := BitVec.ofNat 64 tmask
      let top := (if extend then replicateBit (v0.getLsbD (imms % 64)) else v) &&& ~~~tmask
      let bot := ((v &&& ~~~wmask) ||| (ror64 v0 immr &&& wmask)) &&& tmask
      writeReg s rd (top ||| bot)

/-- Execute one decoded instruction.  The caller adds the four-byte PC advance
for non-control-flow instructions; `arm8Next` below does that. -/
def execInsn (s : Arm8State) : Insn → Arm8State
  | .noOp => s
  | .moveWide op hw imm16 rd =>
      let shift := hw * 16
      let imm := BitVec.ofNat 64 imm16 <<< shift
      match op with
      | .n => writeReg s rd (~~~imm)
      | .z => writeReg s rd imm
      | .k =>
          let mask := (BitVec.ofNat 64 0xFFFF) <<< shift
          writeReg s rd ((readReg s rd &&& ~~~mask) ||| imm)
  | .addSubImmediate sub setFlags imm rn rd =>
      let x := readReg s rn
      let y := if sub then ~~~imm else imm
      let carryIn := sub
      let (result, flags) := addWithCarry x y carryIn
      let s := if setFlags then writeFlags s flags else s
      writeReg s rd result
  | .addSubShiftedRegister sub setFlags shift rm imm6 rn rd =>
      let x := readReg s rn
      let y0 := shiftValue (readReg s rm) shift imm6
      let y := if sub then ~~~y0 else y0
      let (result, flags) := addWithCarry x y sub
      let s := if setFlags then writeFlags s flags else s
      writeReg s rd result
  | .addSubCarry sub setFlags rm rn rd =>
      let x := readReg s rn
      let y0 := readReg s rm
      let y := if sub then ~~~y0 else y0
      let (result, flags) := addWithCarry x y s.c
      let s := if setFlags then writeFlags s flags else s
      writeReg s rd result
  | .logicalImmediate op setFlags imm rn rd =>
      let x := readReg s rn
      let result := match op with
        | .and => x &&& imm
        | .orr => x ||| imm
        | .eor => x ^^^ imm
      let s := if setFlags then writeFlags s (result.getLsbD 63, result = 0, false, false) else s
      writeReg s rd result
  | .logicalShiftedRegister op invert setFlags shift imm rm rn rd =>
      let x := readReg s rn
      let y0 := shiftValue (readReg s rm) shift imm
      let y := if invert then ~~~y0 else y0
      let result := match op with
        | .and => x &&& y
        | .orr => x ||| y
        | .eor => x ^^^ y
      let s := if setFlags then writeFlags s (result.getLsbD 63, result = 0, false, false) else s
      writeReg s rd result
  | .bitfieldMove inzero extend immr imms rn rd =>
      bitfieldMove s inzero extend immr imms rn rd
  | .extractRegister imms _rm rn rd =>
      writeReg s rd (ror64 (readReg s rn) imms)
  | .shift shift rm rn rd =>
      writeReg s rd (shiftValue (readReg s rn) shift (readReg s rm).toNat)
  | .division unsigned rm rn rd =>
      let x := readReg s rn
      let y := readReg s rm
      let result := if unsigned then x.udiv y else x.sdiv y
      writeReg s rd result
  | .multiplyHigh signed rm rn rd =>
      let x := readReg s rn
      let y := readReg s rm
      let result :=
        if signed then
          let prod : BitVec 128 := (x.signExtend 128) * (y.signExtend 128)
          prod.extractLsb' 64 64
        else
          let prod : BitVec 128 := (x.zeroExtend 128) * (y.zeroExtend 128)
          prod.extractLsb' 64 64
      writeReg s rd result
  | .multiplyAddSub sub rm ra rn rd =>
      let product := (readReg s rn) * (readReg s rm)
      let result := if sub then (readReg s ra) - product else (readReg s ra) + product
      writeReg s rd result
  | .conditionalCompareImmediate opc imm cd nzcv rn =>
      let flags :=
        if conditionHolds s cd then
          let x := readReg s rn
          let y := if opc then ~~~imm else imm
          (addWithCarry x y opc).2
        else nzcv
      writeFlags s flags
  | .conditionalSelect op o2 cd rm rn rd =>
      let result :=
        if conditionHolds s cd then readReg s rn
        else
          let y0 := readReg s rm
          let y := if op then ~~~y0 else y0
          if o2 then y + 1 else y
      writeReg s rd result
  | .loadStoreImmediate size _ memop _ _ offset rn rt =>
      let address := readReg s rn + offset
      let bytes := 2 ^ size
      match memop with
      | .load => writeReg s rt (readMemN s bytes address)
      | .store => writeMemN s bytes address (readReg s rt)
  | .branchImmediate imm call =>
      let s := if call then writeReg s 30 s.pc else s
      { s with pc := s.pc - 4 + imm }
  | .branchConditional imm cond =>
      if conditionHolds s cond then { s with pc := s.pc - 4 + imm }
      else s
  | .branchRegister rn kind =>
      let target := readReg s rn
      let s := if kind = .call then writeReg s 30 s.pc else s
      { s with pc := target }
  | .address page imm rd =>
      if page then
        writeReg s rd (((s.pc - 4) &&& ~~~(BitVec.ofNat 64 0xFFF)) + (imm <<< 12))
      else writeReg s rd (s.pc - 4 + imm)

/-- Fetch four bytes little-endian from memory. -/
def fetchWord (s : Arm8State) : BitVec 32 :=
  (s.mem s.pc).setWidth 32 |||
  ((s.mem (s.pc + 1)).setWidth 32 <<< 8) |||
  ((s.mem (s.pc + 2)).setWidth 32 <<< 16) |||
  ((s.mem (s.pc + 3)).setWidth 32 <<< 24)

/-- One machine step: decode and execute the word at `pc`.  A word outside the
emitted subset fails the machine by setting `failed` and does not advance. -/
def arm8Next (s : Arm8State) : Arm8State :=
  match decodeInsn32 (fetchWord s) with
  | some i => execInsn { s with pc := s.pc + 4 } i
  | none => { s with failed := true }

end Flapjack.Compiler.Encoders.Arm8

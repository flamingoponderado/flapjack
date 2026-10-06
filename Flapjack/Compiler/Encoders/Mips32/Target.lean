import Flapjack.Compiler.Encoders.Mips32.Encode
import Flapjack.Compiler.Encoders.AsmProps.Target
import Flapjack.Misc.Alignment
import Flapjack.Misc.SetSep

/-!
# The MIPS32 (Ziren) assembler target

The `asm` target record for Ziren's guest ISA, over Ziren's executable MIPS32r2 model
`ZirenDet.Isa` (little-endian, architectural delay slots, `HI`/`LO`).

The instruction sequences follow CakeML's MIPS64 target
(`cakeml/compiler/encoders/mips/mips_targetScript.sml`) narrowed to 32 bits:
* 64-bit operations (`DADDU`, `DSLL32`, `DMULTU`, ...) become their 32-bit forms, a constant
  is at most `LUI`/`ORI`, and rotations use the MIPS32r2 `ROTR`/`ROTRV` instructions;
* Ziren has no `BLTZAL`, so the "link without branching" idiom `BLTZAL $0, 0` becomes
  `BAL 1`, which links `pc + 8` and branches to `pc + 8` after its delay slot;
* every branch and jump is followed by a `nop` in its delay slot, except `BAL 1`, whose
  delay-slot instruction is the next instruction of the sequence (as in CakeML's MIPS64);
* `Loc` always uses the long form, so its length does not depend on the offset.

As in CakeML's `mips_next`, the next-state function runs a taken branch together with its
delay slot, so the asm-level states are never in a delay slot. It fetches the instruction
word from the machine memory (CakeML's code is in memory), decodes it with Ziren's `decode`
and executes it with Ziren's `exec`; an undecodable word stops the machine (`trapped`), as
`Isa.run` stops on it.

Flapjack-specific: CakeML has no MIPS32 target, so no declaration here carries a `@[hol]` tag.
-/

namespace Flapjack.Compiler.Encoders.Mips32
open Flapjack Flapjack.Compiler.Encoders.Asm ZirenDet.Isa Flapjack.Mips32

/-- `n2w r : word5`. -/
def regOf (r : Nat) : Fin 32 := ⟨r % 32, Nat.mod_lt _ (by decide)⟩

/-- `$at`, the assembler temporary (`temp_reg` in CakeML's MIPS target). -/
def tmp : Fin 32 := 1
/-- `$fp`/`$s8`, the second encoder temporary (`temp_reg2`). -/
def tmp2 : Fin 32 := 30
/-- `$ra`, the link register. -/
def ra : Fin 32 := 31

def lo16 (w : BitVec 32) : BitVec 16 := w.extractLsb' 0 16
def hi16 (w : BitVec 32) : BitVec 16 := w.extractLsb' 16 16

/-- `w2w (a >>> 2) - k`: the word offset of a branch `k` instructions into the sequence. -/
def branchOffset (a : BitVec 32) (k : BitVec 16) : BitVec 16 := (a >>> 2).setWidth 16 - k

/-- `min18 + lo ≤ a ≤ max18 + 4`: the short-branch range. -/
def shortRange (lo : Int) (a : BitVec 32) : Bool :=
  decide (-131072 + lo ≤ a.toInt) && decide (a.toInt ≤ 131071 + 4)

/-- The two-instruction compare of a conditional branch and its branch, for a computed
condition in `$at` (CakeML's `mips_cmp`): the condition and whether the branch is taken
when it is nonzero (`BNE`) or zero (`BEQ`). -/
def cmpBranch (c : Cmp) (rs : Fin 32) (off : BitVec 16) : Insn :=
  match c with
  | .less | .lower | .notTest => .bne rs 0 off
  | _ => .beq rs 0 off

def mips32Ast : HolAsm 32 → List Insn
  | .inst .skip => [nop]
  | .inst (.const r i) =>
    let rd := regOf r
    if hi16 i = 0 then [.ori rd 0 (lo16 i)]
    else if hi16 i = -1 ∧ (lo16 i).msb then [.addiu rd 0 (lo16 i)]
    else [.lui rd (hi16 i), .ori rd rd (lo16 i)]
  | .inst (.arith (.binop bop r1 r2 (.reg r3))) =>
    let rd := regOf r1; let rs := regOf r2; let rt := regOf r3
    match bop with
    | .add => [.addu rd rs rt]
    | .sub => [.subu rd rs rt]
    | .and => [.and rd rs rt]
    | .or => [.or rd rs rt]
    | .xor => [.xor rd rs rt]
  | .inst (.arith (.binop bop r1 r2 (.imm i))) =>
    let rt := regOf r1; let rs := regOf r2
    match bop with
    | .sub => [.addiu rt rs (lo16 (-i))]
    | .add => [.addiu rt rs (lo16 i)]
    | .and => [.andi rt rs (lo16 i)]
    | .or => [.ori rt rs (lo16 i)]
    | .xor => if i = -1 then [.nor rt rs 0] else [.xori rt rs (lo16 i)]
  | .inst (.arith (.shift sh r1 r2 (.imm i))) =>
    let rd := regOf r1; let rt := regOf r2; let sa : BitVec 5 := i.setWidth 5
    match sh with
    | .lsl => [.sll rd rt sa]
    | .lsr => [.srl rd rt sa]
    | .asr => [.sra rd rt sa]
    | .ror => [.rotr rd rt sa]
  | .inst (.arith (.shift sh r1 r2 (.reg r))) =>
    let rd := regOf r1; let rt := regOf r2; let rs := regOf r
    match sh with
    | .lsl => [.sllv rd rt rs]
    | .lsr => [.srlv rd rt rs]
    | .asr => [.srav rd rt rs]
    | .ror => [.rotrv rd rt rs]
  | .inst (.arith (.div r1 r2 r3)) => [.div (regOf r2) (regOf r3), .mflo (regOf r1)]
  | .inst (.arith (.longMul r1 r2 r3 r4)) =>
    [.multu (regOf r3) (regOf r4), .mfhi (regOf r1), .mflo (regOf r2)]
  | .inst (.arith (.longDiv _ _ _ _ _)) => [nop]
  | .inst (.arith (.addCarry r1 r2 r3 r4)) =>
    let a := regOf r1; let b := regOf r2; let c := regOf r3; let d := regOf r4
    [.sltu tmp 0 d, .addu a b c, .sltu d a c, .addu a a tmp, .sltu tmp a tmp, .or d d tmp]
  | .inst (.arith (.addOverflow r1 r2 r3 r4)) =>
    let a := regOf r1; let b := regOf r2; let c := regOf r3; let d := regOf r4
    [.xor tmp b c, .nor tmp tmp 0, .addu a b c, .xor d c a, .and d tmp d, .srl d d 31]
  | .inst (.arith (.subOverflow r1 r2 r3 r4)) =>
    let a := regOf r1; let b := regOf r2; let c := regOf r3; let d := regOf r4
    [.xor tmp b c, .subu a b c, .xor d c a, .nor d d 0, .and d tmp d, .srl d d 31]
  | .inst (.mem mop r1 (.addr r2 a)) =>
    let rt := regOf r1; let base := regOf r2; let off := lo16 a
    match mop with
    | .load | .load32 => [.lw rt base off]
    | .load16 => [.lhu rt base off]
    | .load8 => [.lbu rt base off]
    | .store | .store32 => [.sw rt base off]
    | .store16 => [.sh rt base off]
    | .store8 => [.sb rt base off]
  | .inst (.fp _) => [nop]
  | .jump a =>
    if shortRange 4 a then [.beq 0 0 (branchOffset a 1), nop]
    else
      let b := a - 12
      [.ori tmp2 ra 0, .bal 1, .lui tmp (hi16 b), .ori tmp tmp (lo16 b), .addu tmp ra tmp,
       .jr tmp, .ori ra tmp2 0]
  | .jumpCmp c r1 (.reg r2) a =>
    let rs := regOf r1; let rt := regOf r2; let b := branchOffset a 2
    match c with
    | .equal => [.beq rs rt (b + 1), nop]
    | .notEqual => [.bne rs rt (b + 1), nop]
    | .less | .notLess => [.slt tmp rs rt, cmpBranch c tmp b, nop]
    | .lower | .notLower => [.sltu tmp rs rt, cmpBranch c tmp b, nop]
    | .test | .notTest => [.and tmp rs rt, cmpBranch c tmp b, nop]
  | .jumpCmp c r (.imm i) a =>
    let rs := regOf r; let imm := lo16 i; let b := branchOffset a 2
    match c with
    | .equal => [.addiu tmp 0 imm, .beq rs tmp b, nop]
    | .notEqual => [.addiu tmp 0 imm, .bne rs tmp b, nop]
    | .less | .notLess => [.slti tmp rs imm, cmpBranch c tmp b, nop]
    | .lower | .notLower => [.sltiu tmp rs imm, cmpBranch c tmp b, nop]
    | .test | .notTest => [.andi tmp rs imm, cmpBranch c tmp b, nop]
  | .call a =>
    if shortRange 4 a then [.bal (branchOffset a 1), nop]
    else
      let b := a - 8
      [.bal 1, .lui tmp (hi16 b), .ori tmp tmp (lo16 b), .addu tmp ra tmp, .jalr ra tmp, nop]
  | .jumpReg r => [.jr (regOf r), nop]
  | .loc r i =>
    if r = 31 then
      let b := i - 8
      [.bal 1, .lui tmp (hi16 b), .ori tmp tmp (lo16 b), .addu ra tmp ra]
    else
      let rd := regOf r; let b := i - 12
      [.ori tmp ra 0, .bal 1, .lui rd (hi16 b), .ori rd rd (lo16 b), .addu rd rd ra,
       .ori ra tmp 0]

/-- Little-endian bytes of an instruction. -/
def mips32Encode (i : Insn) : List (BitVec 8) := wordBytes (encodeInsn i)

def mips32Enc (a : HolAsm 32) : List (BitVec 8) := (mips32Ast a).flatMap mips32Encode

/-- The MIPS32 assembler configuration. Registers and immediate ranges follow CakeML's
`mips_config`, at 32 bits and little-endian; jump and `Loc` offsets cover the whole 32-bit
range because the long forms wrap modulo `2 ^ 32`. -/
def mips32Config : AsmConfigExact 32 where
  isa := .mips
  encode := mips32Enc
  regCount := 32
  avoidRegs := [0, 1, 25, 26, 27, 28, 29, 30]
  fpRegCount := 0
  linkReg := some 31
  twoRegArith := false
  bigEndian := false
  validImm := fun operator i =>
    match operator with
    | .inl .and | .inl .or | .inl .xor | .inr .test | .inr .notTest =>
      (0 : BitVec 32).sle i && i.sle 0xFFFF
    | .inl .sub => (-32768 : BitVec 32).slt i && i.sle 32767
    | _ => (-32768 : BitVec 32).sle i && i.sle 32767
  addrOffset := (-32768, 32767)
  hwOffset := (-32768, 32767)
  byteOffset := (-32768, 32767)
  jumpOffset := (0x80000000, 0x7FFFFFFF)
  cjumpOffset := (-131072 + 8, 131071 + 4)
  locOffset := (0x80000000, 0x7FFFFFFF)
  codeAlignment := 2

/-! ## The machine -/

/-- Fetch the word at `pc` from memory, decode it with Ziren's decoder and execute it with
Ziren's `exec`. An undecodable word stops the machine. -/
def fetchExec (s : State) : State :=
  match decode (s.mem.readWord s.pc) with
  | some i => exec s i
  | none => { s with trapped := true }

/-- One asm-level step: an instruction, together with its delay slot when it branched away
(CakeML's `mips_next` merges a branch with its delay slot in the same way). A stopped
machine stays stopped. -/
def mips32Next (s : State) : State :=
  if s.trapped then s
  else
    let s1 := fetchExec s
    if s1.trapped ∨ s1.nextPc = s1.pc + 4 then s1 else fetchExec s1

/-- Valid machine states: not in a delay slot, not stopped, word-aligned `pc`. -/
def mips32Ok (s : State) : Bool :=
  s.nextPc == s.pc + 4 && !s.trapped && holAligned 2 s.pc

abbrev Mips32Projection :=
  W × W × (Fin 32 → W) × W × W × Bool × ((W × BitVec 8) → Prop)

/-- Everything `mips32Next` reads, with the memory restricted to the domain. -/
def mips32Proj (d : W → Prop) (s : State) : Mips32Projection :=
  (s.pc, s.nextPc, s.gpr, s.hi, s.lo, s.trapped, SetSep.fun2Set (s.mem.readByte, d))

def mips32Target : HolAsmTarget 32 State Mips32Projection where
  config := mips32Config
  next := mips32Next
  getPc := State.pc
  getReg := fun s n => s.reg (regOf n)
  getFpReg := fun _ _ => 0
  getByte := fun s a => s.mem.readByte a
  stateOk := mips32Ok
  proj := mips32Proj

end Flapjack.Compiler.Encoders.Mips32

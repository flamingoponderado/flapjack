import Flapjack.RiscV.Encoding.NativeInstruction
import Flapjack.Compiler.Encoders.RiscV.Target

/-!
# RISC-V instruction encoding

This is the concrete artifact boundary corresponding to CakeML's
`riscv_encode`/`riscv_enc`.  The typed instruction model is encoded as one
32-bit RV instruction and then emitted in little-endian byte order, matching
the `word8 list` produced by the HOL target encoder.
-/

namespace Flapjack.RiscV

/-- Generic diagnostic emission uses reviewed native bit-field formats.
Six immediate shifts carry arbitrary generic-width shift amounts through
Itype directly, preserving existing diagnostic behavior even outside RV64.
This is not a tagged HOL instruction port at other widths. -/
def encodeInstructionDiagnostic {width : Nat} [NeZero width] : Instruction width → BitVec 32
  | .slli d a i => L3.Itype (0x13,1,nativeRegister d,nativeRegister a,BitVec.ofNat 12 (shiftAmount i))
  | .srli d a i => L3.Itype (0x13,5,nativeRegister d,nativeRegister a,BitVec.ofNat 12 (shiftAmount i))
  | .srai d a i => L3.Itype (0x13,5,nativeRegister d,nativeRegister a,BitVec.ofNat 12 (1024 + shiftAmount i))
  | .slliW d a i => L3.Itype (0x1b,1,nativeRegister d,nativeRegister a,BitVec.ofNat 12 (i.toNat % 32))
  | .srliW d a i => L3.Itype (0x1b,5,nativeRegister d,nativeRegister a,BitVec.ofNat 12 (i.toNat % 32))
  | .sraiW d a i => L3.Itype (0x1b,5,nativeRegister d,nativeRegister a,BitVec.ofNat 12 (1024 + i.toNat % 32))
  | i => L3.Encode (nativeInstructionAtWidth i)

/-- Actual RV64 words use the reviewed native encoder. Other diagnostic widths
retain their prior behavior through native bit-field formats. No old numeric
implementation is reachable from this executable encoder. -/
def encodeInstruction {width : Nat} [NeZero width] (i : Instruction width) : BitVec 32 :=
  if h : width = 64 then
    L3.Encode (nativeInstruction (h ▸ i))
  else encodeInstructionDiagnostic i

def encodeWordBytes (value : BitVec 32) : List (BitVec 8) :=
  [value.extractLsb' 0 8, value.extractLsb' 8 8,
   value.extractLsb' 16 8, value.extractLsb' 24 8]

/-- Source-order native byte slices; this relation is Flapjack infrastructure. -/
theorem encodeWordBytes_eq_extracts (value : BitVec 32) :
    encodeWordBytes value =
      [value.extractLsb' 0 8, value.extractLsb' 8 8,
       value.extractLsb' 16 8, value.extractLsb' 24 8] := rfl

def encodeInstructionBytes [NeZero width] (instruction : Instruction width) :
    List (BitVec 8) :=
  if h : width = 64 then
    Compiler.Encoders.RiscV.Target.riscvEncode (nativeInstruction (h ▸ instruction))
  else encodeWordBytes (encodeInstructionDiagnostic instruction)

def encodeInstructions [NeZero width] : List (Instruction width) → List (BitVec 8)
  | [] => []
  | instruction :: instructions =>
      encodeInstructionBytes instruction ++ encodeInstructions instructions

structure EncodedRiscVSection (width : Nat) where
  label : Nat
  address : Word width
  bytes : List (BitVec 8)
  deriving Repr

def encodeLinkedSections [NeZero width] :
    List (Nat × Word width × List (Instruction width)) →
      List (EncodedRiscVSection width)
  | [] => []
  | (label, address, instructions) :: sections =>
      { label, address, bytes := encodeInstructions instructions } ::
        encodeLinkedSections sections

/-! The closest HOL result is `riscv_targetProof$length_riscv_encode[local]`
    (`LENGTH (riscv_encode i) = 4`).  It quantifies over HOL's full
    `riscv$instruction` type, which includes AMO, floating-point, FENCE,
    system, and unknown-instruction constructors.  `Flapjack.RiscV.Instruction`
    is a width-indexed, hand-ported subset of that datatype and has none of
    those constructors, so this generic Lean length fact is untagged: its
    quantified instruction domain is not the exact HOL domain.  For each
    represented instruction, both encoders emit four bytes. -/
@[simp] theorem encodeInstructionBytes_length [NeZero width]
    (instruction : Instruction width) :
    (encodeInstructionBytes instruction).length = 4 := by
  unfold encodeInstructionBytes
  split <;> simp [encodeWordBytes, Compiler.Encoders.RiscV.Target.riscvEncode]

theorem encodeInstructions_length [NeZero width]
    (instructions : List (Instruction width)) :
    (encodeInstructions instructions).length = 4 * instructions.length := by
  induction instructions with
  | nil => rfl
  | cons instruction instructions induction =>
      simp [encodeInstructions, encodeInstructionBytes_length, induction]
      omega

end Flapjack.RiscV

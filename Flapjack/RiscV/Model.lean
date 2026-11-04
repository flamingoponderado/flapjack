module

public import Std
public import Flapjack.Pancake.PanLang

@[expose] public section

/-!
The first Lean target-model slice for Flapjack's RISC-V backend.

The HOL reference is
`HOL/examples/l3-machine-code/riscv/model/riscv.sml`. This file ports the
architectural vocabulary and executable register, byte-memory, and
straight-line instruction primitives used by later instruction and
compiler-correctness layers. It intentionally does not claim to be the
complete RISC-V transition system yet.
-/

namespace Flapjack.RiscV

abbrev Word (width : Nat) := BitVec width

/-!
The Loop semantics uses homogeneous shift typeclasses.  BitVec exposes its
architectural shifts through heterogeneous instances because the shift count
is itself a BitVec, so provide the corresponding homogeneous views for the
Word-level Loop-to-Word bridge.
-/
instance bitVecWordShiftLeft : ShiftLeft (Word width) :=
  ⟨fun value amount => value <<< amount.toNat⟩

instance bitVecWordShiftRight : ShiftRight (Word width) :=
  ⟨fun value amount => value >>> amount.toNat⟩

instance bitVecWordPanShiftWidth : PanShiftWidth (Word width) where
  width := width
  amount := BitVec.toNat

instance bitVecWordArithmeticShiftRight [NeZero width] :
    ArithmeticShiftRight (Word width) :=
  ⟨fun value amount => BitVec.sshiftRight value amount.toNat⟩

instance bitVecWordRotateRight [NeZero width] : RotateRightOp (Word width) :=
  ⟨fun value amount => BitVec.rotateRight value amount.toNat⟩

inductive AccessType where
  | read
  | write
  deriving DecidableEq, Repr

inductive FetchType where
  | instruction
  | data
  deriving DecidableEq, Repr

inductive Architecture where
  | rv32i
  | rv64i
  | rv128i
  deriving DecidableEq, Repr

def Architecture.width : Architecture → Nat
  | .rv32i => 32
  | .rv64i => 64
  | .rv128i => 128

inductive Privilege where
  | user
  | supervisor
  | hypervisor
  | machine
  deriving DecidableEq, Repr

inductive VMMode where
  | mbare
  | mbb
  | mbbid
  | sv32
  | sv39
  | sv48
  | sv57
  | sv64
  deriving DecidableEq, Repr

inductive ExtStatus where
  | off
  | initial
  | clean
  | dirty
  deriving DecidableEq, Repr

inductive Interrupt where
  | software
  | timer
  deriving DecidableEq, Repr

inductive ExceptionType where
  | fetchMisaligned
  | fetchFault
  | illegalInstr
  | breakpoint
  | loadFault
  | amoMisaligned
  | storeAmoFault
  | uModeEnvCall
  | sModeEnvCall
  | hModeEnvCall
  | mModeEnvCall
  deriving DecidableEq, Repr

structure SynchronousTrap (width : Nat) where
  badAddress : Option (Word width)
  trap : ExceptionType
  deriving DecidableEq, Repr

inductive TransferControl (width : Nat) where
  | branchTo (address : Word width)
  | eReturn
  | mReturn
  | trap (trap : SynchronousTrap width)
  deriving Repr

def aligned (address : Word width) (alignment : Nat) : Bool :=
  alignment ≠ 0 && address.toNat % alignment = 0

def byteAddress (address : Word width) (offset : Nat) : Word width :=
  address + BitVec.ofNat width offset

def shiftAmount (value : Word width) : Nat := value.toNat % width

/-! RV64 word operations compute in the low 32 bits and sign-extend their
    result back to the architectural register width.  The same definitions
    also give the natural RV32 behaviour when `width = 32`. -/
def word32 (value : Word width) : Word width :=
  BitVec.signExtend width (BitVec.extractLsb 31 0 value)

def word32Low (value : Word width) : Word width :=
  BitVec.ofNat width (BitVec.extractLsb 31 0 value).toNat

def wordShiftAmount (value : Word width) : Nat := value.toNat % 32

def uImmediate (immediate : Word width) : Word width :=
  BitVec.shiftLeft
    (BitVec.signExtend width (BitVec.ofNat 20 immediate.toNat)) 12

/-! I-format immediates are encoded from twelve low bits but execute as
    signed values.  Keeping this conversion at the machine boundary lets
    Cake's raw `ORI ... 0x800` materialization execute as -2048 while the
    encoder still emits the same twelve instruction bits. -/
def iImmediate (immediate : Word width) : Word width :=
  if immediate.toNat < 2 ^ 12 then
    BitVec.signExtend width (BitVec.ofNat 12 immediate.toNat)
  else
    immediate

@[simp] theorem iImmediate_zero [NeZero width] : iImmediate (0 : Word width) = 0 := by
  unfold iImmediate
  ext i
  simp [BitVec.getElem_signExtend]

/-! Signed ordering for the two's-complement word represented by `BitVec`. -/
def signedLess (left right : Word width) : Bool :=
  let sign := 2 ^ (width - 1)
  if left.toNat < sign then
    if right.toNat < sign then decide (left.toNat < right.toNat) else false
  else if right.toNat < sign then
    true
  else
    decide (left.toNat < right.toNat)

/-! RISC-V words use unsigned order for `Lower` and signed order for `Less`. -/

instance [NeZero width] : PanCmp (Word width) where
  lower left right := decide (left < right)
  less := signedLess

@[simp] theorem panCmp_word_lower [NeZero width] (left right : Word width) :
    PanCmp.lower left right = decide (left < right) := by
  rfl

@[simp] theorem panCmp_word_less [NeZero width] (left right : Word width) :
    PanCmp.less left right = signedLess left right := by
  rfl

def accessAligned (access : AccessType) (address : Word width) (alignment : Nat) :
    Option ExceptionType :=
  if aligned address alignment then none
  else some (match access with
    | .read => .loadFault
    | .write => .storeAmoFault)

/-! An execution boundary that rejects instructions classified as trapping.
    The total `execute` transition remains the backend's instruction equation;
    this option-valued boundary exposes its architectural rejection path. -/

theorem accessAligned_aligned (access : AccessType) (address : Word width)
    (alignment : Nat) (aligned_address : aligned address alignment = true) :
    accessAligned access address alignment = none := by
  simp [accessAligned, aligned_address]

def jalrTarget (base offset : Word width) : Word width :=
  (base + offset) &&& BitVec.ofNat width (2 ^ width - 2)

end Flapjack.RiscV

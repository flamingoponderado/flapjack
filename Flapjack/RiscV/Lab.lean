import Flapjack.Compiler.Backend.RiscVConfig.RegisterNames
import Flapjack.Lab
import Flapjack.StackAlloc
import Flapjack.StackAlloc.Runtime
import Flapjack.StackRawCall
import Flapjack.RiscV.Ffi
import Flapjack.RiscV.WordToStack
import Flapjack.RiscV.CakeStackReseat
import Flapjack.RiscV.LongDivRuntime

/-!
# LabLang to RISC-V

This module is the first concrete assembler boundary after StackLang
flattening. It computes byte positions for local labels, resolves symbolic
jumps, and lowers the LabLang operations supported by the current RISC-V
model. Unsupported target operations fail through Option rather than being
silently emitted.
-/

namespace Flapjack.RiscV

/-! CakeML's `riscv_ast (Inst (Const r i))` uses three exact constant
    materialization cases.  Keep the arithmetic here in `Nat` so the same
    instruction-selection function can also provide the instruction count
    needed while resolving Lab labels.  The emitted immediates are still
    width-indexed words at the final instruction boundary. -/

def labConstInstructionCount (value : Nat) : Nat :=
  if value < 2 ^ 11 then 1
  else
    let normalized := value % 2 ^ 64
    let low12 := normalized % 2 ^ 12
    let fitsImm12 :=
      normalized ==
        (if low12 / 2 ^ 11 % 2 = 0 then
          low12
        else
          (2 ^ 64 - (2 ^ 12 - low12)) % 2 ^ 64)
    if fitsImm12 then 1
    else
      let low32 := normalized % 2 ^ 32
      let high32 := normalized / 2 ^ 32 % 2 ^ 32
      let low32Sign := low32 / 2 ^ 31 % 2 = 1
      let fitsSigned32 :=
        (high32 = 0 ∧ !low32Sign) ||
          (high32 = 2 ^ 32 - 1 ∧ low32Sign)
      if fitsSigned32 then 2 else 6

def labConditionPreludeCount (operator : Cmp)
    (right : WordRegImm (Word width)) : Nat :=
  match right with
  | .reg _ => match operator with | .test | .notTest => 1 | _ => 0
  | .imm value =>
      if value == 0 then
        match operator with | .test | .notTest => 1 | _ => 1
      else 1

def labFfiStubOffset [NeZero width] (context : WordFfiContext)
    (function : FunName) (position : Nat) : Option (Word width) := do
  let index ← lookupWordFfiIndex function context.services
  /- `context.services` is the source/discovery order and the exported
     prefix reverses it.  From `cake_main`, source service `i` is therefore
     preceded by `i` other FFI blocks, followed by `cake_clear` and
     `cake_exit`: `(3 + i)` 16-byte blocks. -/
  let stubDistance := 3 + index
  pure (0 - BitVec.ofNat width (position + stubDistance * 16))

/-! In the compact linked image the FFI blocks are physically prepended to the
    first returned section, so their target addresses are nonnegative offsets
    from the beginning of that flattened image.  The assembly-facing helper
    above instead addresses Cake's runtime blocks immediately before
    `cake_main`; keeping the two layouts separate avoids sending a compact
    machine probe to a negative wrapped PC. -/
/-- Absolute position of `function`'s linked stub; `labLinkedFfiStubOffset`
    is this relative to the referring line. -/
def labLinkedFfiStubTarget (context : WordFfiContext) (function : FunName) :
    Option Nat := do
  let index ← lookupWordFfiIndex function context.services
  pure ((context.services.length - index - 1) * 16)

def labLinkedFfiStubOffset [NeZero width] (context : WordFfiContext)
    (function : FunName) (position : Nat) : Option (Word width) := do
  let index ← lookupWordFfiIndex function context.services
  let target := (context.services.length - index - 1) * 16
  pure (if target >= position then
    BitVec.ofNat width (target - position)
  else
    0 - BitVec.ofNat width (position - target))

def labLookupPosition (label : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (candidate, position) :: labels =>
      if label == candidate then some position
      else labLookupPosition label labels

def labResolveRef (sectionId : Nat) (labels : List (Nat × Nat)) (ref : LabRef) :
    Option Nat :=
  if ref.sectionId == sectionId then labLookupPosition ref.label labels
  else none

def labOffset [NeZero width] (target position : Nat) : Word width :=
  if target >= position then
    BitVec.ofNat width (target - position)
  else
    0 - BitVec.ofNat width (position - target)

/-! RISC-V's JAL and conditional-branch encodings have different PC-relative
    ranges.  Cake's `riscv_ast` emits a direct JAL when possible and otherwise
    uses AUIPC/JALR; an out-of-range conditional branch is inverted around the
    corresponding jump.  Positions in this port are byte positions, whereas
    the encoders below take care of the architectural halfword encoding. -/
def labJumpOffsetFits (target position : Nat) : Bool :=
  if target >= position then
    target - position <= 2 ^ 20 - 2
  else
    position - target <= 2 ^ 20

def labBranchOffsetFits (target position : Nat) : Bool :=
  if target >= position then
    target - position <= 4095
  else
    position - target <= 4092

/-- The distance from `position` back to `function`'s exported stub;
    `labFfiStubOffset` is the negation of `position + this` as a target word. -/
def labFfiStubDistance (context : WordFfiContext) (function : FunName) :
    Option Nat := do
  let index ← lookupWordFfiIndex function context.services
  pure ((3 + index) * 16)

/-! StackLang's `LocValue` uses register 0 as the conventional link
    register.  The port's ordinary register fields are hardware-numbered, so
    this special carrier must be translated separately; sending port register
    0 through `portToStack` would select the architectural zero register and
    silently discard FFI/install return addresses. -/
def labLocValueRegister (register : Nat) : Option (Fin 32) :=
  if register = 0 then
    labRegisterOfNat (portToStack portLinkRegister)
  else
    labRegisterOfNat (portToStack register)

/-! Cake's RISC-V encoder keeps an immediate comparison operand as an
    explicit temporary, including the zero immediate.  The general evaluator
    helper uses x0 for `Imm 0`, which is semantically equivalent but changes
    the source-shaped artifact and the following label positions.  Preserve
    Cake's `ORI temp, x0, 0` form for ordinary comparisons, while Test/NotTest
    use Cake's explicit zero-ANDI path. -/

/-- The label table a Lab encoding pass resolves against.

    CakeML keeps this in an `sptree` (`lab_to_targetScript`'s `get_label` /
    `find_pos`), not in a list: `enc_secs_again` resolves every label
    reference in the program against it, so the lookup is on the hot path of
    every relocation round and of the final link.

    The list form is kept alongside because the collectors build and compare
    lists -- `labCollectProgramLabelsStable` iterates until the list stops
    changing -- and because it is the order that decides which entry wins. -/
structure LabLabelIndex where
  entries : List (Nat × Nat × Nat)
  /-- Section to label to position, mirroring Cake's per-section `sptree`. -/
  positions : Std.TreeMap Nat (Std.TreeMap Nat Nat)
  deriving Inhabited

/-- Build the index.  `foldr` inserts later entries first, so an earlier
    entry overwrites a later duplicate and the table agrees with the
    first-match list scan it replaces. -/
def labLabelIndexOf (entries : List (Nat × Nat × Nat)) : LabLabelIndex :=
  { entries := entries
    positions := entries.foldr
      (fun entry table =>
        let sectionTable := (table[entry.1]?).getD ∅
        table.insert entry.1 (sectionTable.insert entry.2.1 entry.2.2)) ∅ }

def labLookupProgramPosition (sectionId label : Nat)
    (labels : LabLabelIndex) : Option Nat :=
  match labels.positions[sectionId]? with
  | none => none
  | some sectionTable => sectionTable[label]?

/-! The current concrete Word-to-Stack compiler uses `Nat` for constants,
    while the target backend uses width-indexed words.  Since only conditional
    immediates carry the StackProg type parameter, this adapter is deliberately
    small and explicit. -/
def labAsmNatToWord [NeZero width] : LabAsm Nat → LabAsm (Word width)
  | .jump target => .jump target
  | .jumpCmp operator condition (.imm value) target =>
      .jumpCmp operator condition (.imm (BitVec.ofNat width value)) target
  | .jumpCmp operator condition (.reg register) target =>
      .jumpCmp operator condition (.reg register) target
  | .call target => .call target
  | .locValue register target => .locValue register target
  | .linkValue target => .linkValue target
  | .return register => .return register
  | .callFfi function => .callFfi function
  | .heapAlloc words => .heapAlloc words
  | .install => .install
  | .halt => .halt

def labWordRegImmToWord [NeZero width] : WordRegImm Nat → WordRegImm (Word width)
  | .reg register => .reg register
  | .imm value => .imm (BitVec.ofNat width value)

def labResolveProgramRef (labels : LabLabelIndex) (ref : LabRef) :
    Option Nat :=
  labLookupProgramPosition ref.sectionId ref.label labels

/-! The exported Pancake image has a fixed 1000-byte runtime prefix.  Cake's
    initial `enc_sec_list` sweep, however, positions source sections after the
    pre-finalization runtime layout, whose source base is 1104 bytes.  Keeping
    these bases separate is observable only at long-range relocation
    boundaries, but is required to retain Cake's first-pass instruction slot. -/
def pancakeInitialSourceBase : Nat := 1104

/-! The initial runtime sections occupy 104 bytes more than the exported
    runtime table before Cake's final relocation pass. -/
def pancakeInitialRuntimeLabelOffset : Nat := pancakeInitialSourceBase - 1000

end Flapjack.RiscV

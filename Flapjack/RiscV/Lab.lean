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

def labLineInstructionCount : LabLine (Word width) → Nat
  | .label _ _ _ => 0
  | .asm operation _ _ =>
      match operation with
      | .shift .ror _ _ _ => 5
      | .word (.arith (.shift .ror _ _ (.imm _))) => 3
      | .word (.arith (.shift .ror _ _ (.reg _))) => 5
      | .word (.arith (.longMul _ _ _ _)) => 2
      | .word (.arith (.addCarry _ _ _ _ _)) => 6
      | .word (.arith (.cakeAddCarry _ _ _ _)) => 6
      | .word (.arith (.addOverflow _ _ _ _)) => 6
      | .word (.arith (.subOverflow _ _ _ _)) => 6
      | .word (.const _ value) => labConstInstructionCount value.toNat
      | .const _ value => labConstInstructionCount value
      | .stackMem _ _ _ _ => 1
      | .stackMemSub _ _ _ _ => 1
      | .shareMemOffset _ _ _ _ => 1
      | .arithImm _ destination left immediate =>
          if destination = left && immediate = 0 then 0 else 1
      | .shiftImm .ror _ _ _ => 3
      | .shiftImm _ _ _ _ => 1
      | .tick => 0
      | _ => 1
  | .labAsm operation _ _ =>
      match operation with
      | .jump _ | .call _ | .return _ | .install | .halt => 1
      | .locValue _ _ | .linkValue _ => 2
      | .jumpCmp operator _ right _ => 1 + labConditionPreludeCount operator right
      | .callFfi _ => 1
      | .heapAlloc _ => 1

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

def labCollectLabels (_sectionId : Nat) (position : Nat) :
    List (LabLine (Word width)) → List (Nat × Nat)
  | [] => []
  | .label _ label _ :: lines =>
      if label = 0 then labCollectLabels _sectionId position lines
      else (label, position) :: labCollectLabels _sectionId position lines
  | line :: lines =>
      labCollectLabels _sectionId
        (position + 4 * labLineInstructionCount line) lines

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

def labWordArithToWord [NeZero width] : WordArith Nat → WordArith (Word width)
  | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
      .longMul destinationLeft destinationRight sourceLeft sourceRight
  | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient =>
      .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient
  | .addCarry destination resultCarry sourceLeft sourceRight carryIn =>
      .addCarry destination resultCarry sourceLeft sourceRight carryIn
  | .cakeAddCarry destination sourceLeft sourceRight carry =>
      .cakeAddCarry destination sourceLeft sourceRight carry
  | .addOverflow d l r flag => .addOverflow d l r flag
  | .subOverflow d l r flag => .subOverflow d l r flag
  | .div destination dividend divisor =>
      .div destination dividend divisor
  | .binOp operator destination sourceLeft sourceRight =>
      .binOp operator destination sourceLeft (labWordRegImmToWord sourceRight)
  | .shift operator destination sourceLeft sourceRight =>
      .shift operator destination sourceLeft (labWordRegImmToWord sourceRight)

def labWordInstToWord [NeZero width] : WordInst Nat → WordInst (Word width)
  | .const destination value => .const destination (BitVec.ofNat width value)
  | .arith operation => .arith (labWordArithToWord operation)
  | .mem operator destination address => .mem operator destination address
  | .memOffset operator destination address offset =>
      .memOffset operator destination address (BitVec.ofNat width offset)

def labPlainNatToWord [NeZero width] : LabPlain Nat → LabPlain (Word width)
  | .word instruction => .word (labWordInstToWord instruction)
  | .stackMem operator register base offset =>
      .stackMem operator register base offset
  | .stackMemSub operator register base offset =>
      .stackMemSub operator register base offset
  | .shiftImm operator destination left immediate =>
      .shiftImm operator destination left immediate
  | .const destination value => .const destination value
  | .arith operator destination left right =>
      .arith operator destination left right
  | .arithImm operator destination left immediate =>
      .arithImm operator destination left immediate
  | .shift operator destination left right =>
      .shift operator destination left right
  | .tick => .tick
  | .jumpReg register => .jumpReg register
  | .codeBufferWrite address value => .codeBufferWrite address value
  | .dataBufferWrite address value => .dataBufferWrite address value
  | .shareMem operator register address =>
      .shareMem operator register address
  | .shareMemOffset operator register address offset =>
      .shareMemOffset operator register address (BitVec.ofNat width offset)
  | .memOffset memoryOperator operator destination address offset =>
      .memOffset memoryOperator operator destination address offset

def labLineNatToWord [NeZero width] : LabLine Nat → LabLine (Word width)
  | .label sectionId label length => .label sectionId label length
  | .asm operation bytes length =>
      .asm (labPlainNatToWord operation) bytes length
  | .labAsm operation bytes length =>
      .labAsm (labAsmNatToWord operation) bytes length

def labSectionNatToWord [NeZero width] (sectionData : LabSection Nat) :
    LabSection (Word width) :=
  { name := sectionData.name
    lines := sectionData.lines.map labLineNatToWord }

def labSectionInstructionCount (sectionData : LabSection (Word width)) : Nat :=
  sectionData.lines.foldl
    (fun count line => count + labLineInstructionCount line) 0

/-- Executed static label-position estimate. As in HOL compute_labels_alt,
section zero denotes the section base, independent of explicit zero labels.
This is untagged infrastructure: positions here use production instruction
counts rather than the original encoded line lengths. -/
def labCollectProgramLabels (base : Nat) :
    LabProgram (Word width) → List (Nat × Nat × Nat)
  | [] => []
  | sectionData :: sections =>
      let localLabels := labCollectLabels sectionData.name 0 sectionData.lines
      let globalLabels := localLabels.map
        (fun (label, position) => (sectionData.name, label, base + position))
      (sectionData.name, 0, base) :: globalLabels ++ labCollectProgramLabels
        (base + 4 * labSectionInstructionCount sectionData) sections

def labResolveProgramRef (labels : LabLabelIndex) (ref : LabRef) :
    Option Nat :=
  labLookupProgramPosition ref.sectionId ref.label labels

/-! CakeML's target assembler turns `Halt` into a jump to the target's halt
    PC.  The existing ordinary compiler intentionally rejects that pseudo-op;
    this parallel path computes a halt PC immediately after the linked image,
    emits the jump, and appends a self-loop at that PC. -/

def labProgramInstructionCount : LabProgram (Word width) → Nat
  | [] => 0
  | sectionData :: sections =>
      labSectionInstructionCount sectionData + labProgramInstructionCount sections

/-! A linked FFI call is nested inside an ordinary Cake function call.  Its
    continuation must not overwrite the caller's `x1` link: the service stub
    returns through the reserved scratch `x31`, while the ordinary function
    return still uses `x1`.  Rebase only the linked FFI carrier here; the
    generic Lab flattening contract retains the source `returnAddress` field. -/
def labRebaseLinkedFfiReturnLines [NeZero width] :
    List (LabLine (Word width)) → List (LabLine (Word width))
  | .labAsm (.locValue _ target) bytes length ::
      .labAsm (.callFfi function) callBytes callLength :: lines =>
      .labAsm (.locValue 31 target) bytes length ::
        .labAsm (.callFfi function) callBytes callLength ::
          labRebaseLinkedFfiReturnLines lines
  | line :: lines => line :: labRebaseLinkedFfiReturnLines lines
  | [] => []

/-! Cake's `enc_lines_again` retains the maximum encoded length of a LabAsm
    across relocation iterations. A branch that first needs two instructions
    and later fits in one therefore keeps a two-instruction slot; `pad_code`
    fills the residual slot with the encoded Skip. The ordinary linker above
    recomputes only the final length, losing this source-shaped artifact. -/

def labStoredLineLength {width : Nat} [NeZero width] :
    LabLine (Word width) → Nat
  | .label _ _ length => length
  | .asm _ _ length => length
  | .labAsm _ _ length => length

def labStoredSectionLength {width : Nat} [NeZero width] :
    List (LabLine (Word width)) → Nat
  | [] => 0
  | line :: lines => labStoredLineLength line + labStoredSectionLength lines

def labStoredProgramLength {width : Nat} [NeZero width] :
    LabProgram (Word width) → Nat
  | [] => 0
  | sectionData :: sections =>
      labStoredSectionLength sectionData.lines + labStoredProgramLength sections

def labInitialStoredLine [NeZero width] :
    LabLine (Word width) → LabLine (Word width)
  /- Every real label starts with Cake's four-byte relocation slot
     (`lab_to_target$enc_line_def`). The native section codec introduces no
     synthetic entry labels, so section position does not exempt a label. -/
  | .label sectionId label _ =>
      .label sectionId label 4
  | .asm operation bytes _ =>
      .asm operation bytes (4 * labLineInstructionCount (.asm operation bytes 0))
  | .labAsm operation bytes _ =>
      .labAsm operation bytes (4 * labLineInstructionCount
        (.labAsm operation bytes 0))

def labInitialStoredEntryLine [NeZero width] :
    LabLine (Word width) → LabLine (Word width)
  | .label sectionId label _ => .label sectionId label 0
  | line => labInitialStoredLine line

def labInitialStoredSectionLines [NeZero width] :
    Nat → List (LabLine (Word width)) → List (LabLine (Word width))
  | _, [] => []
  | 0, line :: lines =>
      labInitialStoredLine line :: labInitialStoredSectionLines 0 lines
  | fuel + 1, line :: lines =>
      labInitialStoredEntryLine line ::
        labInitialStoredSectionLines fuel lines

def labInitialStoredProgram [NeZero width] :
    LabProgram (Word width) → LabProgram (Word width)
  | [] => []
  | sectionData :: sections =>
      { sectionData with
          lines := sectionData.lines.map labInitialStoredLine } ::
        labInitialStoredProgram sections

def labCollectStoredSectionLabels [NeZero width] (sectionId base : Nat) :
    List (LabLine (Word width)) → List (Nat × Nat × Nat)
  | [] => []
  | .label _ label length :: lines =>
      if label = 0 then
        labCollectStoredSectionLabels sectionId (base + length) lines
      else
        (sectionId, label, base + length) ::
          labCollectStoredSectionLabels sectionId (base + length) lines
  | line :: lines =>
      labCollectStoredSectionLabels sectionId
        (base + labStoredLineLength line) lines

def labCollectStoredProgramLabels [NeZero width] (base : Nat) :
    LabProgram (Word width) → List (Nat × Nat × Nat)
  | [] => []
  | sectionData :: sections =>
      ((sectionData.name, 0, base) ::
        labCollectStoredSectionLabels sectionData.name base sectionData.lines) ++
        labCollectStoredProgramLabels
          (base + labStoredSectionLength sectionData.lines) sections

def labCollectPancakeRuntimeStoredLabelsAt [NeZero width] (sourceBase : Nat)
    (program : LabProgram (Word width)) : List (Nat × Nat × Nat) :=
  let sourceProgram := program.filter (fun entry => entry.name >= 3)
  [(0, 0, 812), (1, 0, 848), (2, 0, 772)] ++
    labCollectStoredProgramLabels sourceBase sourceProgram

def labCollectPancakeRuntimeStoredLabelsAtWithRuntimeOffset [NeZero width]
    (sourceBase runtimeOffset : Nat) (program : LabProgram (Word width)) :
    List (Nat × Nat × Nat) :=
  let sourceProgram := program.filter (fun entry => entry.name >= 3)
  [(0, 0, 812 + runtimeOffset), (1, 0, 848 + runtimeOffset),
      (2, 0, 772 + runtimeOffset)] ++
    labCollectStoredProgramLabels sourceBase sourceProgram

def labCollectPancakeRuntimeStoredLabels [NeZero width]
    (program : LabProgram (Word width)) : List (Nat × Nat × Nat) :=
  labCollectPancakeRuntimeStoredLabelsAt 1000 program

/-! The exported Pancake image has a fixed 1000-byte runtime prefix.  Cake's
    initial `enc_sec_list` sweep, however, positions source sections after the
    pre-finalization runtime layout, whose source base is 1104 bytes.  Keeping
    these bases separate is observable only at long-range relocation
    boundaries, but is required to retain Cake's first-pass instruction slot. -/
def pancakeInitialSourceBase : Nat := 1104

/-! The initial runtime sections occupy 104 bytes more than the exported
    runtime table before Cake's final relocation pass. -/
def pancakeInitialRuntimeLabelOffset : Nat := pancakeInitialSourceBase - 1000

/-- Every line's stored length, in order.  This is what CakeML's
    `remove_labels_loop` tests with `all_lengths_ok` to decide whether another
    `enc_secs_again` round is needed. -/
def labStoredLineLengths [NeZero width] :
    LabProgram (Word width) → List Nat
  | [] => []
  | sectionData :: sections =>
      sectionData.lines.map (fun line =>
        match line with
        | .label _ _ length => length
        | .asm _ _ length => length
        | .labAsm _ _ length => length)
        ++ labStoredLineLengths sections

def labUpdateStoredLabelLengths [NeZero width] (base : Nat) :
    LabProgram (Word width) → LabProgram (Word width)
  | [] => []
  | sectionData :: sections =>
      let rec updateLines (position : Nat) :
          List (LabLine (Word width)) → List (LabLine (Word width))
        | [] => []
        | .label sectionId label _ :: lines =>
            let length := if position % 2 = 0 then 0 else 1
            .label sectionId label length ::
              updateLines (position + length) lines
        | .asm operation bytes length :: lines =>
            .asm operation bytes length :: updateLines (position + length) lines
        | .labAsm operation bytes length :: lines =>
            .labAsm operation bytes length :: updateLines (position + length) lines
      let lines := updateLines base sectionData.lines
      { sectionData with lines := lines } ::
        labUpdateStoredLabelLengths (base + labStoredSectionLength lines) sections

/-! The Pancake artifact carries Cake's fixed runtime byte prefix separately.
    Runtime sections 0, 1, and 2 remain symbolic jump targets, but do not
    contribute to the linked source-section base. -/
def labCollectPancakeRuntimeLabels : LabProgram (Word width) →
    List (Nat × Nat × Nat)
  | program =>
      let sourceProgram := program.filter (fun entry => entry.name >= 3)
      [(0, 0, 812), (1, 0, 848), (2, 0, 772)] ++
        labCollectProgramLabels 1000 sourceProgram

/-! Source-shaped Cake lowering keeps abstract `riscv_names` stack registers
    through StackRemove.  The executable Lab compiler above consumes the
    historical hardware-numbered representation, so apply the register map
    exactly once to the completed StackProg before entering it. -/
def stackRemoveCakeProgram (config : StackRemoveConfig) (program : StackProg Nat) :
    StackProg Nat :=
  stackMapRegisters Flapjack.Compiler.Backend.RiscVConfig.riscvNameLookup
    (stackRemoveComplete (cakeStackRemoveConfig config) program)

/-! Linked counterpart of the bitmap/simple-GC entry point.  Keeping the
runtime sections in the same Lab linker as ordinary functions preserves their
resolved entry addresses for machine-level correctness harnesses. -/

theorem labLineInstructionCount_ffi :
    labLineInstructionCount
        (.labAsm (.callFfi "sum") [] 0 : LabLine (Word width)) = 1 := by
  rfl

/-! Cake's RISC-V `cakeAddCarry` expands to six instructions.  Keep the
    section-size accounting tied to that source expansion so later labels do
    not drift when a carry operation is present. -/
theorem labLineInstructionCount_cakeAddCarry :
    labLineInstructionCount
        (.asm (.word (.arith (.cakeAddCarry 10 10 16 1))) [] 0 :
          LabLine (Word width)) = 6 := by
  rfl

end Flapjack.RiscV

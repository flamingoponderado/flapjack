import Flapjack.Stack
import Flapjack.RiscV.Allocator
import Flapjack.RiscV.RegAlloc
import Flapjack.RiscV.CakeAllocatorCore
import Flapjack.Compiler.Backend.WordToStack

/-!
# Word-to-Stack spill moves

This is the first executable consumer of the spill locations produced by the
Word allocator.  It ports the essential `wMoveSingle` cases from CakeML's
`word_to_stackScript.sml`: a virtual variable is either represented by a
physical register or by a slot in the current stack frame, and `x31` is used
as the temporary for moves involving stack locations.

The full CakeML pass also lowers every Word instruction and maintains GC
bitmaps.  Those later pieces will build on this total location lookup and its
explicit move cases.
-/

namespace Flapjack.RiscV

/-! The executable StackLang model carries hardware RISC-V register numbers
    directly at the ABI boundary.  The CakeML ABI's first argument/result
    register is stack register 1, which is hardware `x10`; the existing `+2`
    layout supplies subsequent word locations. -/
def wordStackAbiBase : Nat := 10

/-! A `LocValue` materializes a code label, rather than reading a source
    variable.  A register destination can receive the StackLang instruction
    directly; a spilled destination is materialized in the reserved scratch
    register and then stored in its stack slot.  The entry field is zero for
    the ordinary code-label values emitted by CakeML's Word-to-Stack pass. -/

/- Cake's `wReg1` lowers a spilled store address through the first allocator
   register `k`.  `scratch` is that register in the source-shaped RISC-V
   configuration; the next register (`addressScratch`) is reserved for
   `wReg2` operands and is used for a spilled store value. -/

def wordMoveDestinations (moves : List (Nat × Nat)) : List Nat :=
  moves.map (fun move => move.1)

def wordMoveRemoveDestination (destination : Nat) :
    List (Nat × Nat) → List (Nat × Nat) :=
  List.filter (fun move => move.1 != destination)

def wordMoveReady (destinations : List Nat) :
    List (Nat × Nat) → Option (Nat × Nat)
  | [] => none
  | move :: moves =>
      if move.1 ∉ destinations then
        some move
      else
        wordMoveReady destinations moves
termination_by moves => sizeOf moves
decreasing_by all_goals decreasing_trivial

/-! Bitmap accumulation used by CakeML's `word_to_stack` pass.

    CakeML stores bitmaps as a flat append-only word list.  The first word of
    each bitmap chunk records which following constant words are pointers;
    liveness bitmaps have one additional terminating pointer bit.  Keeping
    the accumulator explicit makes the state change caused by `Alloc` and
    `StoreConsts` observable, rather than silently rejecting those Word
    constructors as the stateless compiler above must do. -/

def wordStackBitsToNat : List Bool → Nat
  | [] => 1
  | bit :: bits =>
      wordStackBitsToNat bits * 2 + if bit then 1 else 0

def wordStackBitmapChunk (constants : List (Bool × Nat)) : List Nat :=
  wordStackBitsToNat (constants.map Prod.fst) :: constants.map Prod.snd

def wordStackBitmapWordsAux (chunkSize : Nat) :
    Nat → List Bool → List Nat
  | 0, _ => []
  | fuel + 1, bits =>
      if chunkSize = 0 || bits.length ≤ chunkSize then
        [wordStackBitsToNat bits]
      else
        wordStackBitsToNat (bits.take chunkSize ++ [true]) ::
          wordStackBitmapWordsAux chunkSize fuel (bits.drop chunkSize)

def wordStackBitmapWords (chunkSize : Nat) (bits : List Bool) : List Nat :=
  wordStackBitmapWordsAux chunkSize (bits.length + 1) bits

def wordStackConstBitmapWordsAux (wordBits : Nat) :
    Nat → List (Bool × Nat) → List Nat
  | 0, _ => []
  | fuel + 1, constants =>
      let chunkSize := wordBits - 1
      if chunkSize = 0 || constants.length < chunkSize then
        wordStackBitmapChunk constants
      else
        wordStackBitmapChunk (constants.take chunkSize) ++
          wordStackConstBitmapWordsAux wordBits fuel (constants.drop chunkSize)

def wordStackConstBitmapWords (wordBits : Nat)
    (constants : List (Bool × Nat)) : List Nat :=
  wordStackConstBitmapWordsAux wordBits (constants.length + 1) constants

def wordStackLiveBitmap (registerCount frameSlots wordBits : Nat)
    (live : List Nat) : List Nat :=
  let names := live.map (fun register =>
    frameSlots - 1 - (register / 2 - registerCount))
  let bits := (List.range frameSlots).map (fun slot => names.contains slot)
  wordStackBitmapWords (wordBits - 1) (bits ++ [true])

/-! A compact executable semantics for the move fragment.  StackLang uses
natural-number register names, so this boundary deliberately models the
register file and frame slots independently of the later byte-addressed
RISC-V stack representation. -/
structure WordStackState (width : Nat) where
  registers : Nat → Word width
  stack : Nat → Word width

def wordStackWriteRegister [NeZero width] (state : WordStackState width)
    (register : Nat) (value : Word width) : WordStackState width :=
  { state with registers := fun current =>
      if current = register then value else state.registers current }

def wordStackWriteSlot [NeZero width] (state : WordStackState width)
    (slot : Nat) (value : Word width) : WordStackState width :=
  { state with stack := fun current =>
      if current = slot then value else state.stack current }

/-! A slightly richer executable StackLang semantics for the concrete Nat
    compiler.  It is intentionally an abstract word-memory model: byte
    layout and RISC-V instruction encoding remain below StackLang, while this
    state is sufficient to state expression-lowering preservation. -/

def wordStackMachineBinOp : BinOp → Word width → Word width → Word width
  | .add, left, right => left + right
  | .sub, left, right => left - right
  | .and, left, right => left &&& right
  | .or, left, right => left ||| right
  | .xor, left, right => left ^^^ right

def wordStackMachineRotateRight (value : Word width) (amount : Word width) :
    Word width :=
  let amount := amount.toNat % width
  BitVec.ushiftRight value amount |||
    BitVec.shiftLeft value ((width - amount) % width)

def wordStackMachineShift : Shift → Word width → Word width → Word width
  | .lsl, left, right => BitVec.shiftLeft left (shiftAmount right)
  | .lsr, left, right => BitVec.ushiftRight left (shiftAmount right)
  | .asr, left, right => BitVec.sshiftRight left (shiftAmount right)
  | .ror, left, right => wordStackMachineRotateRight left right

/-! The StackLang `LongDiv` operation follows CakeML's word convention: the
    two source words form one unsigned double-width dividend, the divisor must
    be nonzero, and the quotient must fit in one word.  Returning `none` for
    either failed precondition matches the source/StackLang semantics. -/
def wordStackLongDivResult [NeZero width]
    (sourceLeft sourceRight divisor : Word width) :
    Option (Word width × Word width) :=
  let divisorValue := divisor.toNat
  let dividendValue := sourceLeft.toNat * 2 ^ width + sourceRight.toNat
  if divisorValue == 0 then
    none
  else
    let quotient := dividendValue / divisorValue
    if quotient < 2 ^ width then
      some (BitVec.ofNat width quotient,
        BitVec.ofNat width (dividendValue % divisorValue))
    else
      none

end Flapjack.RiscV

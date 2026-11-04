module

public import Flapjack.MemOp
public import Flapjack.Pancake.LoopLive
public import Flapjack.NumSet

@[expose] public section

/-!
The Word intermediate language used by CakeML's backend. This first port
keeps the register-level instruction set small but preserves the structure
needed by `loop_to_word`: words, register expressions, memory instructions,
calls, loops, and foreign calls.
-/

namespace Flapjack

inductive WordStore (α : Type u) where
  | temp (address : BitVec 5)
  | nextFree
  | endOfHeap
  | triggerGC
  | currHeap
  | heapLength
  | progStart
  | bitmapBase
  | otherHeap
  | allocSize
  | globals
  | globReal
  | handler
  | genStart
  | codeBuffer
  | codeBufferEnd
  | bitmapBuffer
  | bitmapBufferEnd
  deriving DecidableEq, Repr

inductive WordRegImm (α : Type u) where
  | imm (value : α)
  | reg (name : Nat)
  deriving DecidableEq, Repr

end Flapjack

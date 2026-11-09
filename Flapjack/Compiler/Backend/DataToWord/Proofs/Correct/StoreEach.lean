module

public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
public import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListExists

@[expose] public section

/-! Execution of the constructor's consecutive word stores. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack

/-- Memory produced by consecutive stores, retaining the word machine's
last-write-wins behavior even if addresses wrap around. -/
def storeEachMemory {width : Nat} [NeZero width] (base offset : BitVec width) :
    List (WordLocW width) → (BitVec width → WordLocW width) → BitVec width → WordLocW width
  | [], memory => memory
  | value :: values, memory =>
      storeEachMemory base (offset + BitVec.ofNat width (width / 8)) values
        (fun address => if address = base + offset then value else memory address)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct

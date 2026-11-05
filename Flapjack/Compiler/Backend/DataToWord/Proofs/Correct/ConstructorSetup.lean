import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ConstructorHeap
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Address

/-! Generated scratch-register setup for constructor allocation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Computing the pointer from `nextFree - currHeap` gives the abstract
constructor address on supported word widths. -/
theorem constructor_pointerValue {width : Nat} [NeZero width] (conf : Config)
    (tag len index : Nat) (curr : BitVec width) (good : goodDimindex width)
    (shiftBound : wordShiftAmount width ≤ shiftLength conf) :
    (((curr + StackRemove.bytesInWord width * BitVec.ofNat width index - curr) <<<
        (shiftLength conf - wordShiftAmount width)) |||
      getLowerBits conf (.word (ptrBits conf tag len))) =
      getAddr conf index (.word (ptrBits conf tag len)) := by
  simp only [getAddr, BitVec.add_comm curr, BitVec.add_sub_cancel]
  rw [BitVec.mul_comm, ← shiftWordBytes good, ← BitVec.shiftLeft_add]
  have shiftEq : wordShiftAmount width + (shiftLength conf - wordShiftAmount width) = shiftLength conf := by omega
  rw [shiftEq]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct

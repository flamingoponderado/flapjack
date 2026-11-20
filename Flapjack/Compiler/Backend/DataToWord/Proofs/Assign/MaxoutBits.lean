module

public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Numbers

@[expose] public section

/-! Agreement of the source-shaped pointer-field code with the former executable. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord

/-- Flapjack-specific executable equivalence: the former arithmetic mask and
HOL slice produce identical target programs at every positive word width. -/
theorem maxoutBitsCode_eq_inlined {width : Nat} [NeZero width] (bits shift dest src : Nat) :
    maxoutBitsCode (width := width) bits shift dest src =
      .ite .lower src (.imm (BitVec.ofNat width (2 ^ bits - 1)))
        (.assign dest (.op .or [.var dest, shiftN .lsl (.var src) shift]))
        (.assign dest (.op .or [.var dest, .const (BitVec.ofNat width ((2 ^ bits - 1) * 2 ^ shift))])) := by
  simp [maxoutBitsCode, allOnes_eq_inlined]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

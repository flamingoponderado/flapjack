module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ValueEquality

@[expose] public section

/-! Results captured under `vb_eq_size_*` in the HOL memory representation probe. -/
namespace Flapjack.Test.DataToWordValueEqualityParity
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private def refs : Spt (BvlSem.Ref Nat) := .ln

example : vbEqSize refs (.number 7) (.number 7) = some (1, true) := by
  simp [vbEqSize]

example : vbEqSize refs (.block 0 2 [.number 7, .number 8])
    (.block 1 2 [.number 7, .number 9]) = some (5, false) := by
  simp [vbEqSize, vbEqSizeList, isClosure]

example : vbEqSize refs (.block 0 30 [.number 7]) (.block 0 31 [.number 9]) = some (1, true) := by
  simp [vbEqSize, isClosure]

example : vbEqSize refs (.block 0 30 [.number 7]) (.block 0 2 [.number 7]) = none := by
  simp [vbEqSize, isClosure]

example : vbEqSizeList refs [.number 7, .codePtr 1] [.number 8, .codePtr 1] = some (2, false) := by
  simp [vbEqSize, vbEqSizeList]

example : vbEqSizeList refs [.number 7, .codePtr 1] [.number 7, .codePtr 1] = none := by
  simp [vbEqSize, vbEqSizeList]

end Flapjack.Test.DataToWordValueEqualityParity

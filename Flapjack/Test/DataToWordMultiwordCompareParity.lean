import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordCompare

/-! The `mw_cmp_*32` results are captured from the pinned HOL implementation. -/
namespace Flapjack.Test.DataToWordMultiwordCompareParity
open Flapjack Flapjack.Misc.Multiword

example : mwCmp ([1, 2] : List (BitVec 32)) [1, 2] = none := by
  rw [mwCmp]
  simp [holLast]
  rw [mwCmp]
  simp [holLast]
  rw [mwCmp]
  rfl

example : mwCmp ([1, 2] : List (BitVec 32)) [4, 2] = some true := by
  rw [mwCmp]
  simp [holLast]
  rw [mwCmp]
  simp [holLast]

example : mwCmp ([1, 3] : List (BitVec 32)) [4, 2] = some false := by
  rw [mwCmp]
  simp [holLast]

end Flapjack.Test.DataToWordMultiwordCompareParity

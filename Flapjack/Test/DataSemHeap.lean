import Flapjack.Compiler.Backend.Semantics.DataSem.Heap

/-! Heap-space accounting on shared blocks and cyclic references. -/
namespace Flapjack.Test.DataSemHeap
open Flapjack
open Flapjack.Compiler.Backend
open DataSem

private def limits : Limits := ⟨1000, 1000, 1000, true, false, false⟩

example : bignumDigits true 0 = 0 := by rw [bignumDigits]; rfl
example : bignumDigits true (2 ^ 64) = 2 := by
  rw [bignumDigits, bignumDigits, bignumDigits]
  decide

/-- The tail root is visited first, so the second block sharing timestamp 7
is the only one whose payload contributes to the total. -/
example : (sizeOfValues limits
    [.block 7 5 [.word64 0], .block 7 6 [.number 9]] .ln .ln).1 = 2 := by
  simp [sizeOfValues, checkRes, sptSize, sptLookup, sptInsert, smallNum, limits]

/-- A reference to itself is removed before its payload is traversed. -/
example : (sizeOfValues limits [.refPtr true 0]
    (.ls (.valueArray [.refPtr true 0])) .ln).1 = 2 := by
  simp [sizeOfValues, sptLookup, sptDelete]

example : sptToList (.bs (.ls 2) 3 (.ls 4)) = [2, 3, 4] := by
  rfl

end Flapjack.Test.DataSemHeap

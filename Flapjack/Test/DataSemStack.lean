module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Stack

@[expose] public section

/-! Data-language stack-bound edge cases. -/
namespace Flapjack.Test.DataSemStack
open Flapjack
open Flapjack.Compiler.Backend
open DataSem

private def limits : Limits := ⟨1000, 1000, 1000, true, false, false⟩

example : valueDepth (.block 0 3 [.number 1, .block 1 2 [.number 5]]) = 2 := by
  simp [valueDepth, valuesDepth]

example : valueBlockSize (.block 0 3 [.number 1, .block 1 2 [.number 5]]) = 12 := by
  simp [valueBlockSize]

example : stackConsumed .ln limits (.intOp .mult) [.number 2, .number 3] = some 0 := by
  simp [stackConsumed, smallNum, limits]

example : stackConsumed .ln limits (.intOp .mult) [.number (-2), .number 3] = none := by
  simp [stackConsumed, smallNum, limits, sptLookup]

example : stackConsumed .ln limits .install [] = none := by
  simp [stackConsumed, allowedOp]

end Flapjack.Test.DataSemStack

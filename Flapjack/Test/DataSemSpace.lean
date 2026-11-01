import Flapjack.Compiler.Backend.Semantics.DataSem.Space

/-! Boundary cases in data-language allocation bounds. -/
namespace Flapjack.Test.DataSemSpace
open Flapjack
open Flapjack.Compiler.Backend
open DataSem

example : holIntDiv 7 3 = 2 := by
  rw [holIntDiv_spec 7 3 (by decide)]
  rfl

example : holIntDiv (-7) 3 = -3 := by
  rw [holIntDiv_spec (-7) 3 (by decide)]
  rfl

example : holIntMod (-7) 3 = 2 := by
  rw [holIntMod_spec (-7) 3 (by decide), holIntDiv_spec (-7) 3 (by decide)]
  rfl

example {C F : Type} (state : State C F) :
    spaceConsumed state (.memOp .refArray) [.number (-3), .number 0] = 1 := by
  simp [spaceConsumed]

example {C F : Type} (state : State C F) :
    spaceConsumed state (.blockOp (.consExtend 4))
      [.block 0 5 [.number 1, .number 2, .number 3], .number 1,
       .number 2, .number 9, .number 4] = 4 := by
  simp [spaceConsumed]

example {C F : Type} (state : State C F) (h : state.limits.arch64Bit = true) :
    spaceConsumed state (.intOp .add) [.number 4, .number 7] = 0 := by
  simp [spaceConsumed, smallNum, h]

end Flapjack.Test.DataSemSpace

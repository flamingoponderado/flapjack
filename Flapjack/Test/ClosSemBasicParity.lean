import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBasic

/-! Replay block-operation observations from the pinned HOL probe. -/
namespace Flapjack.Test.ClosSemBasicParity
open Flapjack.Compiler.Backend.ClosSem

example : getGlobal 0 [some (3 : Nat), none] = some (some 3) := rfl
example : getGlobal 1 [some (3 : Nat), none] = some none := rfl
example : getGlobal 2 [some (3 : Nat), none] = none := rfl
example : unitValue = .block 0 [] := rfl

example {C F : Type} (s : State C F) :
    applyBlock (.tagLenEq 2 1) [.block 2 [.number 9]] s = some (.block 1 [], s) := rfl
example {C F : Type} (s : State C F) :
    applyBlock (.lenEq 1) [.block 4 [.number 9]] s = some (.block 1 [], s) := rfl
example {C F : Type} (s : State C F) :
    applyBlock (.boolTest .equal) [.block 0 [], .block 1 []] s = some (.block 0 [], s) := rfl
example {C F : Type} (s : State C F) :
    applyBlock (.boolTest .equal) [.block 1 [], .block 1 []] s = some (.block 1 [], s) := rfl
example {C F : Type} (s : State C F) :
    applyBlock (.boolTest .equal) [.block 2 [], .block 1 []] s = none := rfl
example {C F : Type} (s : State C F) :
    applyBlock .boolNot [.block 0 []] s = some (.block 1 [], s) := rfl
example {C F : Type} (s : State C F) :
    applyBlock .boolNot [.block 1 [.number 0]] s = none := rfl
example {C F : Type} (s : State C F) :
    applyBlock (.consExtend 2) [.block 0 [.number 1, .number 2, .number 3], .number 1, .number 2,
      .number 3, .number 8] s = some (.block 2 [.number 8, .number 2, .number 3], s) := rfl
example {C F : Type} (s : State C F) :
    applyBlock (.consExtend 2) [.block 0 [.number 1], .number 1, .number 2, .number 2] s = none := rfl
example {C F : Type} (s : State C F) :
    applyBlock (.constant (.constCons 4 [.constInt 3, .constInt 7])) [] s =
      some (.block 4 [.number 3, .number 7], s) := by simp [applyBlock, makeConst]
example : makeConst (.constCons 4 [.constInt (-3), .constWord64 18446744073709551615,
    .constStr (.implode [0, 128, 255])]) =
    .block 4 [.number (-3), .word64 18446744073709551615, .byteVector [0, 128, 255]] := by
  simp [makeConst]

end Flapjack.Test.ClosSemBasicParity

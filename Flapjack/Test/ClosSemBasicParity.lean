import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBasic

/-! Replay block-operation observations from the pinned HOL probe. -/
namespace Flapjack.Test.ClosSemBasicParity
open Flapjack.Compiler.Backend.ClosSem

example {C F : Type} (s : State C F) :
    applyBlock (.tagLenEq 2 1) [.block 2 [.number 9]] s = some (.block 1 [], s) := rfl
example {C F : Type} (s : State C F) :
    applyBlock (.lenEq 1) [.block 4 [.number 9]] s = some (.block 1 [], s) := rfl
example {C F : Type} (s : State C F) :
    applyBlock (.boolTest .equal) [.block 0 [], .block 1 []] s = some (.block 0 [], s) := rfl
example {C F : Type} (s : State C F) :
    applyBlock (.consExtend 2) [.block 0 [.number 1, .number 2, .number 3], .number 1, .number 2,
      .number 3, .number 8] s = some (.block 2 [.number 8, .number 2, .number 3], s) := rfl
example {C F : Type} (s : State C F) :
    applyBlock (.consExtend 2) [.block 0 [.number 1], .number 1, .number 2, .number 2] s = none := rfl
example {C F : Type} (s : State C F) :
    applyBlock (.constant (.constCons 4 [.constInt 3, .constInt 7])) [] s =
      some (.block 4 [.number 3, .number 7], s) := by simp [applyBlock, makeConst]

end Flapjack.Test.ClosSemBasicParity

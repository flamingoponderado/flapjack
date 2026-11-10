module

public import Flapjack.RiscV.WordToStack
public import Flapjack.Compiler.Backend.WordToStack.NativeMoves

@[expose] public section

namespace Flapjack.Test.ProductionScheduler
open Flapjack RiscV

/-! Kernel computation fixtures for optional scheduling. -/
-- Original sr_none_slot: NONE maps to the second reserved scratch, 23.
example : Compiler.Backend.WordToStackRegFormat.formatVar 22 none = .inl 23 := by cbv
-- Full original sr_spill_cycle tree: NONE uses23, spill-to-spill uses22.
example : Compiler.Backend.WordToStack.Native.wMoveNative (width := 64)
    [(44,46),(46,44)] (22,3,2) =
      .seq (.stackLoad 23 1)
        (.seq (.seq (.stackLoad 22 2) (.stackStore 22 1)) (.stackStore 23 2)) := by cbv
-- Original zero-frame observation retains natural subtraction at every slot.
example : Compiler.Backend.WordToStack.Native.wMoveNative (width := 64)
    [(44,46),(46,44)] (22,0,0) =
      .seq (.stackLoad 23 0)
        (.seq (.seq (.stackLoad 22 0) (.stackStore 22 0)) (.stackStore 23 0)) := by cbv

end Flapjack.Test.ProductionScheduler

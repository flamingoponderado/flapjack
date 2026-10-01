import Flapjack.Compiler.Backend.WordToStack.ProductionScheduler
import Flapjack.Compiler.Backend.WordToStack.NativeMoves

namespace Flapjack.Test.ProductionScheduler
open Flapjack RiscV

/-! Kernel computation fixtures for optional scheduling. -/
example : wordStackCakeParallelOptionOrder [] = some [] := by cbv
example : wordStackCakeParallelOptionOrder [(.register 0, .register 0)] = some [] := by cbv
example : wordStackCakeParallelOptionOrder [(.register 0, .register 1), (.register 0, .register 2)] =
    some [(some (.register 0), some (.register 1)), (some (.register 0), some (.register 2))] := by cbv
example : wordStackCakeParallelOptionOrder [(.register 0, .register 1), (.register 1, .register 0)] =
    some [(none, some (.register 1)), (some (.register 1), some (.register 0)),
      (some (.register 0), none)] := by cbv
example : wordStackCakeParallelOptionOrder [(.stack 0, .register 1), (.register 1, .stack 0)] =
    some [(none, some (.register 1)), (some (.register 1), some (.stack 0)),
      (some (.stack 0), none)] := by cbv
example (moves : List (WordLocation × WordLocation)) :
    wordStackCakeParallelOptionOrder moves =
      some (Compiler.Backend.Parmove.parmove moves) :=
  ProductionScheduler.optionOrder_eq_parmove moves

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

def runChecks : IO Bool := do
  IO.println "PASS actual option scheduler and native temporary/frame fixtures match original HOL rows"
  pure true

end Flapjack.Test.ProductionScheduler

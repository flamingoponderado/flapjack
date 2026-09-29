import Flapjack.Pipeline

/-!
# Production Loop-to-Word comp_func route checks

These fixtures exercise the fixed-width production wrapper, rather than only
the HOL definition. They cover recursive control flow, call handlers, direct
memory operations, and byte-ranged FFI names. Each also checks equality with
the pre-route executable implementation on the same input.
-/

namespace Flapjack.Test.LoopToWordProductionRouteParity

open Flapjack Flapjack.LoopToWord

private def controlBody : LoopProg (BitVec 8) :=
  .seq (.ite .equal 0 (.reg 1)
      (.assign 2 (.var 1)) (.assign 2 (.var 0)) [2])
    (.loop [2] (.assign 2 (.var 2)) [2])

private def handlerBody : LoopProg (BitVec 8) :=
  .call (some ([2], [2])) (some 7) [0, 1]
    (some (4, .assign 2 (.var 1), .assign 2 (.var 0), [2]))

private def memoryBody : LoopProg (BitVec 8) :=
  .seq (.load32 0 1) (.storeByte 0 1)

private def ffiBody : LoopProg (BitVec 8) :=
  .ffi "foo" 0 1 2 3 [0, 1]

private def nonByteFfiBody : LoopProg (BitVec 8) :=
  .ffi "λ" 0 1 2 3 [0, 1]

example : (loopToWordCompFuncViaHOL 3 [0, 1] controlBody).isSome = true := by
  native_decide
example : (loopToWordCompFuncViaHOL 3 [0, 1] handlerBody).isSome = true := by
  native_decide
example : (loopToWordCompFuncViaHOL 3 [0, 1] memoryBody).isSome = true := by
  native_decide
example : (loopToWordCompFuncViaHOL 3 [0, 1] ffiBody).isSome = true := by
  native_decide
example : loopToWordCompFuncViaHOL 3 [0, 1] nonByteFfiBody = none := by
  native_decide

example : reprStr (loopToWordCompFuncRouted 3 [0, 1] controlBody) =
    reprStr (loopToWordCompFunc 3 [0, 1] controlBody) := by native_decide
example : reprStr (loopToWordCompFuncRouted 3 [0, 1] handlerBody) =
    reprStr (loopToWordCompFunc 3 [0, 1] handlerBody) := by native_decide
example : reprStr (loopToWordCompFuncRouted 3 [0, 1] memoryBody) =
    reprStr (loopToWordCompFunc 3 [0, 1] memoryBody) := by native_decide
example : reprStr (loopToWordCompFuncRouted 3 [0, 1] ffiBody) =
    reprStr (loopToWordCompFunc 3 [0, 1] ffiBody) := by native_decide

end Flapjack.Test.LoopToWordProductionRouteParity

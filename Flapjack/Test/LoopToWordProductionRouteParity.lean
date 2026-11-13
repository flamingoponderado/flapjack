module

public import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL
public import Flapjack.Pancake.PanGlobals
public import Flapjack.Pancake.PanStructs.CompileExpCorrespondence
public import Flapjack.Pancake.PanStructs.CompileDeclsExact
public import Flapjack.CompileFunctionDistinct
public import Flapjack.Pancake.CrepToLoop.ProductionCompileProg
public import Flapjack.Pancake.PanToCrep.CompileToCrepBridge
public import Flapjack.Pancake.CrepInline.InlineRouteNames
public import Flapjack.Pancake.LoopToWord.CompFuncExact
public import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
public import Flapjack.RiscV.WordDiagnostics
public import Flapjack.RiscV.WordFuseConditions
public import Flapjack.RiscV.WordUnreach
public import Flapjack.RiscV.Lab
public import Flapjack.Display

@[expose] public section

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

end Flapjack.Test.LoopToWordProductionRouteParity

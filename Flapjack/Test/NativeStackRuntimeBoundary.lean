module

public import Flapjack.Compiler.Backend.StackRemove.ProgComp
public import Flapjack.Compiler.Backend.StackNames.ProgramNames
public import Flapjack.Compiler.Backend.StackToLab.ExecutedInput
public import Flapjack.Compiler.Backend.MlStringBridge
public import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
public import Flapjack.RiscV.Lab

@[expose] public section

/-! Kernel fixtures for the executed native compiler boundary; not HOL theorem ports. -/
namespace Flapjack.Test.NativeStackRuntimeBoundary
open Flapjack Flapjack.Compiler.Backend.StackToLab

end Flapjack.Test.NativeStackRuntimeBoundary

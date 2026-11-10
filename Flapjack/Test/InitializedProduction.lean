module

public import Flapjack.Compiler.Backend.StackNames.ProgramNames
public import Flapjack.Compiler.Backend.StackToLab.ExecutedInput
public import Flapjack.Compiler.Backend.MlStringBridge
public import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
public import Flapjack.RiscV.Lab
public import Flapjack.Compiler.Backend.StackRemove.Compile

@[expose] public section
set_option maxRecDepth 4096
namespace Flapjack.Test.InitializedProduction
open Flapjack Flapjack.Compiler.Backend.StackToLab
end Flapjack.Test.InitializedProduction

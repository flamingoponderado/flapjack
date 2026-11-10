module

public import Flapjack.Compiler.Backend.WordToStack.ProductionMoves

@[expose] public section

namespace Flapjack.Test.ProductionMoves
open Flapjack RiscV Flapjack.ProductionMoves
open Compiler.Backend.StackLang Compiler.Backend.WordToStack.Native

example : wMoveSingleNative (width := 64) (.inr 22, .inr 23) (22, 0, 0) =
    .seq (.stackLoad 22 0) (.stackStore 22 0) := rfl
end Flapjack.Test.ProductionMoves

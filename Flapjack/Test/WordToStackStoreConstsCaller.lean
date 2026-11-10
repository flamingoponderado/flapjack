module

public import Flapjack.Compiler.Backend.WordToStack.ProductionBitmapTransport
public import Flapjack.Compiler.Backend.StackLang.WordPayloads

@[expose] public section

namespace Flapjack.Test.WordToStackStoreConstsCaller
open Flapjack RiscV Compiler.Backend.StackLang

private def constants8 : List (Bool × BitVec 8) := [(true, 255), (false, 1)]

end Flapjack.Test.WordToStackStoreConstsCaller

module

public import Flapjack.RiscV.RuntimeSymbolPreservation

import all Flapjack.RiscV.RuntimeSymbolPreservation

public meta import Flapjack.RiscV.RuntimeSymbolPreservation

@[expose] public section
namespace Flapjack.Test.RuntimeSymbolWiringParity
open Flapjack.RiscV
#guard (initializedRuntimeStubName 0) == (some "_Init")
#guard (initializedRuntimeSymbolName [] 13 0) == ("cml__Init_13")
#guard (initializedRuntimeStubName 1) == (some "_Halt0")
#guard (initializedRuntimeSymbolName [] 13 1) == ("cml__Halt0_13")
#guard (initializedRuntimeStubName 2) == (some "_Halt2")
#guard (initializedRuntimeSymbolName [] 13 2) == ("cml__Halt2_13")
#guard (initializedRuntimeStubName 4) == (some "_GC")
#guard (initializedRuntimeSymbolName [] 13 4) == ("cml__GC_13")
#guard (initializedRuntimeStubName 5) == (some "_Raise")
#guard (initializedRuntimeSymbolName [] 13 5) == ("cml__Raise_13")
#guard (initializedRuntimeStubName 6) == (some "_StoreConsts")
#guard (initializedRuntimeSymbolName [] 13 6) == ("cml__StoreConsts_13")
#guard (initializedRuntimeSymbolName [] 13 3) == ("cml_section_13")
#guard (initializedRuntimeSymbolName [] 13 Flapjack.firstLoopName) == ("cml_generated_main_13")
#guard (initializedRuntimeSymbolName [] 13 100) == ("cml_section_13")
end Flapjack.Test.RuntimeSymbolWiringParity

import Flapjack.RiscV.RuntimeSymbolPreservation
namespace Flapjack.Test.RuntimeSymbolWiringParity
open Flapjack.RiscV
example : initializedRuntimeStubName 0 = some "_Init" := by decide
example : initializedRuntimeSymbolName [] 13 0 = "cml__Init_13" := by decide
example : initializedRuntimeStubName 1 = some "_Halt0" := by decide
example : initializedRuntimeSymbolName [] 13 1 = "cml__Halt0_13" := by decide
example : initializedRuntimeStubName 2 = some "_Halt2" := by decide
example : initializedRuntimeSymbolName [] 13 2 = "cml__Halt2_13" := by decide
example : initializedRuntimeStubName 4 = some "_GC" := by decide
example : initializedRuntimeSymbolName [] 13 4 = "cml__GC_13" := by decide
example : initializedRuntimeStubName 5 = some "_Raise" := by decide
example : initializedRuntimeSymbolName [] 13 5 = "cml__Raise_13" := by decide
example : initializedRuntimeStubName 6 = some "_StoreConsts" := by decide
example : initializedRuntimeSymbolName [] 13 6 = "cml__StoreConsts_13" := by decide
example : initializedRuntimeSymbolName [] 13 3 = "cml_section_13" := by decide
example : initializedRuntimeSymbolName [] 13 Flapjack.firstLoopName = "cml_generated_main_13" := by decide
example : initializedRuntimeSymbolName [] 13 100 = "cml_section_13" := by decide
end Flapjack.Test.RuntimeSymbolWiringParity

module

public import Flapjack.Compiler.Backend.RegAlloc.ProductionFixedTags

import all Flapjack.Compiler.Backend.RegAlloc.ProductionFixedTags

public meta import Flapjack.RiscV.CakeRegAlloc

@[expose] public section
set_option maxRecDepth 100000
namespace Flapjack.Test.RegAllocProductionFixedTags
open RiscV RiscV.CakeRegAlloc

private def mixed : CakeRaState :=
  { CakeRaState.empty 2 with
    nodeTag := (CakeNodeMap.ofList [.fixed 7, .aTemp]).set 9 (.fixed 3)
    degrees := CakeNodeMap.ofList [0, 1]
    coalesced := CakeNodeMap.ofList [0, 1] }

#guard ((cakeAssignAtemps 2 [1,0,9] (fun _ _ _ => none) mixed).nodeTag.get 0) == (some (.fixed 7))
#guard ((cakeAssignAtemps 2 [1,0,9] (fun _ _ _ => none) mixed).nodeTag.get 9) == (some (.fixed 3))
#guard ((cakeAssignStemps 2 (fun _ _ _ => none) mixed).nodeTag.get 0) == (some (.fixed 7))
#guard ((cakeInitAlloc1Heu [(0,(0,1))] 2 mixed).2.nodeTag.get 0) == (some (.fixed 7))
#guard ((cakeRptDoStep none 2 3 mixed).nodeTag.get 9) == (some (.fixed 3))
#guard ((cakeDecDeg 5 mixed).failure) == (some .subscript)
#guard ((cakeDecDeg 5 mixed).nodeTag.get 9) == (some (.fixed 3))
#guard ((cakeDecDeg 1 { mixed with degrees := CakeNodeMap.ofSize 2 }).failure) == (some .missingDegreeSlot)
#guard ((cakeDecDeg 1 { mixed with degrees := CakeNodeMap.ofSize 2 }).nodeTag.get 0) == (some (.fixed 7))

def runChecks : IO Bool := do
  IO.println "PASS production allocator fixed tags across assignment, initialization, IRC and explicit failures (9 kernel fixtures)"
  return true
end Flapjack.Test.RegAllocProductionFixedTags

import Flapjack.Compiler.Backend.RegAlloc.ProductionFixedTags

namespace Flapjack.Test.RegAllocProductionFixedTags
open RiscV RiscV.CakeRegAlloc

private def mixed : CakeRaState :=
  { CakeRaState.empty 2 with
    nodeTag := (CakeNodeMap.ofList [.fixed 7, .aTemp]).set 9 (.fixed 3)
    degrees := CakeNodeMap.ofList [0, 1]
    coalesced := CakeNodeMap.ofList [0, 1] }

example : (cakeAssignAtemps 2 [1,0,9] (fun _ _ _ => none) mixed).nodeTag.get 0 =
    some (.fixed 7) := by cbv
example : (cakeAssignAtemps 2 [1,0,9] (fun _ _ _ => none) mixed).nodeTag.get 9 =
    some (.fixed 3) := by cbv
example : (cakeAssignStemps 2 (fun _ _ _ => none) mixed).nodeTag.get 0 =
    some (.fixed 7) := by cbv
example : (cakeInitAlloc1Heu [(0,(0,1))] 2 mixed).2.nodeTag.get 0 =
    some (.fixed 7) := by cbv
example : (cakeRptDoStep none 2 3 mixed).nodeTag.get 9 =
    some (.fixed 3) := by cbv
example : (cakeDecDeg 5 mixed).failure = some .subscript := by cbv
example : (cakeDecDeg 5 mixed).nodeTag.get 9 = some (.fixed 3) := by cbv
example : (cakeDecDeg 1 { mixed with degrees := CakeNodeMap.ofSize 2 }).failure =
    some .missingDegreeSlot := by cbv
example : (cakeDecDeg 1 { mixed with degrees := CakeNodeMap.ofSize 2 }).nodeTag.get 0 =
    some (.fixed 7) := by cbv

def runChecks : IO Bool := do
  IO.println "PASS production allocator fixed tags across assignment, initialization, IRC and explicit failures (9 kernel fixtures)"
  return true
end Flapjack.Test.RegAllocProductionFixedTags

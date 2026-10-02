import Flapjack.Compiler.Backend.RegAlloc.ProductionColourLookup

namespace Flapjack.Test.RegAllocProductionColourLookup
open RiscV RiscV.CakeRegAlloc

example : cakeSpDefaultIndexed (cakeSpDefaultIndex [(8,3),(8,9)]) 8 = 3 := by rw [spDefaultIndexed_corresponds]; cbv
example : cakeSpDefaultIndexed (cakeSpDefaultIndex []) 8 = 4 := by rw [spDefaultIndexed_corresponds]; cbv
example : cakeSpDefaultIndexed (cakeSpDefaultIndex []) 9 = 0 := by rw [spDefaultIndexed_corresponds]; cbv
example : (cakeMkBij (.delta [8,8] [2,8])).toAllocator = [(8,1),(2,0)] := by cbv
example : (cakeMkBij (.delta [8,8] [2,8])).fromAllocator = [(1,8),(0,2)] := by cbv
example : (cakeMkTags 2 [(1,8),(0,2)] []).get 1 = some (.fixed 4) := by
  rw [mkTags_get _ _ _ _ (by omega), spDefaultIndexed_corresponds]
  cbv
example : (cakeMkTags 2 [(1,8),(0,2)] []).get 0 = some (.fixed 1) := by
  rw [mkTags_get _ _ _ _ (by omega), spDefaultIndexed_corresponds]
  cbv
example : (cakeMkTags 1 [(0,7)] []).get 0 = some .sTemp := by
  rw [mkTags_get _ _ _ _ (by omega), spDefaultIndexed_corresponds]
  cbv
example : (cakeMkTags 1 [(0,5)] []).get 0 = some .aTemp := by
  rw [mkTags_get _ _ _ _ (by omega), spDefaultIndexed_corresponds]
  cbv
example : cakeExtractColor
    { CakeRaState.empty 2 with nodeTag := CakeNodeMap.ofList [.fixed 1, .fixed 4] }
    [(8,1),(2,0)] = [(2,1),(8,4)] := by cbv

def runChecks : IO Bool := do
  IO.println "PASS production allocator index, duplicate ownership, physical tags and sorted extraction (10 kernel fixtures)"
  return true
end Flapjack.Test.RegAllocProductionColourLookup

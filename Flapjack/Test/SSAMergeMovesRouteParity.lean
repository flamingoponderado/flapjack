import Flapjack.Compiler.Backend.WordAlloc.ProductionMergeMoves

namespace Flapjack.Test.SSAMergeMovesRouteParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc
-- Whole original list-decoded outputs from ssa_merge_route_probe.out.
-- Counters31/47 are independent production state metadata, preserved by the route.
private def route (ns : List Nat) (l r : List (Nat × Nat)) (n : Nat) :=
  wordSsaMergeMoves ns {current:=l,next:=31} {current:=r,next:=47} n
private def result (lm rm : List (Nat × Nat)) (n : Nat) (l r : List (Nat × Nat)) :=
  (lm,rm,n,({current:=l,next:=31}:WordSsaState),({current:=r,next:=47}:WordSsaState))
example : route [] [(1,7),(1,99)] [(1,9)] 5 = result [] [] 5 [(1,7)] [(1,9)] := by decide +kernel
example : route [1] [] [(1,9)] 5 = result [] [] 5 [] [(1,9)] := by decide +kernel
example : route [1] [(1,7)] [(1,7)] 5 = result [] [] 5 [(1,7)] [(1,7)] := by decide +kernel
example : route [1] [(1,7)] [(1,9)] 5 = result [(5,7)] [(5,9)] 9 [(1,5)] [(1,5)] := by decide +kernel
example : route [0,2] [(0,7),(2,11)] [(0,9),(2,13)] 5 =
  result [(9,7),(5,11)] [(9,9),(5,13)] 13 [(0,9),(2,5)] [(0,9),(2,5)] := by decide +kernel
example : route [1,1] [(1,7)] [(1,9)] 5 = result [(5,7)] [(5,9)] 9 [(1,5)] [(1,5)] := by decide +kernel
example : route [1] [(1,7),(1,9)] [(1,7),(1,11)] 5 = result [] [] 5 [(1,7)] [(1,7)] := by decide +kernel
example : route [0] [(0,18446744073709551616)] [(0,3)] 18446744073709551616 =
  result [(18446744073709551616,18446744073709551616)] [(18446744073709551616,3)]
    18446744073709551620 [(0,18446744073709551616)] [(0,18446744073709551616)] := by decide +kernel
-- Universal input and output correspondence is checked on arbitrary lists/states.
example (entries : List (Nat × Nat)) (key : Nat) :
    lookupNatInfo key entries = sptAListLookup key entries := productionMergeMapLookup entries key
example (ns : List Nat) (l r : WordSsaState) (n : Nat) := wordSsaMergeMovesCorresponds ns l r n
end Flapjack.Test.SSAMergeMovesRouteParity

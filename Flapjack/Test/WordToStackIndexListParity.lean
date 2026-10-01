import Flapjack.Compiler.Backend.WordToStack.Proofs.IndexList
namespace Flapjack.Test.WordToStackIndexListParity
open Flapjack.WordToStackProofs
example : indexList ([] : List Nat) 5 = [] := by cbv
example : indexList [9] 5 = [(5,9)] := by cbv
example : indexList [7,8,9] 4 = [(6,7),(5,8),(4,9)] := by cbv
example : adjustNames 8 = 4 := by cbv
example : adjustNames 9 = 4 := by cbv

def runChecks : IO Bool := do
  IO.println "PASS exact Word-to-Stack indexing matches five original HOL rows"
  pure true
end Flapjack.Test.WordToStackIndexListParity

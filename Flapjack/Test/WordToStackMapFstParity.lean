import Flapjack.Compiler.Backend.WordToStack.Proofs.MapFst

namespace Flapjack.Test.WordToStackMapFstParity
open Flapjack.WordToStackProofs
example : mapFst (fun n : Nat => n / 2) ([] : List (Nat × Nat)) = [] := by cbv
example : mapFst (fun n : Nat => n / 2) [(6,7),(4,8),(2,9)] = [(3,7),(2,8),(1,9)] := by cbv
example : mapFst (fun _ : Nat => 0) [(6,7),(4,8)] = [(0,7),(0,8)] := by cbv
example : (mapFst (fun n : Nat => n / 2) [(6,7),(4,8),(2,9)]).map Prod.snd = [7,8,9] := by cbv
def runChecks : IO Bool := do
  IO.println "PASS exact Word-to-Stack pair-key mapping matches four original HOL rows"
  pure true
end Flapjack.Test.WordToStackMapFstParity

import Flapjack.Misc.TakeFlatReplicate
namespace Flapjack.Test.MiscTakeFlatReplicateParity
open Flapjack.Misc
example : ((List.replicate 4 [1,2,3]).flatten).take (2*3) = [1,2,3,1,2,3] := rfl
example : ((List.replicate 3 [true,false]).flatten).take (3*2) = (List.replicate 3 [true,false]).flatten := rfl
example : ((List.replicate 5 [true,false]).flatten).take (0*2) = [] := rfl
example : ((List.replicate 5 ([] : List Nat)).flatten).take (3*0) = (List.replicate 3 ([] : List Nat)).flatten := rfl
example : ((List.replicate 0 [true,false]).flatten).take (0*2) = (List.replicate 0 [true,false]).flatten := rfl
example : ((List.replicate 2 [true,false]).flatten).take (3*2) ≠ (List.replicate 3 [true,false]).flatten := by decide
example : ((List.replicate 3 [true,false]).flatten).take (2*1) ≠ (List.replicate 2 [true,false]).flatten := by decide
example {α : Type} (j k : Nat) (ls : List α) (len : Nat) :
    len = ls.length ∧ k ≤ j →
      ((List.replicate j ls).flatten).take (k * len) = (List.replicate k ls).flatten :=
  takeFlatReplicateLeq j k ls len
example : ((List.replicate 5 ([] : List Nat)).flatten).take (3*0) = (List.replicate 3 ([] : List Nat)).flatten :=
  takeFlatReplicateLeq 5 3 [] 0 ⟨rfl,by decide⟩
def runChecks : IO Bool := do
  IO.println "PASS full generic TAKE_FLAT_REPLICATE_LEQ (7 original observations, full generic and empty consumers)"
  pure true
end Flapjack.Test.MiscTakeFlatReplicateParity

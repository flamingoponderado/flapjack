import Flapjack.Compiler.Backend.Parmove.StateToList
namespace Flapjack.Test.ParmoveStateToListParity
open Flapjack.Compiler.Backend.Parmove
example : stateToList (([],[],[]) : List (Nat) × List (Nat) × List (Nat)) = [] := by rfl
example : stateToList (([1,2],[],[]) : List (Nat) × List (Nat) × List (Nat)) = [1,2] := by rfl
example : stateToList (([],[3,4],[]) : List (Nat) × List (Nat) × List (Nat)) = [3,4] := by rfl
example : stateToList (([],[],[5,6]) : List (Nat) × List (Nat) × List (Nat)) = [5,6] := by rfl
example : stateToList (([1,2],[3,4],[5,6]) : List (Nat) × List (Nat) × List (Nat)) = [1,2,3,4,5,6] := by rfl
example : stateToList (([2,2],[2],[2,2]) : List (Nat) × List (Nat) × List (Nat)) = [2,2,2,2,2] := by rfl
example : stateToList (([18446744073709551617],[0],[18446744073709551618]) : List (Nat) × List (Nat) × List (Nat)) = [18446744073709551617,0,18446744073709551618] := by rfl
example : stateToList (([true],[false],[true,false]) : List (Bool) × List (Bool) × List (Bool)) = [true,false,true,false] := by rfl
example : stateToList (([(1,2)],[(3,4)],[(5,6)]) : List (Nat × Nat) × List (Nat × Nat) × List (Nat × Nat)) = [(1,2),(3,4),(5,6)] := by rfl
end Flapjack.Test.ParmoveStateToListParity

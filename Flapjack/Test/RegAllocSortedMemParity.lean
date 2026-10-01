import Flapjack.Compiler.Backend.RegAlloc.SortedMem
import Flapjack.RiscV.CakeRegAlloc

namespace Flapjack.Test.RegAllocSortedMemParity
open Flapjack.RegAlloc
open Flapjack.RiscV.CakeRegAlloc

/-- Kernel regression of the former executed equation on arbitrary inputs. -/
example (x : Nat) (ys : List Nat) : cakeSortedMem x ys =
    match ys with
    | [] => false
    | y :: rest => if x = y then true else if x > y then false else cakeSortedMem x rest := by
  cases ys <;> rfl

example : cakeSortedMem 7 [2,7] = false := rfl
example : cakeSortedMem 2 [7,2,9] = true := rfl

/- Same-input kernel replay of fresh original HOL EVAL rows, including
unsorted lists where early stopping differs from unrestricted membership. -/
example : sortedMem 0 [] = false := by rfl
example : sortedMem 4 [4] = true := by rfl
example : sortedMem 8 [7, 4, 2] = false := by rfl
example : sortedMem 4 [7, 4, 2] = true := by rfl
example : sortedMem 5 [7, 4, 2] = false := by rfl
example : sortedMem 1 [7, 4, 2] = false := by rfl
example : sortedMem 2 [7, 4, 2] = true := by rfl
example : sortedMem 4 [7, 4, 4, 2] = true := by rfl
example : sortedMem 7 [2, 7] = false := by rfl
example : sortedMem 2 [7, 2, 9] = true := by rfl
example : sortedMem 0 [2, 1, 0] = true := by rfl
example : sortedMem 1208925819614629174706176 [1208925819614629174706177, 1208925819614629174706176] = true := by rfl
end Flapjack.Test.RegAllocSortedMemParity

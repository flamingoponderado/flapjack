import Flapjack.RiscV.CakeRegAlloc

namespace Flapjack.Test.RegAllocSortMovesRouteParity
open Flapjack.RiscV.CakeRegAlloc

-- Production specializes the reviewed generic payload to a register pair.
example (moves : List (Nat × (Nat × Nat))) :
    cakeSortMoves moves = Flapjack.RegAlloc.sortMoves moves := rfl
example (xs ys : List (Nat × (Nat × Nat))) :
    cakeSMerge xs ys = Flapjack.RegAlloc.smerge xs ys := rfl
example (moves : List (Nat × (Nat × Nat))) :
    cakeSortMoves moves = cakeSort (fun a b => a.1 > b.1) moves :=
  cakeSortMoves_eq_legacy moves

example : cakeSortMoves [] = [] := by decide +kernel
example : cakeSortMoves [(3,(7,8))] = [(3,(7,8))] := by decide +kernel
example : cakeSortMoves [(3,(1,0)),(3,(2,0)),(3,(3,0)),(3,(4,0)),(3,(5,0))] =
    [(3,(5,0)),(3,(4,0)),(3,(3,0)),(3,(2,0)),(3,(1,0))] := by decide +kernel
example : cakeSortMoves [(1,(9,0)),(4,(2,0)),(2,(8,0)),(0,(5,0))] =
    [(4,(2,0)),(2,(8,0)),(1,(9,0)),(0,(5,0))] := by decide +kernel
example : cakeSMerge [] [] = [] := by decide +kernel
example : cakeSMerge [(2,(7,0)),(1,(8,0))] [] = [(2,(7,0)),(1,(8,0))] :=
  by decide +kernel
example : cakeSMerge [] [(2,(7,0)),(1,(8,0))] = [(2,(7,0)),(1,(8,0))] :=
  by decide +kernel
example : cakeSMerge [(3,(1,0)),(3,(2,0)),(1,(8,0))] [(3,(4,0)),(2,(5,0)),(1,(9,0))] =
    [(3,(1,0)),(3,(2,0)),(3,(4,0)),(2,(5,0)),(1,(8,0)),(1,(9,0))] := by decide +kernel
example : cakeSMerge [(1,(2,0)),(9,(3,0))] [(2,(4,0)),(0,(5,0))] =
    [(2,(4,0)),(1,(2,0)),(9,(3,0)),(0,(5,0))] := by decide +kernel
example : cakeSMerge [(4,(7,0)),(4,(7,0))] [(4,(7,0))] =
    [(4,(7,0)),(4,(7,0)),(4,(7,0))] := by decide +kernel

#print axioms cakeSortMoves_eq_legacy
#print axioms cakeSMerge_eq_legacy
end Flapjack.Test.RegAllocSortMovesRouteParity

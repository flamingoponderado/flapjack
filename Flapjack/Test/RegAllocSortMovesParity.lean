import Flapjack.Compiler.Backend.RegAlloc.SortMoves

namespace Flapjack.Test.RegAllocSortMovesParity
open Flapjack.RegAlloc

example : sortMoves ([] : List (Nat × Nat)) = [] := by decide +kernel
example : sortMoves [(3,7)] = [(3,7)] := by decide +kernel
example : smerge ([] : List (Nat × Nat)) [] = [] := by decide +kernel
example : smerge [(2,7),(1,8)] [] = [(2,7),(1,8)] := by decide +kernel
example : smerge [] [(2,7),(1,8)] = [(2,7),(1,8)] := by decide +kernel

-- Fresh original reg_alloc observations; equal-priority sort reverses this
-- five-element input, whereas smerge preserves left bias at equal heads.
example : sortMoves [(3,1),(3,2),(3,3),(3,4),(3,5)] =
    [(3,5),(3,4),(3,3),(3,2),(3,1)] := by decide +kernel
example : sortMoves [(1,9),(4,2),(2,8),(0,5)] =
    [(4,2),(2,8),(1,9),(0,5)] := by decide +kernel
example : sortMoves [(1,true),(3,false),(2,true)] =
    [(3,false),(2,true),(1,true)] := by decide +kernel
example : smerge [(3,1),(3,2),(1,8)] [(3,4),(2,5),(1,9)] =
    [(3,1),(3,2),(3,4),(2,5),(1,8),(1,9)] := by decide +kernel
example : smerge [(1,2),(9,3)] [(2,4),(0,5)] =
    [(2,4),(1,2),(9,3),(0,5)] := by decide +kernel
example : smerge [(4,7),(4,7)] [(4,7)] =
    [(4,7),(4,7),(4,7)] := by decide +kernel
example : smerge [(3,true),(1,false)] [(3,false),(2,true)] =
    [(3,true),(3,false),(2,true),(1,false)] := by decide +kernel
example {α : Type} (x : Nat × α) (xs ys : List (Nat × α)) :
    x ∈ smerge xs ys ↔ x ∈ xs ∨ x ∈ ys := memSmerge x xs ys

#print axioms sortMoves
#print axioms smerge
#print axioms memSmerge
end Flapjack.Test.RegAllocSortMovesParity

import Flapjack.Compiler.Backend.WordAlloc.CanonizeMoves

namespace Flapjack.Test.CanonizeMovesParity
open Flapjack.WordAlloc
/-! Fresh original complete canonize_moves observations. Kernel replay covers
normalization, sorting, group counts, maximum priorities, reverse group order,
self moves and unbounded natural numbers. Finite observations do not establish
cross-assistant equivalence or executed allocator routing. -/
-- cm_empty=T
example : canonizeMoves [] = [] := by decide +kernel
-- cm_one=T
example : canonizeMoves [(3,(7,2))] = [(1,3,(2,7))] := by decide +kernel
-- cm_two=T
example : canonizeMoves [(2,(3,4)),(1,(1,2))] = [(1,2,(3,4)),(1,1,(1,2))] := by decide +kernel
-- cm_three=T
example : canonizeMoves [(9,(1,2)),(3,(1,1)),(2,(1,2))] = [(2,9,(1,2)),(1,3,(1,1))] := by decide +kernel
-- cm_four=T
example : canonizeMoves [(5,(2,1)),(2,(1,5)),(9,(1,2)),(3,(1,2))] = [(1,2,(1,5)),(3,9,(1,2))] := by decide +kernel
-- cm_five=T
example : canonizeMoves [(7,(3,2)),(1,(1,2)),(4,(2,3)),(5,(1,2)),(2,(2,1))] = [(2,7,(2,3)),(3,5,(1,2))] := by decide +kernel
-- cm_odd=T
example : canonizeMoves [(9,(3,5)),(8,(2,4)),(7,(1,3)),(6,(3,2)),(5,(2,1)),(4,(1,2)),(3,(1,1))] = [(1,9,(3,5)),(1,8,(2,4)),(1,6,(2,3)),(1,7,(1,3)),(2,5,(1,2)),(1,3,(1,1))] := by decide +kernel
-- cm_even=T
example : canonizeMoves [(3,(2,1)),(2,(1,2)),(1,(1,1)),(9,(1,1)),(8,(2,1)),(7,(3,4)),(6,(3,3)),(5,(1,3))] = [(1,7,(3,4)),(1,6,(3,3)),(1,5,(1,3)),(3,8,(1,2)),(2,9,(1,1))] := by decide +kernel
-- cm_dups=T
example : canonizeMoves [(2,(1,3)),(2,(1,3)),(1,(1,3)),(2,(1,3))] = [(4,2,(1,3))] := by decide +kernel
-- cm_priority=T
example : canonizeMoves [(9,(1,2)),(1,(1,2)),(7,(1,2)),(0,(1,2)),(9,(1,2))] = [(5,9,(1,2))] := by decide +kernel
-- cm_x_first=T
example : canonizeMoves [(0,(9,0)),(99,(1,99)),(0,(2,0))] = [(1,99,(1,99)),(1,0,(0,9)),(1,0,(0,2))] := by decide +kernel
-- cm_y_second=T
example : canonizeMoves [(0,(1,9)),(99,(1,1)),(0,(1,2))] = [(1,0,(1,9)),(1,0,(1,2)),(1,99,(1,1))] := by decide +kernel
-- cm_reversed_coords=T
example : canonizeMoves [(1,(9,2)),(3,(2,9)),(2,(9,2)),(0,(2,9))] = [(4,3,(2,9))] := by decide +kernel
-- cm_large=T
example : canonizeMoves [(18446744073709551616,(1,2)),(0,(18446744073709551616,2)),(1,(1,2))] = [(1,0,(2,18446744073709551616)),(2,18446744073709551616,(1,2))] := by decide +kernel
-- cm_zeros=T
example : canonizeMoves [(0,(0,0)),(1,(0,0)),(0,(1,0)),(0,(0,1)),(0,(0,0))] = [(2,0,(0,1)),(3,1,(0,0))] := by decide +kernel
-- cm_descending=T
example : canonizeMoves [(0,(12,13)),(1,(11,12)),(2,(10,11)),(3,(9,10)),(4,(8,9)),(5,(7,8)),(6,(6,7)),(7,(5,6)),(8,(4,5)),(9,(3,4)),(10,(2,3)),(11,(1,2))] = [(1,0,(12,13)),(1,1,(11,12)),(1,2,(10,11)),(1,3,(9,10)),(1,4,(8,9)),(1,5,(7,8)),(1,6,(6,7)),(1,7,(5,6)),(1,8,(4,5)),(1,9,(3,4)),(1,10,(2,3)),(1,11,(1,2))] := by decide +kernel
-- cm_ascending=T
example : canonizeMoves [(0,(0,1)),(1,(1,2)),(2,(2,3)),(3,(3,4)),(4,(4,5)),(5,(5,6)),(6,(6,7)),(7,(7,8)),(8,(8,9)),(9,(9,10)),(10,(10,11)),(11,(11,12))] = [(1,11,(11,12)),(1,10,(10,11)),(1,9,(9,10)),(1,8,(8,9)),(1,7,(7,8)),(1,6,(6,7)),(1,5,(5,6)),(1,4,(4,5)),(1,3,(3,4)),(1,2,(2,3)),(1,1,(1,2)),(1,0,(0,1))] := by decide +kernel
-- cm_self_moves=T
example : canonizeMoves [(0,(4,4)),(7,(4,4)),(9,(3,3))] = [(2,7,(4,4)),(1,9,(3,3))] := by decide +kernel
-- cm_all_flipped=T
example : canonizeMoves [(2,(9,1)),(3,(9,1)),(1,(9,1))] = [(3,3,(1,9))] := by decide +kernel

end Flapjack.Test.CanonizeMovesParity

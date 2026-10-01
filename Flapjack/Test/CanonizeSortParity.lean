import Flapjack.Compiler.Backend.WordAlloc.CanonizeSort

namespace Flapjack.Test.CanonizeSortParity
open Flapjack Flapjack.WordAlloc
/-! Fresh original observations on the literal inline move comparator and
existing native mllist merge-sort. No normalization is performed in this
prerequisite. Finite observations do not establish general cross-prover
equivalence or completion of canonize_moves/production allocator routing. -/
-- cs_empty=T
example : sortCanonizeMoves [] = [] := by decide +kernel
-- cs_one=T
example : sortCanonizeMoves [(3,(7,2))] = [(3,(7,2))] := by decide +kernel
-- cs_two=T
example : sortCanonizeMoves [(2,(3,4)),(1,(1,2))] = [(1,(1,2)),(2,(3,4))] := by decide +kernel
-- cs_three=T
example : sortCanonizeMoves [(9,(1,2)),(3,(1,1)),(2,(1,2))] = [(3,(1,1)),(2,(1,2)),(9,(1,2))] := by decide +kernel
-- cs_four=T
example : sortCanonizeMoves [(5,(2,1)),(2,(1,5)),(9,(1,2)),(3,(1,2))] = [(3,(1,2)),(9,(1,2)),(2,(1,5)),(5,(2,1))] := by decide +kernel
-- cs_five=T
example : sortCanonizeMoves [(7,(3,2)),(1,(1,2)),(4,(2,3)),(5,(1,2)),(2,(2,1))] = [(1,(1,2)),(5,(1,2)),(2,(2,1)),(4,(2,3)),(7,(3,2))] := by decide +kernel
-- cs_odd=T
example : sortCanonizeMoves [(9,(3,5)),(8,(2,4)),(7,(1,3)),(6,(3,2)),(5,(2,1)),(4,(1,2)),(3,(1,1))] = [(3,(1,1)),(4,(1,2)),(7,(1,3)),(5,(2,1)),(8,(2,4)),(6,(3,2)),(9,(3,5))] := by decide +kernel
-- cs_even=T
example : sortCanonizeMoves [(3,(2,1)),(2,(1,2)),(1,(1,1)),(9,(1,1)),(8,(2,1)),(7,(3,4)),(6,(3,3)),(5,(1,3))] = [(1,(1,1)),(9,(1,1)),(2,(1,2)),(5,(1,3)),(3,(2,1)),(8,(2,1)),(6,(3,3)),(7,(3,4))] := by decide +kernel
-- cs_dups=T
example : sortCanonizeMoves [(2,(1,3)),(2,(1,3)),(1,(1,3)),(2,(1,3))] = [(1,(1,3)),(2,(1,3)),(2,(1,3)),(2,(1,3))] := by decide +kernel
-- cs_priority=T
example : sortCanonizeMoves [(9,(1,2)),(1,(1,2)),(7,(1,2)),(0,(1,2)),(9,(1,2))] = [(0,(1,2)),(1,(1,2)),(7,(1,2)),(9,(1,2)),(9,(1,2))] := by decide +kernel
-- cs_x_first=T
example : sortCanonizeMoves [(0,(9,0)),(99,(1,99)),(0,(2,0))] = [(99,(1,99)),(0,(2,0)),(0,(9,0))] := by decide +kernel
-- cs_y_second=T
example : sortCanonizeMoves [(0,(1,9)),(99,(1,1)),(0,(1,2))] = [(99,(1,1)),(0,(1,2)),(0,(1,9))] := by decide +kernel
-- cs_reversed_coords=T
example : sortCanonizeMoves [(1,(9,2)),(3,(2,9)),(2,(9,2)),(0,(2,9))] = [(0,(2,9)),(3,(2,9)),(1,(9,2)),(2,(9,2))] := by decide +kernel
-- cs_large=T
example : sortCanonizeMoves [(18446744073709551616,(1,2)),(0,(18446744073709551616,2)),(1,(1,2))] = [(1,(1,2)),(18446744073709551616,(1,2)),(0,(18446744073709551616,2))] := by decide +kernel
-- cs_zeros=T
example : sortCanonizeMoves [(0,(0,0)),(1,(0,0)),(0,(1,0)),(0,(0,1)),(0,(0,0))] = [(0,(0,0)),(0,(0,0)),(1,(0,0)),(0,(0,1)),(0,(1,0))] := by decide +kernel
-- cs_descending=T
example : sortCanonizeMoves [(0,(12,13)),(1,(11,12)),(2,(10,11)),(3,(9,10)),(4,(8,9)),(5,(7,8)),(6,(6,7)),(7,(5,6)),(8,(4,5)),(9,(3,4)),(10,(2,3)),(11,(1,2))] = [(11,(1,2)),(10,(2,3)),(9,(3,4)),(8,(4,5)),(7,(5,6)),(6,(6,7)),(5,(7,8)),(4,(8,9)),(3,(9,10)),(2,(10,11)),(1,(11,12)),(0,(12,13))] := by decide +kernel
-- cs_ascending=T
example : sortCanonizeMoves [(0,(0,1)),(1,(1,2)),(2,(2,3)),(3,(3,4)),(4,(4,5)),(5,(5,6)),(6,(6,7)),(7,(7,8)),(8,(8,9)),(9,(9,10)),(10,(10,11)),(11,(11,12))] = [(0,(0,1)),(1,(1,2)),(2,(2,3)),(3,(3,4)),(4,(4,5)),(5,(5,6)),(6,(6,7)),(7,(7,8)),(8,(8,9)),(9,(9,10)),(10,(10,11)),(11,(11,12))] := by decide +kernel

end Flapjack.Test.CanonizeSortParity

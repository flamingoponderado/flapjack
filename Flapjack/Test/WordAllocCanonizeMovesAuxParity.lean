import Flapjack.Compiler.Backend.WordAlloc.CanonizeMovesAux
namespace Flapjack.Test.WordAllocCanonizeMovesAuxParity
open Flapjack.WordAlloc
-- cma_empty=T
example : canonizeMovesAux 7 (2,3) 0 [] [] = [(0,7,(2,3))] := by decide
-- cma_acc=T
example : canonizeMovesAux 7 (2,3) 9 [] [(8,6,(4,5))] = [(9,7,(2,3)),(8,6,(4,5))] := by decide
-- cma_same_up=T
example : canonizeMovesAux 2 (1,3) 1 [(9,(1,3))] [] = [(2,9,(1,3))] := by decide
-- cma_same_down=T
example : canonizeMovesAux 9 (1,3) 4 [(2,(1,3))] [] = [(5,9,(1,3))] := by decide
-- cma_same_equal=T
example : canonizeMovesAux 9 (1,3) 0 [(9,(1,3))] [] = [(1,9,(1,3))] := by decide
-- cma_different=T
example : canonizeMovesAux 7 (1,3) 4 [(2,(4,5))] [] = [(1,2,(4,5)),(4,7,(1,3))] := by decide
-- cma_groups=T
example : canonizeMovesAux 2 (1,3) 1 [(7,(1,3)),(4,(5,6)),(9,(5,6))] [(8,6,(4,5))] = [(2,9,(5,6)),(2,7,(1,3)),(8,6,(4,5))] := by decide
-- cma_unsorted=T
example : canonizeMovesAux 2 (1,3) 1 [(7,(4,5)),(4,(1,3))] [] = [(1,4,(1,3)),(1,7,(4,5)),(1,2,(1,3))] := by decide
-- cma_reversed=T
example : canonizeMovesAux 2 (1,3) 1 [(7,(3,1))] [] = [(1,7,(3,1)),(1,2,(1,3))] := by decide
-- cma_self=T
example : canonizeMovesAux 0 (3,3) 0 [(0,(3,3))] [] = [(1,0,(3,3))] := by decide
-- cma_large=T
example : canonizeMovesAux 18446744073709551616 (18446744073709551617,3) 18446744073709551616 [(2,(18446744073709551617,3))] [] = [(18446744073709551617,18446744073709551616,(18446744073709551617,3))] := by decide
-- cma_bool=T
example : canonizeMovesAux 2 true 4 [(7,true),(3,false)] [] = [(1,3,false),(5,7,true)] := by decide
end Flapjack.Test.WordAllocCanonizeMovesAuxParity

import Flapjack.Compiler.Backend.WordAlloc.CanonizeMoves
namespace Flapjack.Test.WordAllocCanonizeMovesParity
open Flapjack.WordAlloc
example : canonizeMoves [] = [] := by decide +kernel
example : canonizeMoves [(3,1,2)] = [(1,3,1,2)] := by decide +kernel
example : canonizeMoves [(3,9,2)] = [(1,3,2,9)] := by decide +kernel
example : canonizeMoves [(4,5,5)] = [(1,4,5,5)] := by decide +kernel
example : canonizeMoves [(2,1,2),(8,2,1),(3,1,2)] = [(3,8,1,2)] := by decide +kernel
example : canonizeMoves [(99,4,5),(1,1,2),(50,3,4)] = [(1,99,4,5),(1,50,3,4),(1,1,1,2)] := by decide +kernel
example : canonizeMoves [(1,1,9),(7,1,3),(2,1,6)] = [(1,1,1,9),(1,2,1,6),(1,7,1,3)] := by decide +kernel
example : canonizeMoves [(4,2,3),(4,3,2),(4,2,3)] = [(3,4,2,3)] := by decide +kernel
example : canonizeMoves [(1,9,2),(8,1,4),(7,2,9),(3,4,1),(2,2,9)] = [(3,7,2,9),(2,8,1,4)] := by decide +kernel
example : canonizeMoves [(0,1,2),(1,1,2),(2,1,2),(3,1,2),(4,1,2),(5,1,2),(6,1,2)] = [(7,6,1,2)] := by decide +kernel
example : canonizeMoves [(18446744073709551617,18446744073709551619,18446744073709551618),(18446744073709551620,18446744073709551618,18446744073709551619)] = [(2,18446744073709551620,18446744073709551618,18446744073709551619)] := by decide +kernel
example : canonizeMoves [(0,0,0),(1,2,0),(0,0,2),(3,0,0)] = [(2,1,0,2),(2,3,0,0)] := by decide +kernel
end Flapjack.Test.WordAllocCanonizeMovesParity

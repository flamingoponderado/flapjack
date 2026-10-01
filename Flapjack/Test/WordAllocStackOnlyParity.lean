import Flapjack.Compiler.Backend.WordAlloc.GetStackOnly
namespace Flapjack.Test.WordAllocStackOnlyParity
open Flapjack Flapjack.WordAlloc
abbrev P := WordLangProgHOL (BitVec 64)
private def m1 : P := .move 0 [(3,1)]
private def m2 : P := .move 0 [(1,5)]
example : getStackOnlyAux (.ls (),.bn .ln .ln) (.skip : P) = (.ls (),.bn .ln .ln) := by simp [getStackOnlyAux, getClashTree, removeTempStack]
example : getStackOnlyAux (.ln,.ln) m1 = (sptInsert 1 () .ln,.ln) := by simp [m1,getStackOnlyAux,mergeStackOnly,isStackVar,isAllocVar]
example : getStackOnlyAux (.ln,.ln) (.move 0 [(1,5),(3,1)] : P) = (sptInsert 5 () (sptInsert 1 () .ln),sptInsert 1 () .ln) := by simp [getStackOnlyAux,mergeStackOnly,sptLookup,sptInsert,isStackVar,isAllocVar,isPhyVar]
example : getStackOnlyAux (.ln,.ln) (.seq m2 m1) = (sptInsert 5 () (sptInsert 1 () .ln),sptInsert 1 () .ln) := by simp [m1,m2,getStackOnlyAux,mergeStackOnly,sptLookup,sptInsert,isStackVar,isAllocVar,isPhyVar]
example : getStackOnlyAux (.ln,.ln) (.mustTerminate m1) = (sptInsert 1 () .ln,.ln) := by simp [m1,getStackOnlyAux,mergeStackOnly,isStackVar,isAllocVar]
example : getStackOnlyAux (.ln,.ln) (.loop .ln m1 .ln) = (sptInsert 1 () .ln,.ln) := by simp [m1,getStackOnlyAux,mergeStackOnly,isStackVar,isAllocVar]
example : getStackOnlyAux (.ls (),.bn .ln .ln) (.call none none [] (some (0,m1,0,0))) = (.ls (),.bn .ln .ln) := by simp [getStackOnlyAux]
example : getStackOnlyAux (.ln,.ln) (.call (some ([],(.ln,.ln),m1,0,0)) none [] none) = (sptInsert 1 () .ln,.ln) := by simp [m1,getStackOnlyAux,mergeStackOnly,isStackVar,isAllocVar]
example : getStackOnlyAux (.ls (),.bn .ln .ln) (.tick : P) = (.ls (),.bn .ln .ln) := by simp [getStackOnlyAux,getClashTree,removeTempStack]
example : getStackOnlyAux (.ls (),.bn .ln .ln) (.return 0 [] : P) = (.ln,.bn .ln .ln) := by simp [getStackOnlyAux,getClashTree,removeTempStack,sptDelete]
example : getStackOnlyAux (.ls (),.bn .ln .ln) (.alloc 0 (.ln,.ln) : P) = (.ls (),.bn .ln .ln) := by simp [getStackOnlyAux,getClashTree]
example : getStackOnly (.seq m2 m1) = sptInsert 1 () .ln := by simp [getStackOnly,m1,m2,getStackOnlyAux,mergeStackOnly,sptLookup,sptInsert,isStackVar,isAllocVar,isPhyVar]
example : getStackOnlyAux (.ln,.ln) (.ite .equal 1 (.reg 1) m1 m1) = (.ln,.ln) := by simp [m1,getStackOnlyAux,mergeStackOnly,isStackVar,isAllocVar,mergeStackSets,removeTempStack,sptInsert,sptInter,sptDifference,sptUnion,sptDelete,sptMkBN]
example : getStackOnlyAux (.ln,.ln) (.ite .equal 0 (.imm 0) m1 m1) = (sptInsert 1 () .ln,.ln) := by simp [m1,getStackOnlyAux,mergeStackOnly,isStackVar,isAllocVar,mergeStackSets,removeTempStack,sptInsert,sptInter,sptDifference,sptUnion,sptDelete]
example : getStackOnlyAux (.ln,.ln) (.call (some ([],(.ln,.ln),m1,0,0)) none [] (some (0,m1,0,0))) = (sptInsert 1 () .ln,.ln) := by simp [m1,getStackOnlyAux,mergeStackOnly,isStackVar,isAllocVar,mergeStackSets,sptInsert,sptInter,sptDifference,sptUnion]
end Flapjack.Test.WordAllocStackOnlyParity

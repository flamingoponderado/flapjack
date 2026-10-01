import Flapjack.Pancake.LoopToWord.Proofs.ProgramNames

namespace Flapjack.Test.LoopToWordProgramNamesParity
open Flapjack Flapjack.LoopToWord

def duplicateRows {width : Nat} [NeZero width] : List (Nat × List Nat × HolLoopProg width) :=
  [(7, [1], .skip), (7, [], .tick)]
def distinctRows {width : Nat} [NeZero width] : List (Nat × List Nat × HolLoopProg width) :=
  [(7, [1], .skip), (8, [], .tick)]

example {width : Nat} [NeZero width] :
    loopToWordCompileProgHOL (duplicateRows : List (Nat × List Nat × HolLoopProg width)) =
      [(7, 2, .skip), (7, 1, .tick)] := by
  simp [duplicateRows, loopToWordCompileProgHOL, loopToWordCompFuncHOL, LoopToWord.compHOL]
example {width : Nat} [NeZero width] :
    loopToWordCompileProgHOL (distinctRows : List (Nat × List Nat × HolLoopProg width)) =
      [(7, 2, .skip), (8, 1, .tick)] := by
  simp [distinctRows, loopToWordCompileProgHOL, loopToWordCompFuncHOL, LoopToWord.compHOL]
example {width : Nat} [NeZero width] :
    ((loopToWordCompileProgHOL (distinctRows : List (Nat × List Nat × HolLoopProg width))).map Prod.fst).Nodup := by
  apply loopToWordFirstCompileProgAllDistinct
  simp [distinctRows]
example {width : Nat} [NeZero width] :
    ((loopToWordCompileHOL (distinctRows : List (Nat × List Nat × HolLoopProg width))).map Prod.fst).Nodup := by
  apply loopToWordFirstCompileAllDistinct
  simp [distinctRows]
example : ¬ ((loopToWordCompileProgHOL (duplicateRows : List (Nat × List Nat × HolLoopProg 64))).map Prod.fst).Nodup := by
  simp [duplicateRows, loopToWordCompileProgHOL]
example {width : Nat} [NeZero width] :
    (7, 2, loopToWordCompFuncHOL 7 [1] (.skip : HolLoopProg width)) ∈
      loopToWordCompileProgHOL duplicateRows := by
  simpa using loopToWordMemProgMemCompileProg duplicateRows 7 [1] (.skip : HolLoopProg width)
    (by simp [duplicateRows])
example {width : Nat} [NeZero width] :
    sptLookup 7 (sptFromAList (loopToWordCompileProgHOL
      (duplicateRows : List (Nat × List Nat × HolLoopProg width)))) = some (2, .skip) := by
  have h := loopToWordLookupProgSomeLookupCompileProg duplicateRows 7 [1] (.skip : HolLoopProg width)
    (by simp [duplicateRows, sptLookup_sptFromAList, sptAListLookup])
  simpa [loopToWordCompFuncHOL, LoopToWord.compHOL] using h
example {width : Nat} [NeZero width] :
    sptLookup 9 (sptFromAList (loopToWordCompileProgHOL
      (duplicateRows : List (Nat × List Nat × HolLoopProg width)))) = none := by
  simp [duplicateRows, loopToWordCompileProgHOL, sptLookup_sptFromAList, sptAListLookup]

end Flapjack.Test.LoopToWordProgramNamesParity

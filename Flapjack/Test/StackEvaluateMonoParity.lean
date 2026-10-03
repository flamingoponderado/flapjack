import Flapjack.Compiler.Backend.StackProps.EvaluateMono

namespace Flapjack.Test.StackEvaluateMonoParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps.EvaluateMono

example {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (program, source) = (result, post)) :
    source.bitmaps.IsPrefix post.bitmaps ∧ sptSubspt source.code post.code :=
  evaluateMono program source post result execution

example {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source post : StackSemStateFiniteExact width C F)
    (execution : StackSemEvaluate.evaluate (program, source) = (none, post)) :
    source.bitmaps.IsPrefix post.bitmaps ∧ sptSubspt source.code post.code :=
  evaluateMono program source post _ execution

example {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source post : StackSemStateFiniteExact width C F)
    (execution : StackSemEvaluate.evaluate (program, source) = (some .error, post)) :
    source.bitmaps.IsPrefix post.bitmaps ∧ sptSubspt source.code post.code :=
  evaluateMono program source post _ execution

example {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source post : StackSemStateFiniteExact width C F)
    (execution : StackSemEvaluate.evaluate (program, source) = (some .timeOut, post)) :
    source.bitmaps.IsPrefix post.bitmaps ∧ sptSubspt source.code post.code :=
  evaluateMono program source post _ execution

-- Native lookup consequence of the full theorem: the original code entry
-- survives arbitrary execution, including unsuccessful results.
example {width : Nat} [NeZero width] {C F : Type}
    (program entry : HolProg width) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (key : Nat)
    (execution : StackSemEvaluate.evaluate (program, source) = (result, post))
    (lookup : sptLookup key source.code = some entry) :
    sptLookup key post.code = some entry :=
  (sptSubsptLookup source.code post.code).mp
    (evaluateMono program source post result execution).2 key entry lookup

private def observedUnion : Spt Nat :=
  sptUnion (sptFromAList [(0,11)]) (sptFromAList [(0,22),(1,33)])

-- Values below come from the fresh original HOL observations.
example : sptLookup 0 observedUnion = some 11 := by cbv
example : sptLookup 1 observedUnion = some 33 := by cbv
example : ([255,0] : List (BitVec 8)).IsPrefix [255,0,1] := by decide
example : ¬([255,0] : List (BitVec 8)).IsPrefix [255] := by decide

def runChecks : IO Bool := do
  let ok := (sptLookup 0 observedUnion == some 11) &&
    (sptLookup 1 observedUnion == some 33) &&
    decide (([255,0] : List (BitVec 8)).IsPrefix [255,0,1]) &&
    !decide (([255,0] : List (BitVec 8)).IsPrefix [255])
  IO.println (if ok then "PASS original evaluator monotonicity observations (4) and generic consumers (5)" else "FAIL evaluator monotonicity")
  pure ok

end Flapjack.Test.StackEvaluateMonoParity

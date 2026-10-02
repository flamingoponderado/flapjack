import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapFrameUpdates

namespace Flapjack.Test.WordToStackBitmapFrameUpdatesParity
open Flapjack.Compiler.Backend.WordToStack

/-- The 63 corresponding original HOL EVAL rows all return true. They cover
empty/truncated/location-valued stacks, terminal/continuation chunks, and
positive widths 8, 64 and 80. The generic port has no such fixture restriction. -/
private def observations (width : Nat) [NeZero width] : Bool :=
  ([0,6,7,8,63,64,80] : List Nat).all fun frame =>
    ([[], [.word 0], [.loc 17 19, .word 0, .loc 3 4]] :
      List (List (WordLocW width))).all fun xs =>
      decide (listUpdate
        ((writeBitmapExact (sptFromAList [(2,()),(4,())]) 1 frame).map WordLocW.word)
        0 xs ≠ [WordLocW.word (0 : BitVec width)])

#guard observations 8
#guard observations 64
#guard observations 80

example {width : Nat} [NeZero width] {α : Type} (names : Spt α)
    (k frame : Nat) (xs : List (WordLocW width)) (h : 8 ≤ width) :=
  listUpdateWriteBitmapNotNil names k frame xs h

example {α : Type} (n1 n2 n3 : Nat) (xs : List α)
    (h : n1 + n2 + n3 ≤ xs.length) := appendFrameLemma n1 n2 n3 xs h

example {α : Type} (ys xs : List α) (n : Nat) :=
  dropListUpdateSameOffset ys n xs

def run : IO Bool := do
  let ok := observations 8 && observations 64 && observations 80
  IO.println (if ok then "PASS original bitmap frame overwrite (63 observations)"
    else "FAIL original bitmap frame overwrite")
  pure ok

end Flapjack.Test.WordToStackBitmapFrameUpdatesParity

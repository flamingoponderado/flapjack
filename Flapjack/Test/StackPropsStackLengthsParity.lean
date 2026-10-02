import Flapjack.Compiler.Backend.StackProps.StackLengths

namespace Flapjack.Test.StackPropsStackLengthsParity
open Flapjack StackSem StackPropsStackLengths

private theorem map_empty : mapBitmap [] [10] [20,30] = some ([], [10], [20,30]) := by decide +kernel

private theorem map_mixed : mapBitmap [true,false,true] [10,11,12] [20,21,22,23] = some ([10,21,11],[12],[23]) := by decide +kernel

private theorem map_false : mapBitmap [false,false] ([] : List Nat) [20,21,22] = some ([20,21],[],[22]) := by decide +kernel

private theorem map_payload_lists : mapBitmap [true,false] [[114],[117]] [[97],[98],[116]] = some ([[114],[98]],[[117]],[[116]]) := by decide +kernel

private theorem map_missing_root : mapBitmap [true] ([] : List Nat) [20] = none := by decide +kernel

private theorem map_missing_value : mapBitmap [false] [10] [] = none := by decide +kernel

private theorem dec_empty : decStack ([] : List (BitVec 8)) []
    ([] : List (WordLocW 8)) = none := by decide +kernel

private theorem dec_zero : decStack ([] : List (BitVec 8)) []
    ([.word 0] : List (WordLocW 8)) = some [.word 0] := by decide +kernel

private theorem dec_true : decStack ([3] : List (BitVec 8)) [.word 9]
    ([.word 1,.word 7,.word 0] : List (WordLocW 64)) = some [.word 1,.word 9,.word 0] := by decide +kernel

private theorem dec_false : decStack ([2] : List (BitVec 8)) []
    ([.word 1,.loc 4 5,.word 0] : List (WordLocW 64)) = some [.word 1,.loc 4 5,.word 0] := by decide +kernel

private theorem dec_short_roots : decStack ([3] : List (BitVec 8)) []
    ([.word 1,.word 7,.word 0] : List (WordLocW 64)) = none := by decide +kernel

private theorem dec_extra_roots : decStack ([3] : List (BitVec 8)) [.word 9,.word 10]
    ([.word 1,.word 7,.word 0] : List (WordLocW 64)) = none := by decide +kernel

private theorem dec_two : decStack ([3] : List (BitVec 8)) [.word 9,.loc 2 1]
    ([.word 1,.word 7,.word 1,.loc 4 0,.word 0] : List (WordLocW 80)) = some [.word 1,.word 9,.word 1,.loc 2 1,.word 0] := by decide +kernel

private theorem dec_zero_extra : decStack ([] : List (BitVec 8)) []
    ([.word 0,.word 1] : List (WordLocW 8)) = none := by decide +kernel

private theorem dec_mixed : decStack ([3] : List (BitVec 8)) [.word 0]
    ([.word 1,.word 1,.word 0] : List (WordLocW 1)) = some [.word 1,.word 0,.word 0] := by decide +kernel

private theorem dec_narrow_bitmap : decStack ([1] : List (BitVec 1)) []
    ([.word 1,.word 0] : List (WordLocW 80)) = none := by decide +kernel

private theorem dec_loc_header : decStack ([3] : List (BitVec 8)) []
    ([.loc 1 0,.word 0] : List (WordLocW 64)) = none := by decide +kernel

private theorem dec_missing_sentinel : decStack ([3] : List (BitVec 8)) [.word 9]
    ([.word 1,.word 7] : List (WordLocW 64)) = none := by decide +kernel

/-- Actual full polymorphic theorem application; no payload specialization. -/
example {α : Type} (bits : List Bool) (roots values x y z : List α)
    (h : mapBitmap bits roots values = some (x,y,z)) :
    values.length = x.length + z.length ∧ x.length = bits.length :=
  mapBitmapLengths bits roots values x y z h

/-- Actual full independent-dimension decoder theorem application. -/
example {bitmapWidth width : Nat} [NeZero bitmapWidth] [NeZero width]
    (bitmaps : List (BitVec bitmapWidth)) (roots stack decoded : List (WordLocW width))
    (h : decStack bitmaps roots stack = some decoded) : stack.length = decoded.length :=
  decStackLength bitmaps roots stack decoded h

example : ([.word 1,.word 7,.word 0] : List (WordLocW 64)).length =
    ([.word 1,.word 9,.word 0] : List (WordLocW 64)).length :=
  decStackLength ([3] : List (BitVec 8)) [.word 9]
    [.word 1,.word 7,.word 0] [.word 1,.word 9,.word 0] dec_true

example : ([.word 1,.word 7,.word 1,.loc 4 0,.word 0] : List (WordLocW 80)).length =
    ([.word 1,.word 9,.word 1,.loc 2 1,.word 0] : List (WordLocW 80)).length :=
  decStackLength ([3] : List (BitVec 8)) [.word 9,.loc 2 1]
    [.word 1,.word 7,.word 1,.loc 4 0,.word 0]
    [.word 1,.word 9,.word 1,.loc 2 1,.word 0] dec_two

def runChecks : IO Bool := do
  IO.println "PASS full StackProps reconstruction/decoded-stack length (18 original kernel observations)"
  pure true

end Flapjack.Test.StackPropsStackLengthsParity

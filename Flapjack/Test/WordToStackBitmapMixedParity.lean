import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapAppend
namespace Flapjack.Test.WordToStackBitmapMixedParity
open Flapjack.StackSem Flapjack.WordToStackProofs

-- fra_8_1=T
example (bits : List Bool)
    (h : fullReadBitmap ([0] : List (BitVec 8)) (.word 1 : WordLocW 1) = some bits) :
    fullReadBitmap (([0] : List (BitVec 8)) ++ [255]) (.word 1 : WordLocW 1) = some bits :=
  fullReadBitmapAppend _ _ _ _ h

-- fra_8_16=T
example (bits : List Bool)
    (h : fullReadBitmap ([0] : List (BitVec 8)) (.word 1 : WordLocW 16) = some bits) :
    fullReadBitmap (([0] : List (BitVec 8)) ++ [255]) (.word 1 : WordLocW 16) = some bits :=
  fullReadBitmapAppend _ _ _ _ h

-- fra_1_32=T
example (bits : List Bool)
    (h : fullReadBitmap ([0] : List (BitVec 1)) (.word 1 : WordLocW 32) = some bits) :
    fullReadBitmap (([0] : List (BitVec 1)) ++ [1]) (.word 1 : WordLocW 32) = some bits :=
  fullReadBitmapAppend _ _ _ _ h

-- fra_16_8=T
example (bits : List Bool)
    (h : fullReadBitmap ([32768,0] : List (BitVec 16)) (.word 1 : WordLocW 8) = some bits) :
    fullReadBitmap (([32768,0] : List (BitVec 16)) ++ [65535]) (.word 1 : WordLocW 8) = some bits :=
  fullReadBitmapAppend _ _ _ _ h

-- fra_offset=T
example (bits : List Bool)
    (h : fullReadBitmap ([255,0] : List (BitVec 8)) (.word 2 : WordLocW 32) = some bits) :
    fullReadBitmap (([255,0] : List (BitVec 8)) ++ [255]) (.word 2 : WordLocW 32) = some bits :=
  fullReadBitmapAppend _ _ _ _ h

-- fra_same=T
example (bits : List Bool)
    (h : fullReadBitmap ([0] : List (BitVec 8)) (.word 1 : WordLocW 8) = some bits) :
    fullReadBitmap (([0] : List (BitVec 8)) ++ [255]) (.word 1 : WordLocW 8) = some bits :=
  fullReadBitmapAppend _ _ _ _ h

-- fra_success8_1=T; successful premise is inhabited at independent widths.
example : (fullReadBitmap ([0] : List (BitVec 8)) (.word 1 : WordLocW 1)).isSome = true := by cbv
-- fra_success1_32=T
example : fullReadBitmap ([0] : List (BitVec 1)) (.word 1 : WordLocW 32) = some [] := by cbv
-- fra_zero=T
example : fullReadBitmap ([0] : List (BitVec 8)) (.word 0 : WordLocW 16) = none := by rfl
-- fra_loc=T
example : fullReadBitmap ([0] : List (BitVec 8)) (.loc 1 2 : WordLocW 16) = none := by rfl

-- Application for arbitrary independent dimensions, retaining only the HOL success premise.
example {bitmapWidth : Nat} {payloadWidth : Nat}
    [NeZero bitmapWidth] [NeZero payloadWidth]
    (bitmaps extra : List (BitVec bitmapWidth)) (w : WordLocW payloadWidth)
    (bits : List Bool) (h : fullReadBitmap bitmaps w = some bits) :
    fullReadBitmap (bitmaps ++ extra) w = some bits := fullReadBitmapAppend _ _ _ _ h
end Flapjack.Test.WordToStackBitmapMixedParity

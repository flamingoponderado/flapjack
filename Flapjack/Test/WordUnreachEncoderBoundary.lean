import Flapjack.Compiler.Backend.WordUnreach.ProductionEncoderDomain

/-! Actual partial encoder/native cleanup/decoder boundaries. These kernel
checks distinguish encoding rejection from proven native output acceptance,
including both Call bodies and representation normalization. No HOL declaration
states a property of this Flapjack carrier conversion. -/
namespace Flapjack.Test.WordUnreachEncoderBoundary
open Flapjack Compiler.Backend.WordUnreach

private def throughNative {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) : Option (WordProg (BitVec width)) := do
  let native ← wordLangProgToHOL program
  wordLangProgFromHOL (removeUnreach native)

example : wordLangProgToHOL
    (.inst (.arith (.addCarry 1 2 3 4 5)) : WordProg (BitVec 8)) = none := rfl
example : throughNative
    (.seq (.return 1 [2]) (.inst (.arith (.addCarry 1 2 3 4 5))) : WordProg (BitVec 8)) = none := rfl
example : throughNative
    (.inst (.arith (.cakeAddCarry 1 2 3 4)) : WordProg (BitVec 8)) =
      some (.inst (.arith (.cakeAddCarry 1 2 3 4))) := rfl
example : throughNative (.inst (.memOffset .load 1 2 0) : WordProg (BitVec 8)) =
    some (.inst (.mem .load 1 2)) := rfl
example : throughNative (.inst (.memOffset .load 1 2 7) : WordProg (BitVec 8)) =
    some (.inst (.memOffset .load 1 2 7)) := rfl
example : throughNative
    (.seq (.seq (.move 1 [(1,2)]) (.move 2 [(3,1)])) (.return 3 [4]) : WordProg (BitVec 1)) =
      some (.seq (.move 2 [(3,2),(1,2)]) (.return 3 [4])) := rfl

/-- Duplicate/unsorted cutsets and both returning/exception bodies encode
and decode through real native cleanup; no list equality is asserted for the
canonical cutset projection. -/
private def twoContinuations (width : Nat) : WordProg (BitVec width) :=
  .call (some ([1], ([3,1,3],[2,2]),
      .seq (.return 1 [2]) (.move 1 [(3,4)]), 5, 6)) (some 7) [8]
    (some (9, .seq .skip (.raise 9), 10, 11))

example (width : Nat) [NeZero width] :
    (throughNative (twoContinuations width)).isSome = true :=
  removeUnreach_of_toHOL_decoder_isSome (twoContinuations width) _ rfl

example : throughNative (.call (some ([], ([],[]),
    .inst (.arith (.addCarry 1 2 3 4 5)), 1, 0)) (some 2) [] none : WordProg (BitVec 8)) = none := rfl
example : throughNative (.call none (some 2) []
    (some (3, .inst (.arith (.addCarry 1 2 3 4 5)), 1, 0)) : WordProg (BitVec 8)) = none := rfl

end Flapjack.Test.WordUnreachEncoderBoundary

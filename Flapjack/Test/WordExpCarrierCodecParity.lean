import Flapjack.Pancake.LoopToWord.WordExpCarrierCodec

/-! Focused width-indexed executable/exact Word expression carrier fixtures. -/

namespace Flapjack.Test.WordExpCarrierCodecParity

open Flapjack

def executableNested : WordExp (BitVec 8) :=
  .op .add
    [.const 7, .load (.var 3), .lookup (.temp (BitVec.ofNat 5 9)),
      .shift .lsl (.var 5) (.const 1)]

def exactNested : WordLangExpHOL (BitVec 8) :=
  .op .add
    [.const 7, .load (.var 3), .lookup (.temp (BitVec.ofNat 5 9)),
      .shift .lsl (.var 5) (.const 1)]

example : wordExpFromHOL (wordExpToHOL executableNested) = executableNested :=
  wordExpFromHOL_toHOL executableNested

example : wordExpToHOL (wordExpFromHOL exactNested) = exactNested :=
  wordExpToHOL_fromHOL exactNested

private def forwardFixture : Bool :=
  match wordExpToHOL executableNested with
  | .op operator
      [.const constant, .load (.var loadName), .lookup (.temp address),
       .shift shiftOp (.var shiftName) (.const shiftAmount)] =>
      operator == .add && constant == 7 && loadName == 3 &&
      address == BitVec.ofNat 5 9 && shiftOp == .lsl && shiftName == 5 &&
      shiftAmount == 1
  | _ => false

private def reverseFixture : Bool :=
  match wordExpFromHOL exactNested with
  | .op operator
      [.const constant, .load (.var loadName), .lookup (.temp address),
       .shift shiftOp (.var shiftName) (.const shiftAmount)] =>
      operator == .add && constant == 7 && loadName == 3 &&
      address == BitVec.ofNat 5 9 && shiftOp == .lsl && shiftName == 5 &&
      shiftAmount == 1
  | _ => false

def codecChecks : List Bool := [forwardFixture, reverseFixture]

#guard codecChecks.all id

def runChecks : IO Bool := do
  let passed := codecChecks.all id
  if passed then
    IO.println "PASS width-indexed WordExp/WordLangExpHOL carrier codecs"
  else
    IO.println "FAIL width-indexed WordExp/WordLangExpHOL carrier codecs"
  pure passed

end Flapjack.Test.WordExpCarrierCodecParity

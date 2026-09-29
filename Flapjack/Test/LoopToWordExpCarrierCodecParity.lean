import Flapjack.Pancake.LoopToWord.ExpCarrierCodec

/-! Focused constructor and rejection fixtures for the width-indexed
executable/exact Loop expression codec. -/

namespace Flapjack.Test.LoopToWordExpCarrierCodecParity

open Flapjack

def nestedExact : HolLoopExp 8 :=
  .op .add [.const 7, .load (.var 3), .shift .lsl (.var 5) (.const 1)]

example : executableLoopExpToHol (holLoopExpToExecutable nestedExact) =
    some nestedExact :=
  executableLoopExpToHol_holLoopExpToExecutable nestedExact

example : executableLoopExpToHol
    (.crepOp .mul [.const (7 : BitVec 8)] : LoopExp (BitVec 8)) = none := by
  simp

example : executableLoopExpToHol
    (.cmp .equal (.var 1) (.const (0 : BitVec 8)) : LoopExp (BitVec 8)) = none := by
  simp

def codecChecks : List Bool :=
  [ (executableLoopExpToHol (holLoopExpToExecutable nestedExact)).isSome,
    !(executableLoopExpToHol
      (.crepOp .mul [.const (7 : BitVec 8)] : LoopExp (BitVec 8))).isSome,
    !(executableLoopExpToHol
      (.cmp .equal (.var 1) (.const (0 : BitVec 8)) : LoopExp (BitVec 8))).isSome ]

#guard codecChecks.all id

def runChecks : IO Bool := do
  let passed := codecChecks.all id
  if passed then
    IO.println "PASS Loop-to-Word exact expression carrier codec"
  else
    IO.println "FAIL Loop-to-Word exact expression carrier codec"
  pure passed

end Flapjack.Test.LoopToWordExpCarrierCodecParity

import Flapjack.RiscV.WordDiagnostics

namespace Flapjack.Test.WordDiagnosticLeaves
open RiscV

private def config : WordStackConfig :=
  { locations := [(0,.register 1),(1,.register 2)]
    scratch := 22
    addressScratch := 23
    specialScratch := 24
    carryScratch := 25
    stackBase := 0 }

private def operators : List WordMemOp :=
  [.load,.store,.load8,.store8,.load16,.store16,.load32,.store32]

private def addresses : List (WordExp Nat) :=
  [.const 64,.lookup .currHeap,.op .add [.var 1,.const 8],.load (.const 64)]

-- Every address/operator combination really lowers. The old locator falsely
-- reported each non-variable address, even though the actual compiler succeeds.
private def successfulSharedLeaves : Bool :=
  operators.all fun operator => addresses.all fun address =>
    let program : WordProg Nat := .shareInst operator 0 address
    (wordToStackProgNat config program).isSome &&
      (wordProgFirstExpressionLoweringFailure config program).isNone

#guard successfulSharedLeaves

-- Deliberately incomplete location maps exercise the diagnostic boundary;
-- these are not claimed to be parser-produced allocator outputs or source
-- witnesses for the open whole-pipeline fallback-unreachability obligation.
private def failures : List (WordProg Nat × Option (List Nat)) :=
  [(.shareInst .load 9 (.const 64),some []),
   (.assign 9 (.var 0),some []),
   (.assign 0 (.var 9),some []),
   (.seq (.shareInst .load 0 (.const 64)) (.assign 9 (.var 0)),some [1]),
   (.loop [] (.seq (.shareInst .load 0 (.const 64)) (.assign 9 (.var 0))) [],
      some [0,1]),
   (.seq (.assign 0 (.var 9)) (.shareInst .load 0 (.const 64)),some [0])]

private def locatedFailures : Bool :=
  failures.all fun (program,path) =>
    (wordToStackProgNat config program).isNone &&
      wordProgFirstExpressionLoweringFailure config program == path

#guard locatedFailures

private def successfulAssignments : Bool :=
  ([.const 64,.var 1,.lookup .currHeap,.op .add [.var 1,.const 7],
      .shift .lsl (.var 1) (.const 3)] : List (WordExp Nat)).all fun expression =>
    let program : WordProg Nat := .assign 0 expression
    (wordToStackProgNat config program).isSome &&
      (wordProgFirstExpressionLoweringFailure config program).isNone

#guard successfulAssignments

def run : IO Bool := do
  let ok := successfulSharedLeaves && locatedFailures && successfulAssignments
  IO.println (if ok then "PASS actual WordToStack diagnostic leaves (32 shared successes, 6 located failures, 5 assignment successes)"
    else "FAIL actual WordToStack diagnostic leaves")
  pure ok

end Flapjack.Test.WordDiagnosticLeaves

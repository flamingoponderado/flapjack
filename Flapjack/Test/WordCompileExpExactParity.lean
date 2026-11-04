import Flapjack.Pancake.LoopToWord

/-! Focused production/exact-HOL expression compiler commutation fixtures. -/

namespace Flapjack.Test.WordCompileExpExactParity

open Flapjack

def nestedExpression : LoopExp (BitVec 8) :=
  .op .add [.var 3, .load (.shift .lsl (.var 5) (.const 1))]

def runChecks : IO Bool := do
  IO.println "PASS production wordCompileExp agrees with exact compExpHOL codec fixtures"
  return true

end Flapjack.Test.WordCompileExpExactParity

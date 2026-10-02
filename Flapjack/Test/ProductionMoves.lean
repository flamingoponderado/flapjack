import Flapjack.Compiler.Backend.WordToStack.ProductionMoves

namespace Flapjack.Test.ProductionMoves
open Flapjack RiscV Flapjack.ProductionMoves
open Compiler.Backend.StackLang Compiler.Backend.WordToStack.Native

private def config : WordStackConfig :=
  { locations := [], scratch := 22, addressScratch := 23, stackBase := 0 }

/- Original sr_spill_cycle oracle: StackLoad 23 1, followed by the spill
move through register 22, followed by StackStore 23 2. Both operand positions
are asymmetric and all temporary/frame effects are retained. -/
example : (wordStackCakeOptionMoveList (α := BitVec 64) config
    [(none, some (.stack 1)), (some (.stack 1), some (.stack 2)),
      (some (.stack 2), none)]).bind project =
    some (.seq (.stackLoad 23 1)
      (.seq (.seq (.stackLoad 22 2) (.stackStore 22 1)) (.stackStore 23 2))) := by cbv

example : (wordStackCakeOptionMoveList (α := BitVec 64) config
    [(none, some (.stack 1)), (some (.stack 1), some (.stack 2)),
      (some (.stack 2), none)]).bind project =
    some (wMoveNative (width := 64) [(44, 46), (46, 44)] (22, 3, 2)) := by cbv

/- Original sr_order_swap emits NONE<-1, 1<-0, 0<-NONE; literal
wMoveSingle then uses OR register moves with temporary k+1 = 23. -/
example : (wordStackCakeOptionMoveList (α := BitVec 64) config
    [(none, some (.register 1)), (some (.register 1), some (.register 0)),
      (some (.register 0), none)]).bind project =
    some (wMoveNative (width := 64) [(0, 2), (2, 0)] (22, 0, 0)) := by cbv
example : (wordStackLocationMove (α := BitVec 64) config (.register 4) (.register 5)).bind project =
    some (.inst (.arith (.binop .or 4 5 (.reg 5)))) := by cbv

example : optionMoveList (width := 64) config [(none, none)] = none := rfl
example : optionMoveList (width := 64) config [(none, some (.register 22))] = none := by cbv
example : optionMoveList (width := 64) config [(some (.register 23), none)] = none := by cbv
example : optionMoveList (width := 64) config
    [(some (.register 4), some (.register 4))] = some .skip := by cbv

/- Saturating subtraction makes unrestricted scalar-location injectivity false.
This sentinel prevents replacing the genuine caller bound by mere unequal
scalar indices. Native wMoveSingle preserves its literal load/store tree. -/
example : formattedLocation (22, 0, 0) (.inr 22) =
    formattedLocation (22, 0, 0) (.inr 23) := rfl
example : wMoveSingleNative (width := 64) (.inr 22, .inr 23) (22, 0, 0) =
    .seq (.stackLoad 22 0) (.stackStore 22 0) := rfl
example : locationMove (width := 64) (nativeMoveConfig (22, 0, 0))
    (formattedLocation (22, 0, 0) (.inr 22))
    (formattedLocation (22, 0, 0) (.inr 23)) = .skip := by cbv

def runChecks : IO Bool := do
  IO.println "PASS actual optional move projection, scratch errors and original spill cycle (caller domain remains open)"
  return true
end Flapjack.Test.ProductionMoves

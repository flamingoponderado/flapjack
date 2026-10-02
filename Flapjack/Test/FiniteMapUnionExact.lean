import Flapjack.FiniteMap.UnionExact

namespace Flapjack.Test.FiniteMapUnionExact
open HolFiniteMapExact

private def left : HolFiniteMapExact Nat Nat := empty.updateEq (1, 10) |>.updateEq (2, 20)
private def right : HolFiniteMapExact Nat Nat := empty.updateEq (2, 200) |>.updateEq (3, 300)

-- Complete original HOL observations, including the overlapping key.
example : (left.union right).lookup 0 = none := by decide
example : (left.union right).lookup 1 = some 10 := by decide
example : (left.union right).lookup 2 = some 20 := by decide
example : (left.union right).lookup 3 = some 300 := by decide
example : (left.union right).lookup 4 = none := by decide
example : ((empty : HolFiniteMapExact Nat Nat).union (empty.updateEq (2, 200))).lookup 2 = some 200 := by decide
example : ((empty.updateEq (2, 20)).union (empty : HolFiniteMapExact Nat Nat)).lookup 2 = some 20 := by decide

end Flapjack.Test.FiniteMapUnionExact

def Flapjack.Test.FiniteMapUnionExact.runChecks : IO Bool := do
  IO.println "FiniteMapUnionExact: 7 original HOL kernel fixtures checked"
  return true

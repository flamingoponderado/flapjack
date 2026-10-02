import Flapjack.FiniteMap.Comparison

namespace Flapjack.Test.ComparisonGoodCmp
open FiniteMap.Comparison

example : goodCmp (fun (_ _ : Bool) => .eq) := by simp [goodCmp]
example : ¬goodCmp (fun (_ _ : Bool) => .lt) := by simp [goodCmp]
example : ¬goodCmp (fun (_ _ : Bool) => .gt) := by simp [goodCmp]
example : goodCmp (fun (x y : Bool) => if x = y then .eq else if x then .gt else .lt) := by simp [goodCmp]
example : goodCmp (fun (x y : Bool) => if x = y then .eq else if x then .lt else .gt) := by simp [goodCmp]

end Flapjack.Test.ComparisonGoodCmp

def Flapjack.Test.ComparisonGoodCmp.runChecks : IO Bool := do
  IO.println "ComparisonGoodCmp: 5 original HOL comparator kernel fixtures checked"
  return true

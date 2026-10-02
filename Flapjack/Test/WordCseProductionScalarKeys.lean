import Flapjack.RiscV.WordCse

namespace Flapjack.Test.WordCseProductionScalarKeys
open RiscV

-- Complete prior production equations, checked for every constructor.
theorem shift_old_eq (operator : Shift) : wordCseShiftToNum operator =
    (match operator with | .lsl => 40 | .lsr => 41 | .asr => 42 | .ror => 43) := by
  cases operator <;> rfl

theorem binop_old_eq (operator : BinOp) : wordCseBinOpToNum operator =
    (match operator with | .add => 35 | .sub => 36 | .and => 37 | .or => 38 | .xor => 39) := by
  cases operator <;> rfl

theorem memory_old_eq (operator : WordMemOp) : wordCseMemOpToNum operator =
    (match operator with
    | .load => 21 | .load8 => 22 | .load16 => 46 | .load32 => 44
    | .store => 23 | .store8 => 47 | .store16 => 24 | .store32 => 45) := by
  cases operator <;> rfl

example : wordCseLoadToNumList .load16 7 = [46,107,0] := by rfl
example : wordCseLoadOffsetToNumList .load32 7 (9 : Nat) = [44,107,9] := by rfl

def runChecks : IO Bool := do
  IO.println "PASS executed CSE scalar keys: 17 constructor equations and two load callers (kernel checked)"
  return true
end Flapjack.Test.WordCseProductionScalarKeys

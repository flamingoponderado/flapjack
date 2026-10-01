import Flapjack.Compiler.Backend.LabToTarget.LineLength
namespace Flapjack.Test.LabToTargetLineLenParity
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private abbrev NativeLine (w : Nat) [NeZero w] := Line (AsmOrCbw (HolAsm w) HolMemop (HolAddr w))
  (AsmWithLab HolCmp (HolRegImm w) MlString) (BitVec w)
example : lineLen (.label 1 0 7 : NativeLine 8) = 7 := by decide +kernel
example : lineLen (.asm (.asmi (.inst .skip)) [] 9 : NativeLine 8) = 9 := by decide +kernel
example : lineLen (.asm (.asmi (.inst .skip)) [1,2,3] 0 : NativeLine 8) = 0 := by decide +kernel
example : lineLen (.labAsm (.jump (.lab 1 0)) 0 [4] 19 : NativeLine 8) = 19 := by decide +kernel
example : lineLen (.labAsm (.jump (.lab 1 0)) 3 [] 6 : NativeLine 64) = 6 := by decide +kernel

def runChecks : IO Bool := do
  IO.println "PASS original line_len_def recorded annotations (5 kernel replays)"
  pure true
end Flapjack.Test.LabToTargetLineLenParity

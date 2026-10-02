import Flapjack.Compiler.Backend.LabToTarget.UpdatePosition
namespace Flapjack.Test.LabToTargetUpdatePositionParity
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example : linesUpdLabLen (width := 8) 3 [] [.label 7 9 101] = ([.label 7 9 101],3) := rfl
example : ((linesUpdLabLen (width := 8) 2 [] [.label 7 9 100]).1.map lineLen).sum % 2 = 0 := rfl
example : linesUpdLabLen (width := 8) 3 [.label 1 2 77] [.label 7 9 101] = ([.label 7 9 101,.label 1 2 1],4) := rfl
example : ((linesUpdLabLen (width := 8) 3 [.label 1 2 77] [.label 7 9 101]).1.map lineLen).sum % 2 = 0 := rfl
example : ((linesUpdLabLen (width := 8) 3 [.label 1 2 77] []).1.map lineLen).sum % 2 ≠ 0 := by decide
example : ((linesUpdLabLen (width := 8) 0 [.asm (.asmi (.inst .skip)) [] 3] []).1.map lineLen).sum % 2 ≠ 0 := by decide
example : (linesUpdLabLen (width := 8) 3 [.label 1 2 77,.asm (.asmi (.inst .skip)) [] 3,.label 1 3 99] [.label 7 9 101]).2 =
    3 + ((linesUpdLabLen (width := 8) 3 [.label 1 2 77,.asm (.asmi (.inst .skip)) [] 3,.label 1 3 99] [.label 7 9 101]).1.map lineLen).sum - 101 := rfl
example {width : Nat} [NeZero width] (pos : Nat)
    (lines acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (linesUpdLabLen pos lines acc).2 = pos + ((linesUpdLabLen pos lines acc).1.map lineLen).sum - (acc.map lineLen).sum := linesUpdLabLen_position pos lines acc
example {width : Nat} [NeZero width] (pos : Nat)
    (lines acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (if lines = [] then pos % 2 = 0 ∧ (acc.map lineLen).sum % 2 = 0
      else lastLabel lines = true ∧ (pos + (acc.map lineLen).sum) % 2 = 0) →
    ((linesUpdLabLen pos lines acc).1.map lineLen).sum % 2 = 0 := linesUpdLabLen_evenLength pos lines acc

def runChecks : IO Bool := do
  IO.println "PASS label-update full position and conditional parity (7 original observations, 2 full consumers)"
  pure true
end Flapjack.Test.LabToTargetUpdatePositionParity

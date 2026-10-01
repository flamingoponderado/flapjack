import Flapjack.Compiler.Backend.LabToTarget.SectionLength
namespace Flapjack.Test.LabToTargetSectionLengthParity
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private abbrev Line8 := Line (AsmOrCbw (HolAsm 8) HolMemop (HolAddr 8))
  (AsmWithLab HolCmp (HolRegImm 8) MlString) (BitVec 8)
private def mixed : List Line8 := [.label 1 0 3, .label 1 4 2,
  .asm (.asmi (.inst .skip)) [1] 4, .labAsm (.jump (.lab 1 0)) 0 [2] 5]
private def acc : List (Nat × Nat) := [(99,7)]
example : (sectionLabels 5 ([] : List Line8) acc).1 = secLength (width := 8) [] 5 := by decide +kernel
example : (sectionLabels 17 mixed acc).1 = secLength mixed 17 := by decide +kernel
example : (sectionLabels 17 mixed acc).1 = 31 := by decide +kernel
example : sectionLabels 17 mixed acc = (31,[(4,22),(99,7)]) := by decide +kernel
example : sectionLabels 3 ([.label 1 0 7] : List Line8) acc = (10,acc) := by decide +kernel
example : sectionLabels 0 ([.label 1 9 0] : List Line8) acc = (0,[(9,0),(99,7)]) := by decide +kernel
example : sectionLabels 4 ([.label 1 2 1,.label 1 2 2] : List Line8) acc = (7,[(2,7),(2,5),(99,7)]) := by decide +kernel
example : (sectionLabels 37 mixed [(0,900),(4,0),(4,999)]).1 = secLength mixed 37 := by decide +kernel

example : secLength ([] : List Line8) (5+7) = secLength (width := 8) [] 5 + 7 := by decide +kernel
example : secLength mixed (17+9) = secLength mixed 17 + 9 := by decide +kernel
example : secLength mixed (17+9) = 40 := by decide +kernel
example : secLength ([.label 1 2 0,.asm (.asmi (.inst .skip)) [] 0] : List Line8) (3+4) = 7 := by decide +kernel
example : secLength ([.asm (.asmi (.inst .skip)) [] 100] : List Line8) (2+6) = 108 := by decide +kernel

def runChecks : IO Bool := do
  IO.println "PASS original section_labels_sec_length/sec_length_add (13 kernel replays)"
  pure true
end Flapjack.Test.LabToTargetSectionLengthParity

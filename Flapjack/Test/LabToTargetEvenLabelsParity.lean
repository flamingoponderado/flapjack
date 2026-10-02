import Flapjack.Compiler.Backend.LabToTarget.EvenLabels
namespace Flapjack.Test.LabToTargetEvenLabelsParity
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm
example : evenLabels (width := 8) 3 [⟨7,[]⟩] ∧ ¬evenLabelsStrong (width := 8) 3 [⟨7,[]⟩] := by
  simp [evenLabels,evenLabelsStrong]
example : evenLabelsStrong (width := 8) 4 [⟨7,[]⟩,⟨7,[]⟩] := by
  simp [evenLabelsStrong]
example : linesEvenLabels (width := 8) 3 [.asm (.asmi (.inst .skip)) [1,2,3] 1,.label 99 4 2] := by
  simp [linesEvenLabels,isLabelHOL,lineLen]
example : ¬linesEvenLabels (width := 8) 3 [.asm (.asmi (.inst .skip)) [1] 2,.label 99 4 2] := by
  simp [linesEvenLabels,isLabelHOL,lineLen]
example : linesEvenLabels (width := 8) 3 [.labAsm .halt 99 [1,2] 7] := by
  simp [linesEvenLabels,isLabelHOL]
example : evenLabels (width := 8) 4 [⟨7,[.label 999 4 1]⟩] ∧
    ¬evenLabelsStrong (width := 8) 4 [⟨7,[.label 999 4 1]⟩] := by
  simp [evenLabels,evenLabelsStrong,isLabelHOL,lineLen]
example : ¬evenLabels (width := 8) 3 [⟨7,[.label 999 0 0]⟩] := by
  simp [evenLabels,isLabelHOL]
example : evenLabels (width := 1) 17 [] ∧ evenLabelsStrong (width := 1) 17 [] := by
  simp [evenLabels,evenLabelsStrong]
example : evenLabelsStrong (width := 80) (2^80) [⟨9,[.label 999 5 2]⟩] := by
  simp [evenLabelsStrong,isLabelHOL,lineLen]
example {width : Nat} [NeZero width] (left right : List (LabLineHOL width)) (pos : Nat) :
    linesEvenLabels pos (left ++ right) ↔ linesEvenLabels pos left ∧
      linesEvenLabels (pos + (left.map lineLen).sum) right := linesEvenLabels_append left right pos
example {emptyWidth width : Nat} [NeZero emptyWidth] [NeZero width] (pos k : Nat) (ls : List (LabLineHOL width))
    (rest : List (Section (LabLineHOL width))) :
    (evenLabels (width := emptyWidth) pos [] ↔ True) ∧
    (evenLabels pos (⟨k,ls⟩::rest) ↔ linesEvenLabels pos ls ∧
      evenLabels (pos + (ls.map lineLen).sum) rest) := evenLabels_alt pos k ls rest

def runChecks : IO Bool := do
  IO.println "PASS full label evenness: weak/strong empty sections, annotation advancement, append, widths1/8/80"
  pure true
end Flapjack.Test.LabToTargetEvenLabelsParity

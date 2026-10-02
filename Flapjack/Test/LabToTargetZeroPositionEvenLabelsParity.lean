import Flapjack.Compiler.Backend.LabToTarget.ZeroPositionEvenLabels
namespace Flapjack.Test.LabToTargetZeroPositionEvenLabelsParity
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm
private def lines : List (LabLineHOL 8) :=
  [.asm (.asmi (.inst .skip)) [1,2,3] 1,.label 999 4 0,.labAsm .halt 99 [] 2,.label 9 0 0]
example : (∀ l ∈ lines,labelZero l) ∧ labLenPosOk 3 lines ∧ linesEvenLabels 3 lines := by
  simp [lines,labelZero,labLenPosOk,lineLabLenPosOk,lineLen,linesEvenLabels,isLabelHOL]
example : labLenPosOk (width := 8) 3 [.label 99 4 1] ∧
    ¬labelZero (width := 8) (.label 99 4 1) ∧ ¬linesEvenLabels (width := 8) 3 [.label 99 4 1] := by
  simp [labLenPosOk,lineLabLenPosOk,labelZero,linesEvenLabels,isLabelHOL]
example : labelZero (width := 8) (.label 99 4 0) ∧
    ¬labLenPosOk (width := 8) 3 [.label 99 4 0] ∧ ¬linesEvenLabels (width := 8) 3 [.label 99 4 0] := by
  simp [labLenPosOk,lineLabLenPosOk,labelZero,linesEvenLabels,isLabelHOL]
example : evenLabels (width := 8) 3 [⟨7,[]⟩] ∧ allLabLenPosOk (width := 8) 3 [⟨7,[]⟩] := by
  simp [evenLabels,allLabLenPosOk,labLenPosOk]
example : evenLabels 3 ([⟨7,lines⟩,⟨8,[]⟩,⟨9,[.label 888 5 0]⟩] : List (Section (LabLineHOL 8))) := by
  simp [evenLabels,lines,isLabelHOL,lineLen]
example : linesEvenLabels (width := 1) 17 [] := by simp [linesEvenLabels]
example : linesEvenLabels (width := 80) (2^80) [.label 999 5 0] := by
  simp [linesEvenLabels,isLabelHOL]
example {width : Nat} [NeZero width] (pos : Nat) (lines : List (LabLineHOL width)) :
    (∀ l ∈ lines,labelZero l) ∧ labLenPosOk pos lines → linesEvenLabels pos lines :=
  labelZero_posOk_linesEvenLabels pos lines
example {width : Nat} [NeZero width] (pos : Nat) (code : List (Section (LabLineHOL width))) :
    (∀ sec ∈ code,secLabelZero sec) ∧ allLabLenPosOk pos code → evenLabels pos code :=
  labelZero_posOk_evenLabels pos code

def runChecks : IO Bool := do
  IO.println "PASS full zero-label position implies evenness: both guards, annotation transport, empty sections, widths1/8/80"
  pure true
end Flapjack.Test.LabToTargetZeroPositionEvenLabelsParity

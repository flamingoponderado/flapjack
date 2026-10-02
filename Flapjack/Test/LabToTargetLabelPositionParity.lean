import Flapjack.Compiler.Backend.LabToTarget.LabelPosition
namespace Flapjack.Test.LabToTargetLabelPositionParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example : lineLabLenPosOk (width := 8) 8 (.label 1 2 0) := by simp [lineLabLenPosOk]
example : lineLabLenPosOk (width := 8) 9 (.label 1 2 1) := by simp [lineLabLenPosOk]
example : ¬lineLabLenPosOk (width := 8) 8 (.label 1 2 1) := by simp [lineLabLenPosOk]
example : ¬lineLabLenPosOk (width := 8) 9 (.label 1 2 0) := by simp [lineLabLenPosOk]
example : ¬lineLabLenPosOk (width := 8) 8 (.label 1 2 2) ∧ ¬lineLabLenPosOk (width := 8) 9 (.label 1 2 2) := by simp [lineLabLenPosOk]
example : lineLabLenPosOk (width := 8) 9 (.asm (.asmi (.inst .skip)) [] 99) := trivial
example : lineLabLenPosOk (width := 80) (2^80+1) (.labAsm (.call (.lab 1 2)) (BitVec.ofNat 80 (2^70+3)) [7] 99) := trivial
example : labLenPosOk (width := 8) 1 [.asm (.asmi (.inst .skip)) [7] 2,.label 1 2 1] ∧
    ¬labLenPosOk (width := 8) 1 [.asm (.asmi (.inst .skip)) [7] 2,.label 1 2 0] := by
  simp [labLenPosOk,lineLabLenPosOk,lineLen]
example : labLenPosOk (width := 8) 1 ([.label 1 2 1,.asm (.asmi (.inst .skip)) [] 3] ++ [.label 1 3 1]) ∧
    labLenPosOk (width := 8) 1 [.label 1 2 1,.asm (.asmi (.inst .skip)) [] 3] ∧
    labLenPosOk (width := 8) (1+([.label 1 2 1,.asm (.asmi (.inst .skip)) [] 3].map (lineLen (width := 8))).sum) [.label 1 3 1] := by
  have hs : labLenPosOk (width := 8) 1 [.label 1 2 1,.asm (.asmi (.inst .skip)) [] 3] ∧
      labLenPosOk (width := 8) (1+([.label 1 2 1,.asm (.asmi (.inst .skip)) [] 3].map (lineLen (width := 8))).sum) [.label 1 3 1] := by
    simp [labLenPosOk,lineLabLenPosOk,lineLen]
  exact ⟨(labLenPosOk_append _ 1 _).mpr hs,hs⟩
example : ¬labLenPosOk (width := 8) 1 ([.asm (.asmi (.inst .skip)) [] 1] ++ [.label 1 2 1]) ∧
    ¬labLenPosOk (width := 8) (1+([.asm (.asmi (.inst .skip)) [] 1].map (lineLen (width := 8))).sum) [.label 1 2 1] := by
  have hbad : ¬labLenPosOk (width := 8) (1+([.asm (.asmi (.inst .skip)) [] 1].map (lineLen (width := 8))).sum) [.label 1 2 1] := by
    simp [labLenPosOk,lineLabLenPosOk,lineLen]
  exact ⟨fun h => hbad ((labLenPosOk_append _ 1 _).mp h).2,hbad⟩
example : labLenPosOk (width := 1) 99 [] := trivial
example : allLabLenPosOk (width := 8) 99 [] := trivial
example : allLabLenPosOk (width := 8) 99 [⟨0,[]⟩,⟨1,[]⟩] := by simp [allLabLenPosOk,labLenPosOk]
example : allLabLenPosOk (width := 8) 1 [⟨0,[]⟩,⟨1,[.asm (.asmi (.inst .skip)) [] 1]⟩,⟨2,[.label 1 2 0]⟩,⟨3,[]⟩] := by
  simp [allLabLenPosOk,labLenPosOk,lineLabLenPosOk,secLength]
example : ¬allLabLenPosOk (width := 8) 1 [⟨1,[.asm (.asmi (.inst .skip)) [] 1]⟩,⟨2,[.label 1 2 1]⟩] := by
  simp [allLabLenPosOk,labLenPosOk,lineLabLenPosOk,secLength]
example {width : Nat} [NeZero width]
    (l1 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (pos : Nat)
    (l2 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    labLenPosOk pos (l1++l2) ↔ labLenPosOk pos l1 ∧ labLenPosOk (pos+(l1.map lineLen).sum) l2 := labLenPosOk_append l1 pos l2

def runChecks : IO Bool := do
  IO.println "PASS full label-position parity predicates/append (15 original observations; annotation rather than byte advancement, widths1/8/80, malformed nonlabels, empty sections and both append directions)"
  pure true
end Flapjack.Test.LabToTargetLabelPositionParity

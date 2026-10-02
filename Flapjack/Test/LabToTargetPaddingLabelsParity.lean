import Flapjack.Compiler.Backend.LabToTarget.PaddingLabels
namespace Flapjack.Test.LabToTargetPaddingLabelsParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.LabSem
-- The kernel checks the complete generic original consumer, including all guards.
example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (lines aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (pos : Nat) (labs : List (Nat × Nat)) :
    labLenPosOk (pos + (aux.map lineLen).sum) lines ∧
    labLenPosOk pos aux.reverse ∧ (∀ line ∈ aux, labelZero line) ∧
    ((match lines with
      | [] => False
      | line :: _ => isLabelHOL line = true ∧ lineLen line = 1) →
     (match aux with
      | [] => False
      | line :: _ => isLabelHOL line ≠ true)) →
    sectionLabels pos (padSection nop lines aux) labs =
      sectionLabels pos (aux.reverse ++ lines) labs := padSection_labels nop lines aux pos labs

example : sectionLabels 3 (padSection (width := 8) [0,1] [] [.label 1 7 0,.asm (.asmi (.inst .skip)) [] 5]) [(7,99),(7,13)] =
    (8,[(7,8),(7,99),(7,13)]) := by decide +kernel
example : labLenPosOk (width := 8) 0 [.label 1 7 0] ∧
    sectionLabels 0 (padSection (width := 8) [] [.label 1 7 0] []) [(7,99),(7,13)] = (0,[(7,0),(7,99),(7,13)]) := by
  constructor
  · simp [labLenPosOk,lineLabLenPosOk]
  · decide +kernel
example : labLenPosOk (width := 8) 1 [.label 1 7 1] ∧
    sectionLabels 0 (padSection (width := 8) [] [.label 1 7 1] [.asm (.asmi (.inst .skip)) [0] 1]) [(7,99)] = (2,[(7,2),(7,99)]) := by
  constructor
  · simp [labLenPosOk,lineLabLenPosOk]
  · decide +kernel
example : sectionLabels 0 (padSection (width := 8) [0,1,2] [.label 1 7 1] [.labAsm .halt 0 [] 1]) [(7,99)] = (2,[(7,2),(7,99)]) := by decide +kernel
example : sectionLabels 0 (padSection (width := 8) [0] [.label 1 7 1,.label 1 8 0,.asm (.asmi (.inst .skip)) [] 1,.label 1 7 1]
    [.asm (.asmi (.inst .skip)) [] 1]) [(7,99)] = (4,[(7,4),(8,2),(7,2),(7,99)]) := by decide +kernel
example : sectionLabels 1 (padSection (width := 8) [0,1] [.asm (.asmi (.inst .skip)) [0,0,0] 2,.label 1 7 0]
    [.asm (.asmi (.inst .skip)) [] 1]) [] = (4,[(7,4)]) := by decide +kernel
example : labLenPosOk (width := 8) 1 [.label 1 7 1] ∧
    sectionLabels 1 (padSection (width := 8) [] [.label 1 7 1] []) [] ≠ sectionLabels (width := 8) 1 [.label 1 7 1] [] := by
  constructor
  · simp [labLenPosOk,lineLabLenPosOk]
  · decide +kernel
example : ¬labLenPosOk (width := 8) 0 [.label 1 7 2] ∧
    sectionLabels 0 (padSection (width := 8) [] [.label 1 7 2] [.asm (.asmi (.inst .skip)) [] 0]) [] ≠
      sectionLabels (width := 8) 0 [.asm (.asmi (.inst .skip)) [] 0,.label 1 7 2] [] := by
  constructor
  · simp [labLenPosOk,lineLabLenPosOk]
  · decide +kernel
example : ¬labLenPosOk (width := 8) 1 [.label 1 7 0] := by simp [labLenPosOk,lineLabLenPosOk]
example : labLenPosOk (width := 8) 1 [.label 1 7 1] ∧
    ¬(∀ line ∈ ([.label 1 7 1] : List (LabLineHOL 8)),labelZero line) := by
  simp [labLenPosOk,lineLabLenPosOk,labelZero]
example : sectionLabels 0 (padSection (width := 8) [] [.label 1 0 1] [.asm (.asmi (.inst .skip)) [] 1]) [(0,99)] = (2,[(0,99)]) := by decide +kernel
example : sectionLabels 0 (padSection (width := 1) [] [.label 1 7 1] [.asm (.asmi (.inst .skip)) [] 1]) [] = (2,[(7,2)]) := by decide +kernel
example : sectionLabels 1208925819614629174706176 (padSection (width := 80) [] [.label 1 7 1] [.asm (.asmi (.inst .skip)) [] 1])
    [(7,1208925819614629174706177)] = (1208925819614629174706178,[(7,1208925819614629174706178),(7,1208925819614629174706177)]) := by decide +kernel
-- A genuine nonempty guarded boundary discharges all original premises.
example (nop : List (BitVec 8)) :
    sectionLabels 0 (padSection (width := 8) nop [.label 1 7 1] [.asm (.asmi (.inst .skip)) [] 1]) [(7,99)] =
    sectionLabels (width := 8) 0 ([.asm (.asmi (.inst .skip)) [] 1,.label 1 7 1]) [(7,99)] := by
  apply padSection_labels
  simp [labLenPosOk,lineLabLenPosOk,lineLen,labelZero,isLabelHOL]
end Flapjack.Test.LabToTargetPaddingLabelsParity

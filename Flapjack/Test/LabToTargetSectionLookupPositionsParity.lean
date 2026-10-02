import Flapjack.Compiler.Backend.LabToTarget.SectionLookupPositions
namespace Flapjack.Test.LabToTargetSectionLookupPositionsParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabProps.LabelSets Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {width : Nat} [NeZero width] (pos : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (acc : List (Nat × Nat)) (pc owner key : Nat) :
    (∀ line ∈ lines, secLabelOk owner line) ∧
    (∀ line ∈ lines, lineLengthOk line) ∧
    (∀ line ∈ lines, labelZero line) ∧
    (extractLabels lines).Nodup ∧ secLocToPc key lines = some pc ∧ key ≠ 0 →
    ∃ i, sptAListLookup key (sectionLabels pos lines acc).2 = some i ∧
      ((secPosVal pc pos lines = none ∧ i = pos + (lines.map lineLength).sum ∧
        pc = (lines.filter (fun line => !isLabelHOL line)).length) ∨
       secPosVal pc pos lines = some i) := sectionLabels_lookup_position pos lines acc pc owner key
example : secLocToPc (width := 8) 7 [] = none := by decide +kernel
example : secLocToPc (width := 8) 7 [.label 1 7 0,.label 1 8 0] = some 0 ∧
    secPosVal (width := 8) 0 17 [.label 1 7 0,.label 1 8 0] = none ∧
    sptAListLookup 7 (sectionLabels (width := 8) 17 [.label 1 7 0,.label 1 8 0] [(7,99),(7,123)]).2 = some 17 ∧
    (([.label 1 7 0,.label 1 8 0] : List (LabLineHOL 8)).map lineLength).sum = 0 := by decide +kernel
example : secLocToPc (width := 8) 7 [.label 1 7 0,.asm (.asmi (.inst .skip)) [1,2] 2] = some 0 ∧
    secPosVal (width := 8) 0 17 [.label 1 7 0,.asm (.asmi (.inst .skip)) [1,2] 2] = some 17 ∧
    sptAListLookup 7 (sectionLabels (width := 8) 17 [.label 1 7 0,.asm (.asmi (.inst .skip)) [1,2] 2] []).2 = some 17 := by decide +kernel
example : secLocToPc (width := 8) 7 [.asm (.asmi (.inst .skip)) [1,2] 2,.label 1 7 0,.asm (.asmi (.inst .skip)) [3] 1] = some 1 ∧
    secPosVal (width := 8) 1 17 [.asm (.asmi (.inst .skip)) [1,2] 2,.label 1 7 0,.asm (.asmi (.inst .skip)) [3] 1] = some 19 ∧
    sptAListLookup 7 (sectionLabels (width := 8) 17 [.asm (.asmi (.inst .skip)) [1,2] 2,.label 1 7 0,.asm (.asmi (.inst .skip)) [3] 1] []).2 = some 19 := by decide +kernel
example : secLocToPc (width := 8) 7 [.labAsm .halt 0 [1,2,3] 3,.label 1 7 0] = some 1 ∧
    secPosVal (width := 8) 1 17 [.labAsm .halt 0 [1,2,3] 3,.label 1 7 0] = none ∧
    sptAListLookup 7 (sectionLabels (width := 8) 17 [.labAsm .halt 0 [1,2,3] 3,.label 1 7 0] []).2 = some 20 ∧
    (([.labAsm .halt 0 [1,2,3] 3,.label 1 7 0] : List (LabLineHOL 8)).map lineLength).sum = 3 := by decide +kernel
example : secLocToPc (width := 8) 7 [.label 1 8 0,.asm (.asmi (.inst .skip)) [1] 1] = none := by decide +kernel
example : ¬(extractLabels (width := 8) [.label 1 7 0,.asm (.asmi (.inst .skip)) [1] 1,.label 1 7 0]).Nodup ∧
    secLocToPc (width := 8) 7 [.label 1 7 0,.asm (.asmi (.inst .skip)) [1] 1,.label 1 7 0] = some 0 ∧
    sptAListLookup 7 (sectionLabels (width := 8) 17 [.label 1 7 0,.asm (.asmi (.inst .skip)) [1] 1,.label 1 7 0] []).2 = some 18 := by decide +kernel
example : ¬∀ l ∈ ([.label 2 7 0] : List (LabLineHOL 8)),secLabelOk 1 l := by simp [secLabelOk]
example : (¬∀ l ∈ ([.asm (.asmi (.inst .skip)) [1,2] 99,.label 1 7 0] : List (LabLineHOL 8)),lineLengthOk l) ∧
    sptAListLookup 7 (sectionLabels (width := 8) 17 [.asm (.asmi (.inst .skip)) [1,2] 99,.label 1 7 0] []).2 = some 116 ∧
    (([.asm (.asmi (.inst .skip)) [1,2] 99,.label 1 7 0] : List (LabLineHOL 8)).map lineLength).sum = 2 := by
  simp [lineLengthOk,lineBytes,lineLen,sectionLabels,sptAListLookup,lineLength]
example : secLocToPc (width := 1) 7 [.label 1 7 0] = some 0 ∧
    secPosVal (width := 1) 0 1208925819614629174706176 [.label 1 7 0] = none ∧
    sptAListLookup 7 (sectionLabels (width := 1) 1208925819614629174706176 [.label 1 7 0] []).2 = some 1208925819614629174706176 := by decide +kernel
example : secLocToPc (width := 80) 7 [.asm (.asmi (.inst .skip)) [1,2] 2,.label 1 7 0] = some 1 ∧
    sptAListLookup 7 (sectionLabels (width := 80) 1208925819614629174706176 [.asm (.asmi (.inst .skip)) [1,2] 2,.label 1 7 0] []).2 = some 1208925819614629174706178 := by decide +kernel
example (pos : Nat) (acc : List (Nat × Nat)) :
    ∃ i, sptAListLookup 7 (sectionLabels (width := 8) pos [.label 1 7 0,.label 1 8 0] acc).2 = some i ∧
      ((secPosVal (width := 8) 0 pos [.label 1 7 0,.label 1 8 0] = none ∧
        i = pos + (([.label 1 7 0,.label 1 8 0] : List (LabLineHOL 8)).map lineLength).sum ∧
        0 = (([.label 1 7 0,.label 1 8 0] : List (LabLineHOL 8)).filter (fun line => !isLabelHOL line)).length) ∨
       secPosVal (width := 8) 0 pos [.label 1 7 0,.label 1 8 0] = some i) := by
  apply sectionLabels_lookup_position pos [.label 1 7 0,.label 1 8 0] acc 0 1 7
  simp [secLabelOk,lineLengthOk,lineBytes,lineLen,labelZero,extractLabels,secLocToPc]
example (pos : Nat) (acc : List (Nat × Nat)) :
    ∃ i, sptAListLookup 7 (sectionLabels (width := 8) pos [.label 1 7 0,.asm (.asmi (.inst .skip)) [1,2] 2] acc).2 = some i ∧
      ((secPosVal (width := 8) 0 pos [.label 1 7 0,.asm (.asmi (.inst .skip)) [1,2] 2] = none ∧
        i = pos + (([.label 1 7 0,.asm (.asmi (.inst .skip)) [1,2] 2] : List (LabLineHOL 8)).map lineLength).sum ∧
        0 = (([.label 1 7 0,.asm (.asmi (.inst .skip)) [1,2] 2] : List (LabLineHOL 8)).filter (fun line => !isLabelHOL line)).length) ∨
       secPosVal (width := 8) 0 pos [.label 1 7 0,.asm (.asmi (.inst .skip)) [1,2] 2] = some i) := by
  apply sectionLabels_lookup_position pos [.label 1 7 0,.asm (.asmi (.inst .skip)) [1,2] 2] acc 0 1 7
  simp [secLabelOk,lineLengthOk,lineBytes,lineLen,labelZero,extractLabels,secLocToPc]
end Flapjack.Test.LabToTargetSectionLookupPositionsParity

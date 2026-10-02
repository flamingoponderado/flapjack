import Flapjack.Compiler.Backend.LabToTarget.SectionLookupPreservation
import Flapjack.Compiler.Backend.LabProps.LabelExtractionValidity
namespace Flapjack.Test.LabToTargetLookupPrerequisitesParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabProps.LabelSets Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.LabSem Flapjack.Basis.Pure.MlString
example {width : Nat} [NeZero width] (pos : Nat) (lines : List (LabLineHOL width))
    (acc : List (Nat × Nat)) (key : Nat) :
    key ∉ (extractLabels lines).map Prod.snd →
    sptAListLookup key (sectionLabels pos lines acc).2 = sptAListLookup key acc :=
  sectionLabels_lookup_ignore pos lines acc key
example {width : Nat} [NeZero width] (sid extracted lid : Nat) (lines : List (LabLineHOL width)) :
    (∀ line ∈ lines, secLabelOk sid line) ∧ (extracted,lid) ∈ extractLabels lines →
    extracted = sid ∧ lid ≠ 0 := secLabelOk_extractLabels sid lines extracted lid
example : sptAListLookup 9 (sectionLabels (width := 8) 7 [] [(9,4),(9,6)]).2 = some 4 := by decide +kernel
example : sptAListLookup 3 (sectionLabels (width := 8) 7 [.label 1 2 99,.label 1 2 0] [(9,4)]).2 = none := by decide +kernel
example : sptAListLookup 9 (sectionLabels (width := 8) 7 [.label 1 2 99,.asm (.asmi (.inst .skip)) [] 123,.labAsm .halt 0 [] 456] [(9,4)]).2 = some 4 := by decide +kernel
example : sptAListLookup 9 (sectionLabels (width := 8) 7 [.label 1 9 2] [(9,4)]).2 = some 9 := by decide +kernel
example : sptAListLookup 0 (sectionLabels (width := 8) 7 [.label 1 0 99] [(0,4)]).2 = some 4 := by decide +kernel
example : sptAListLookup 9 (sectionLabels (width := 1) 1208925819614629174706176 [.label 1 2 99] [(9,4)]).2 = some 4 := by decide +kernel
example : sptAListLookup 9 (sectionLabels (width := 80) 1208925819614629174706176 [.label 1 2 99] [(9,4)]).2 = some 4 := by decide +kernel
example : extractLabels (width := 8) [] = [] := rfl
example : (∀ line ∈ ([.label 1 2 99,.asm (.asmi (.inst .skip)) [] 123,.labAsm .halt 0 [] 456,.label 1 2 0] : List (LabLineHOL 8)),secLabelOk 1 line) ∧
    extractLabels (width := 8) [.label 1 2 99,.asm (.asmi (.inst .skip)) [] 123,.labAsm .halt 0 [] 456,.label 1 2 0] = [(1,2),(1,2)] := by simp [secLabelOk,extractLabels]
example : ¬∀ line ∈ ([.label 2 3 0] : List (LabLineHOL 8)),secLabelOk 1 line := by simp [secLabelOk]
example : ¬∀ line ∈ ([.label 1 0 0] : List (LabLineHOL 8)),secLabelOk 1 line := by simp [secLabelOk]
example : ∀ line ∈ ([.label 1208925819614629174706176 2 99] : List (LabLineHOL 1)),secLabelOk 1208925819614629174706176 line := by simp [secLabelOk]
example : ∀ line ∈ ([.label 1 1208925819614629174706176 99] : List (LabLineHOL 80)),secLabelOk 1 line := by simp [secLabelOk]
example (pos : Nat) (acc : List (Nat × Nat)) :
    sptAListLookup 9 (sectionLabels (width := 8) pos [.label 1 2 99] acc).2 = sptAListLookup 9 acc := by
  apply sectionLabels_lookup_ignore
  simp [extractLabels]
example (len : Nat) : 1 = 1 ∧ 2 ≠ 0 := by
  apply secLabelOk_extractLabels 1 ([.label 1 2 len] : List (LabLineHOL 8)) 1 2
  simp [secLabelOk,extractLabels]
end Flapjack.Test.LabToTargetLookupPrerequisitesParity

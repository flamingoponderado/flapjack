import Flapjack.Compiler.Backend.LabToTarget.ComputedLabelPositions
namespace Flapjack.Test.LabToTargetComputedLabelPositionsParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabProps.LabelSets Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {width : Nat} [NeZero width]
    (pos : Nat) (code : List (Section
      (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
        (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (acc : Spt (Spt Nat)) (sectionId labelId pc : Nat) (c : AsmConfigExact width)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) :
    (∀ sec ∈ code, secLabelsOk sec) ∧
    (code.map (fun sec => sec.sectionId)).Nodup ∧
    (∀ sec ∈ code, (extractLabels sec.lines).Nodup) ∧
    (∀ sec ∈ code, secLabelZero sec) ∧
    allEncOk c labs ffis pos code ∧ locToPc sectionId labelId code = some pc →
    labLookup sectionId labelId (computeLabelsAlt pos code acc) = some (posVal pc pos code) := labLookup_computeLabels_position pos code acc sectionId labelId pc c labs ffis
example (pos : Nat) (acc : Spt (Spt Nat)) (c : AsmConfigExact 8)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (henc : allEncOk c labs ffis pos [⟨1,[.label 1 7 0]⟩,⟨2,[]⟩]) :
    labLookup 1 7 (computeLabelsAlt (width := 8) pos [⟨1,[.label 1 7 0]⟩,⟨2,[]⟩] acc) =
      some (posVal (width := 8) 0 pos [⟨1,[.label 1 7 0]⟩,⟨2,[]⟩]) := by
  apply labLookup_computeLabels_position pos _ acc 1 7 0 c labs ffis
  refine ⟨?_,?_,?_,?_,henc,?_⟩ <;>
    simp [secLabelsOk,secLabelOk,extractLabels,secLabelZero,labelZero,locToPc]
example : locToPc (width := 8) 1 0 [⟨1,[]⟩] = some 0 ∧
    labLookup 1 0 (computeLabelsAlt (width := 8) 18 [⟨1,[]⟩] (sptFromAList [(1,sptFromAList [(0,999)])])) = some 18 ∧
    posVal (width := 8) 0 18 [⟨1,[]⟩] = 18 := by decide +kernel
example : locToPc (width := 8) 1 7 [⟨1,[.asm (.asmi (.inst .skip)) [1,2] 2,.label 1 7 0]⟩,⟨2,[]⟩] = some 1 ∧
    labLookup 1 7 (computeLabelsAlt (width := 8) 18 [⟨1,[.asm (.asmi (.inst .skip)) [1,2] 2,.label 1 7 0]⟩,⟨2,[]⟩] (sptFromAList [(1,sptFromAList [(7,999)])])) = some 20 ∧
    posVal (width := 8) 1 18 [⟨1,[.asm (.asmi (.inst .skip)) [1,2] 2,.label 1 7 0]⟩,⟨2,[]⟩] = 20 := by decide +kernel
example : locToPc (width := 8) 1 7 [⟨1,[.label 1 7 0]⟩,⟨2,[.asm (.asmi (.inst .skip)) [1,2] 2]⟩] = some 0 ∧
    labLookup 1 7 (computeLabelsAlt (width := 8) 18 [⟨1,[.label 1 7 0]⟩,⟨2,[.asm (.asmi (.inst .skip)) [1,2] 2]⟩] (sptFromAList [(1,sptFromAList [(7,999)])])) = some 18 ∧
    posVal (width := 8) 0 18 [⟨1,[.label 1 7 0]⟩,⟨2,[.asm (.asmi (.inst .skip)) [1,2] 2]⟩] = 18 := by decide +kernel
example : locToPc (width := 8) 2 7 [⟨1,[.asm (.asmi (.inst .skip)) [1,2] 2]⟩,⟨2,[.label 2 7 0,.labAsm .halt 0 [3,4] 2]⟩] = some 1 ∧
    labLookup 2 7 (computeLabelsAlt (width := 8) 18 [⟨1,[.asm (.asmi (.inst .skip)) [1,2] 2]⟩,⟨2,[.label 2 7 0,.labAsm .halt 0 [3,4] 2]⟩] (sptFromAList [(2,sptFromAList [(7,999)])])) = some 20 ∧
    posVal (width := 8) 1 18 [⟨1,[.asm (.asmi (.inst .skip)) [1,2] 2]⟩,⟨2,[.label 2 7 0,.labAsm .halt 0 [3,4] 2]⟩] = 20 := by decide +kernel
example : locToPc (width := 8) 2 7 [⟨1,[]⟩,⟨2,[.label 2 7 0]⟩] = some 0 ∧
    labLookup 2 7 (computeLabelsAlt (width := 8) 18 [⟨1,[]⟩,⟨2,[.label 2 7 0]⟩] (sptFromAList [(2,sptFromAList [(7,999)])])) = some 18 ∧
    posVal (width := 8) 0 18 [⟨1,[]⟩,⟨2,[.label 2 7 0]⟩] = 18 := by decide +kernel
end Flapjack.Test.LabToTargetComputedLabelPositionsParity

import Flapjack.Compiler.Backend.LabToTarget.LabelExistenceDomain
import Mathlib.Data.Set.Insert
namespace Flapjack.Test.LabToTargetLabelExistenceDomainParity
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabProps.LabelSets
private def labs : Spt (Spt Bool) := sptInsert 3 (sptInsert 4 false .ln) .ln
private def jump : LabLineHOL 8 := .labAsm (.jump (.lab 3 4)) 99 [] 7
private theorem present : lineLabsExist labs jump := by
  simp [lineLabsExist,jump,labsOf,Set.mem_singleton_iff,Prod.mk.injEq,labLookup,labs,sptLookup,sptInsert]
example : lineLabsExist labs jump ∧ lineGetLabels jump ⊆ labsDomain labs :=
  ⟨present,(lineLabsExist_iff_labelsSubset labs jump).mp present⟩
example : ¬lineLabsExist labs (.labAsm (.jump (.lab 5 4)) (99 : BitVec 8) [] 7) ∧
    ¬lineGetLabels (.labAsm (.jump (.lab 5 4)) (99 : BitVec 8) [] 7) ⊆ labsDomain labs := by
  rw [← lineLabsExist_iff_labelsSubset]
  simp [lineLabsExist,labsOf,Set.mem_singleton_iff,Prod.mk.injEq,labLookup,labs,sptLookup,sptInsert]
example : ¬lineLabsExist labs (.labAsm (.locValue 2 (.lab 3 5)) (99 : BitVec 8) [] 7) ∧
    ¬lineGetLabels (.labAsm (.locValue 2 (.lab 3 5)) (99 : BitVec 8) [] 7) ⊆ labsDomain labs := by
  rw [← lineLabsExist_iff_labelsSubset]
  simp [lineLabsExist,labsOf,Set.mem_singleton_iff,Prod.mk.injEq,labLookup,labs,sptLookup,sptInsert]
example : lineLabsExist (.ln : Spt (Spt Bool)) (.labAsm (.call (.lab 88 99)) (99 : BitVec 8) [] 7) ∧
    lineGetLabels (.labAsm (.call (.lab 88 99)) (99 : BitVec 8) [] 7) ⊆ labsDomain (.ln : Spt (Spt Bool)) := by
  simp [lineLabsExist,lineGetLabels,labsOf]
private def lines : List (LabLineHOL 8) := [.label 99 77 42,.asm (.asmi (.inst .skip)) [9] 3,
  jump,.labAsm (.call (.lab 88 99)) 3 [] 17]
private def code : List (Section (LabLineHOL 8)) :=
  [⟨7,lines⟩,⟨8,[.labAsm (.locValue 2 (.lab 3 4)) 0 [7,8] 29]⟩,⟨9,[]⟩]
private theorem sectionPresent : secLabsExist labs ⟨7,lines⟩ := by
  simp [secLabsExist,lines,lineLabsExist,jump,labsOf,Set.mem_singleton_iff,Prod.mk.injEq,labLookup,labs,sptLookup,sptInsert]
private theorem sectionLabels : secGetLabels (Section.mk 7 lines) = {(3,4)} := by
  ext p
  simp [secGetLabels,lines,jump,lineGetLabels,labsOf]
example : secLabsExist labs ⟨7,lines⟩ ∧ secGetLabels (Section.mk 7 lines) = {(3,4)} ∧
    secGetLabels (Section.mk 7 lines) ⊆ labsDomain labs :=
  ⟨sectionPresent,sectionLabels,(secLabsExist_iff_labelsSubset labs ⟨7,lines⟩).mp sectionPresent⟩
private theorem codePresent : allLabsExist labs code := by
  simp [allLabsExist,secLabsExist,code,lines,lineLabsExist,jump,labsOf,Set.mem_singleton_iff,Prod.mk.injEq,labLookup,labs,sptLookup,sptInsert]
private theorem codeLabels : getLabels code = {(3,4)} := by
  ext p
  simp [getLabels,secGetLabels,code,lines,jump,lineGetLabels,labsOf]
example : allLabsExist labs code ∧ getLabels code = {(3,4)} ∧ getLabels code ⊆ labsDomain labs :=
  ⟨codePresent,codeLabels,(allLabsExist_iff_labelsSubset labs code).mp codePresent⟩
example : ¬allLabsExist (sptInsert 3 (.ln : Spt Bool) .ln) code ∧
    ¬getLabels code ⊆ labsDomain (sptInsert 3 (.ln : Spt Bool) .ln) := by
  rw [← allLabsExist_iff_labelsSubset]
  simp [allLabsExist,secLabsExist,code,lines,lineLabsExist,jump,labsOf,Set.mem_singleton_iff,Prod.mk.injEq,labLookup,sptLookup,sptInsert]
example : lineLabsExist (sptInsert 3 (sptInsert 0 false .ln) .ln)
    (.labAsm (.jump (.lab 3 0)) (99 : BitVec 8) [] 7) ∧
    lineGetLabels (.labAsm (.jump (.lab 3 0)) (99 : BitVec 8) [] 7) ⊆
      labsDomain (sptInsert 3 (sptInsert 0 false .ln) .ln) := by
  rw [← lineLabsExist_iff_labelsSubset]
  simp [lineLabsExist,labsOf,Set.mem_singleton_iff,Prod.mk.injEq,labLookup,sptLookup,sptInsert]
example : lineLabsExist (width := 8) labs (.label 88 99 42) ∧
    lineGetLabels (width := 8) (.label 88 99 42) ⊆ labsDomain labs ∧
    lineLabsExist (width := 8) labs (.asm (.asmi (.inst .skip)) [9] 3) ∧
    lineGetLabels (width := 8) (.asm (.asmi (.inst .skip)) [9] 3) ⊆ labsDomain labs := by
  simp [lineLabsExist,lineGetLabels]
example : allLabsExist (width := 1) (.ln : Spt (Spt Bool)) [] ∧
    getLabels (width := 1) [] ⊆ labsDomain (.ln : Spt (Spt Bool)) := by
  simp [allLabsExist,getLabels]
example {α : Type} {width : Nat} [NeZero width] (labs : Spt (Spt α)) (line : LabLineHOL width) :
    lineLabsExist labs line ↔ lineGetLabels line ⊆ labsDomain labs := lineLabsExist_iff_labelsSubset labs line
example {α : Type} {width : Nat} [NeZero width] (labs : Spt (Spt α)) (sec : Section (LabLineHOL width)) :
    secLabsExist labs sec ↔ secGetLabels sec ⊆ labsDomain labs := secLabsExist_iff_labelsSubset labs sec
example {α : Type} {width : Nat} [NeZero width] (labs : Spt (Spt α)) (code : List (Section (LabLineHOL width))) :
    allLabsExist labs code ↔ getLabels code ⊆ labsDomain labs := allLabsExist_iff_labelsSubset labs code
def runChecks : IO Bool := do
  IO.println "PASS full generic-map existence/domain equivalences: ten original observations, missing/present false maps, full label sets, zero-label reference and all three generic consumers"
  pure true
end Flapjack.Test.LabToTargetLabelExistenceDomainParity

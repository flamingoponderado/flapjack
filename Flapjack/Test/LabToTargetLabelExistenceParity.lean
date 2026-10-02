import Mathlib.Data.Set.Insert
import Flapjack.Compiler.Backend.LabToTarget.LabelExistence
namespace Flapjack.Test.LabToTargetLabelExistenceParity
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabProps.LabelSets
private def labs : Spt (Spt Bool) := sptInsert 3 (sptInsert 4 true .ln) .ln
example : lineLabsExist labs (.labAsm (.jump (.lab 3 4)) (99 : BitVec 8) [] 3) := by
  simp [lineLabsExist,labsOf,Set.mem_singleton_iff,Prod.mk.injEq,labLookup,labs,sptLookup,sptInsert]
example : ¬lineLabsExist labs (.labAsm (.jump (.lab 5 4)) (99 : BitVec 8) [] 3) := by
  simp [lineLabsExist,labsOf,Set.mem_singleton_iff,Prod.mk.injEq,labLookup,labs,sptLookup,sptInsert]
example : ¬lineLabsExist labs (.labAsm (.jumpCmp .equal 2 (.imm 1) (.lab 3 5)) (99 : BitVec 8) [] 3) := by
  simp [lineLabsExist,labsOf,Set.mem_singleton_iff,Prod.mk.injEq,labLookup,labs,sptLookup,sptInsert]
example : lineLabsExist (sptInsert 3 (sptInsert 4 false .ln) .ln)
    (.labAsm (.locValue 2 (.lab 3 4)) (99 : BitVec 8) [] 3) := by
  simp [lineLabsExist,labsOf,Set.mem_singleton_iff,Prod.mk.injEq,labLookup,sptLookup,sptInsert]
example : lineLabsExist (.ln : Spt (Spt Bool)) (.labAsm (.call (.lab 99 88)) (99 : BitVec 8) [] 3) := by
  simp [lineLabsExist,labsOf]
example : lineLabsExist (width := 8) labs (.label 1 2 99) ∧
    lineLabsExist (width := 8) labs (.asm (.asmi (.inst .skip)) [7] 3) := ⟨trivial,trivial⟩
private def c1 : List (Section (LabLineHOL 8)) :=
  [⟨7,[.label 1 2 9,.labAsm (.jump (.lab 3 4)) 99 [] 3]⟩,⟨8,[]⟩]
private def c2 : List (Section (LabLineHOL 8)) :=
  [⟨7,[.label 1 2 0,.labAsm (.jump (.lab 3 4)) 1 [7,8] 12]⟩,⟨8,[]⟩]
private theorem similar : codeSimilar c1 c2 :=
  ⟨⟨True.intro,.nil,rfl⟩,.cons ⟨rfl,rfl⟩ (.cons rfl .nil),rfl⟩
private theorem present : allLabsExist labs c1 := by
  simp [allLabsExist,secLabsExist,lineLabsExist,c1,labsOf,Set.mem_singleton_iff,Prod.mk.injEq,labLookup,labs,sptLookup,sptInsert]
example : codeSimilar c1 c2 ∧ allLabsExist labs c1 ∧ allLabsExist labs c2 :=
  ⟨similar,present,(codeSimilar_allLabsExist labs c1 c2 similar).mp present⟩
example : allLabsExist labs (padCode [] c1) ∧ allLabsExist labs (padCode [7,8] c1) :=
  ⟨(allLabsExist_padCode labs [] c1).mpr present,(allLabsExist_padCode labs [7,8] c1).mpr present⟩
example : allLabsExist labs (updLabLen 17 c1) := (allLabsExist_updLabLen labs 17 c1).mpr present
example : allLabsExist (width := 1) (.ln : Spt (Spt Bool)) [] := by simp [allLabsExist]
example {α : Type} {width : Nat} [NeZero width] (labs : Spt (Spt α))
    (c1 c2 : List (Section (LabLineHOL width))) :
    codeSimilar c1 c2 → (allLabsExist labs c1 ↔ allLabsExist labs c2) :=
  codeSimilar_allLabsExist labs c1 c2
example {α : Type} {width : Nat} [NeZero width] (labs : Spt (Spt α))
    (nop : List (BitVec 8)) (pos : Nat) (code : List (Section (LabLineHOL width))) :
    (allLabsExist labs (padCode nop code) ↔ allLabsExist labs code) ∧
    (allLabsExist labs (updLabLen pos code) ↔ allLabsExist labs code) :=
  ⟨allLabsExist_padCode labs nop code,allLabsExist_updLabLen labs pos code⟩
def runChecks : IO Bool := do
  IO.println "PASS generic-map label existence and full similarity/padding/update preservation: ten original observations, missing/present false values, original Call nonreference"
  pure true
end Flapjack.Test.LabToTargetLabelExistenceParity

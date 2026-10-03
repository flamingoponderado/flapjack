import Flapjack.Compiler.Backend.LabToTarget.MmioShmem
import Flapjack.Compiler.Backend.LabSem.State
namespace Flapjack.Test.LabToTargetMmioShmemParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example (l ffis : List HolFfiName) :
    (∀ x ∈ l, ∀ s, x ≠ HolFfiName.extCall s) ∧
    (∀ x ∈ ffis, ∃ s, x = HolFfiName.extCall s) →
    mmioPcsMinIndex (ffis++l) = some ffis.length :=
  mmioPcsMinIndex_append l ffis

example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (validFfis : List HolFfiName)
    (validPos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (ffis : List HolFfiName) (p : Nat) (newFfiNames : List HolFfiName)
    (newShmemInfo : List ShmemInfoNum) :
    allEncOk c labs validFfis validPos code ∧ encOk c ∧
    (∀ x ∈ ffis, ∃ s, x = HolFfiName.extCall s) ∧
    getShmemInfo code p ffis [] = (newFfiNames,newShmemInfo) →
    mmioPcsMinIndex newFfiNames = some ffis.length :=
  mmioPcsMinIndex_getShmemInfo c labs validFfis validPos code ffis p newFfiNames newShmemInfo

private def guest := HolFfiName.extCall (ofString "guest")
example : mmioPcsMinIndex [] = some 0 := by
  simpa using mmioPcsMinIndex_append [] [] ⟨by simp,by simp⟩
example : mmioPcsMinIndex [guest] = some 1 := by
  simpa [guest] using mmioPcsMinIndex_append [] [guest] ⟨by simp,by simp [guest]⟩
example : mmioPcsMinIndex [.sharedMem .mappedRead] = some 0 := by
  simpa using mmioPcsMinIndex_append [.sharedMem .mappedRead] [] ⟨by simp,by simp⟩
example : mmioPcsMinIndex [guest,guest,.sharedMem .mappedRead,.sharedMem .mappedWrite] = some 2 := by
  simpa using mmioPcsMinIndex_append [.sharedMem .mappedRead,.sharedMem .mappedWrite] [guest,guest]
    ⟨by simp,by simp [guest]⟩
example : ¬(∀ x ∈ [guest], ∀ s, x ≠ HolFfiName.extCall s) := by simp [guest]
example : ¬(∀ x ∈ [HolFfiName.sharedMem .mappedRead], ∃ s, x = HolFfiName.extCall s) := by simp
private def cfg {width : Nat} [NeZero width] (alignment : Nat) (bytes : List (BitVec 8)) : AsmConfigExact width :=
  { isa := .riscv, encode := fun _ => bytes, bigEndian := false, codeAlignment := alignment,
    linkReg := some 7, avoidRegs := [], regCount := 8, fpRegCount := 4,
    twoRegArith := false, validImm := fun _ _ => true,
    addrOffset := (128,127), hwOffset := (128,127), byteOffset := (128,127),
    jumpOffset := (128,127), cjumpOffset := (128,127), locOffset := (128,127) }
private def old : Spt (Spt Nat) := sptFromAList [(1,sptFromAList [(7,20)])]
private def load : LabLineHOL 8 := .asm (.shareMem .load8 3 (.addr 2 5)) [0,0] 2
private def store : LabLineHOL 8 := .asm (.shareMem .store8 4 (.addr 2 (-1))) [0,0] 2
private def code : LabProgHOL 8 :=
  [⟨0,[]⟩,⟨1,[.label 1 7 0,load,.asm (.cbw 1 2) [0,0] 2,
    .labAsm (.jump (.lab 1 7)) 99 [0,0] 2,.label 1 7 0]⟩,
    ⟨2,[store,.asm (.asmi (.inst .skip)) [0,0] 2]⟩,⟨0,[]⟩]
private theorem configOk : encOk (cfg (width := 8) 1 [0,0]) := by
  simp [encOk,offsetMonotonic,cfg]
example (p : Nat) : mmioPcsMinIndex (getShmemInfo code p [guest] []).1 = some 1 :=
  mmioPcsMinIndex_getShmemInfo (cfg (width := 8) 1 [0,0]) old [] 18 code [guest] p
    (getShmemInfo code p [guest] []).1 (getShmemInfo code p [guest] []).2
    ⟨by cbv,configOk,by simp [guest],by cases getShmemInfo code p [guest] []; rfl⟩
example : mmioPcsMinIndex (getShmemInfo code 7 [guest] []).1 = some 1 :=
  mmioPcsMinIndex_getShmemInfo (cfg (width := 8) 1 [0,0]) old [] 18 code [guest] 7
    (getShmemInfo code 7 [guest] []).1 (getShmemInfo code 7 [guest] []).2
    ⟨by cbv,configOk,by simp [guest],by cases getShmemInfo code 7 [guest] []; rfl⟩
end Flapjack.Test.LabToTargetMmioShmemParity

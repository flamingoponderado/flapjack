import Flapjack.Compiler.Backend.LabToTarget.ShmemEntryMax
namespace Flapjack.Test.LabToTargetShmemEntryMaxParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    allEncOk c labs ffis validPos code ∧ encOk c →
    ∀ x ∈ ((List.range (numPcs code)).map
      (fun i => lineToInfo code 0 (i,asmFetchAux i code))).flatten,
      x.2.entryPc < posVal (numPcs code) 0 code := genlistLineToInfo_entryPcMax c labs ffis validPos code
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
example (validPos : Nat) (hv : allEncOk (cfg (width := 8) 1 [0,0]) old [] validPos code) :
    ∀ x ∈ ((List.range (numPcs code)).map
      (fun i => lineToInfo code 0 (i,asmFetchAux i code))).flatten,
      x.2.entryPc < posVal (numPcs code) 0 code :=
  genlistLineToInfo_entryPcMax (cfg (width := 8) 1 [0,0]) old [] validPos code
    ⟨hv,by simp [encOk,offsetMonotonic,cfg]⟩
example : (((List.range (numPcs code)).map
    (fun i => lineToInfo code 0 (i,asmFetchAux i code))).flatten.map
    (fun x => x.2.entryPc)) = [0,6] := by cbv
example : posVal (numPcs code) 0 code = 10 := by cbv
end Flapjack.Test.LabToTargetShmemEntryMaxParity

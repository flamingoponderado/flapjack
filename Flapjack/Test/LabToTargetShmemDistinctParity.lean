import Flapjack.Compiler.Backend.LabToTarget.ShmemDistinct
namespace Flapjack.Test.LabToTargetShmemDistinctParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos p : Nat) :
    (progToBytes code).length < 2^width ∧ encOk c ∧ allEncOk c labs ffis validPos code →
    ((getShmemInfo code p [] []).2.map ShmemInfoNum.entryPc).Nodup :=
  getShmemInfo_entryDistinct code c labs ffis validPos p
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
private def initialNames : List HolFfiName := [.sharedMem .mappedWrite]
private def initialInfo : ShmemInfoNum :=
  {entryPc:=100,nbytes:=3,addrReg:=99,addrOff:=42,reg:=77,exitPc:=103}
private def loadInfo : ShmemInfoNum :=
  {entryPc:=7,nbytes:=1,addrReg:=2,addrOff:=5,reg:=3,exitPc:=9}
private def storeInfo : ShmemInfoNum :=
  {entryPc:=13,nbytes:=1,addrReg:=2,addrOff:=255,reg:=4,exitPc:=15}
private def extracted {width : Nat} [NeZero width] (code : LabProgHOL width) (p : Nat) :=
  (((List.range (numPcs code)).map (fun i=>(i,asmFetchAux i code))).map (lineToInfo code p)).flatten.unzip

example (p : Nat) : ((getShmemInfo code p [] []).2.map ShmemInfoNum.entryPc).Nodup :=
  getShmemInfo_entryDistinct code (cfg (width := 8) 1 [0,0]) old [] 18 p (by refine ⟨by cbv, ?_, by cbv⟩; simp [encOk,offsetMonotonic,cfg])
example : ((getShmemInfo code 7 [] []).2.map ShmemInfoNum.entryPc) = [7,13] := by cbv
example : ((getShmemInfo code 1000 [] []).2.map ShmemInfoNum.entryPc).Nodup := by cbv <;> decide
example : ((getShmemInfo ([] : LabProgHOL 8) 7 [] []).2.map ShmemInfoNum.entryPc).Nodup := by cbv <;> decide
private def zero : LabProgHOL 8 :=
  [⟨1,[.asm (.shareMem .load8 3 (.addr 2 5)) [] 0,
    .asm (.shareMem .store8 4 (.addr 2 5)) [] 0]⟩]
example : allEncOk (cfg (width := 8) 1 []) old [] 18 zero := by cbv
example : ¬encOk (cfg (width := 8) 1 []) := by cbv
example : ¬((getShmemInfo zero 7 [] []).2.map ShmemInfoNum.entryPc).Nodup := by cbv <;> decide
end Flapjack.Test.LabToTargetShmemDistinctParity

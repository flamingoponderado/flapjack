import Flapjack.Compiler.Backend.LabToTarget.ShmemMembership
namespace Flapjack.Test.LabToTargetShmemMembershipParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (pc : Nat) (op : HolMemop) (reg : Nat) (addr : HolAddr width)
    (bytes : List (BitVec 8)) (len : Nat) (name : HolShmemOp) (nbytes : BitVec 8) (p : Nat) :
    allEncOk c labs ffis validPos code ∧
    asmFetchAux pc code = some (.asm (.shareMem op reg addr) bytes len) ∧
    getMemopInfo op = (name,nbytes) →
    (.sharedMem name,
      {entryPc:=posVal pc p code,nbytes:=nbytes,
       addrReg:=match addr with | .addr base _ => base,
       addrOff:=match addr with | .addr _ off => off.toNat,
       reg:=reg,exitPc:=posVal pc (p+bytes.length) code}) ∈
      List.zip (getShmemInfo code p [] []).1 (getShmemInfo code p [] []).2 :=
  getShmemInfo_mem c labs ffis validPos code pc op reg addr bytes len name nbytes p

example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (p : Nat) :
    allEncOk c labs ffis validPos code →
    (getShmemInfo code p [] []).1.length = (getShmemInfo code p [] []).2.length :=
  getShmemInfo_emptyLengthEq c labs ffis validPos code p

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
example : (.sharedMem .mappedRead,loadInfo) ∈
    List.zip (getShmemInfo code 7 [] []).1 (getShmemInfo code 7 [] []).2 := by simp [getShmemInfo,code,load,store,loadInfo,getMemopInfo,ShmemInfoNum.mk.injEq]
example : (.sharedMem .mappedWrite,storeInfo) ∈
    List.zip (getShmemInfo code 7 [] []).1 (getShmemInfo code 7 [] []).2 := by simp [getShmemInfo,code,load,store,storeInfo,getMemopInfo,ShmemInfoNum.mk.injEq]
example : asmFetchAux 0 code = some load := by cbv
example : posVal 0 (7+2) code = 9 := by cbv
example (p : Nat) : (.sharedMem .mappedRead,
      {entryPc:=posVal 0 p code,nbytes:=1,addrReg:=2,addrOff:=5,reg:=3,
       exitPc:=posVal 0 (p+2) code}) ∈
    List.zip (getShmemInfo code p [] []).1 (getShmemInfo code p [] []).2 :=
  getShmemInfo_mem (cfg (width := 8) 1 [0,0]) old [] 18 code 0 .load8 3 (.addr 2 5)
    [0,0] 2 .mappedRead 1 p ⟨by cbv,by cbv,by cbv⟩
example (p : Nat) : (getShmemInfo code p [] []).1.length = (getShmemInfo code p [] []).2.length :=
  getShmemInfo_emptyLengthEq (cfg (width := 8) 1 [0,0]) old [] 18 code p (by cbv)
example : (getShmemInfo code 7 [] []).1.length = 2 ∧ (getShmemInfo code 7 [] []).2.length = 2 := by cbv
example : (getShmemInfo ([] : LabProgHOL 8) 7 [] []).1.length = (getShmemInfo ([] : LabProgHOL 8) 7 [] []).2.length := by cbv
example : (.sharedMem .mappedRead,storeInfo) ∉
    List.zip (getShmemInfo code 7 [] []).1 (getShmemInfo code 7 [] []).2 := by simp [getShmemInfo,code,load,store,storeInfo,getMemopInfo,ShmemInfoNum.mk.injEq]
end Flapjack.Test.LabToTargetShmemMembershipParity

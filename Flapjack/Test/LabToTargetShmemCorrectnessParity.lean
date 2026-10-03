import Flapjack.Compiler.Backend.LabToTarget.ShmemCorrectness
namespace Flapjack.Test.LabToTargetShmemCorrectnessParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private instance : Nonempty HolFfiName := ⟨.sharedMem .mappedRead⟩
private instance : Nonempty ShmemInfoNum := ⟨⟨0,0,0,0,0,0⟩⟩
example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (validFfis : List HolFfiName)
    (validPos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (ffis : List HolFfiName) (p : Nat)
    (newFfiNames : List HolFfiName) (newShmemInfo : List ShmemInfoNum) :
    allEncOk c labs validFfis validPos code ∧ encOk c ∧
      (progToBytes code).length < 2^width ∧
      (∀ x ∈ ffis, ∃ name, x = HolFfiName.extCall name) ∧
      getShmemInfo code p ffis [] = (newFfiNames,newShmemInfo) →
    (∀ pc op reg addr bytes len i,
      asmFetchAux pc code = some (.asm (.shareMem op reg addr) bytes len) ∧
        mmioPcsMinIndex newFfiNames = some i →
      ∃ index, Flapjack.Misc.findIndex (p+posVal pc 0 code)
          (newShmemInfo.map ShmemInfoNum.entryPc) 0 = some index ∧
        (let (name,nb) := getMemopInfo op
         holEl (index+i) newFfiNames = .sharedMem name ∧
         holEl index newShmemInfo =
           {entryPc:=(holEl index newShmemInfo).entryPc,nbytes:=nb,
            addrReg:=match addr with | .addr base _ => base,
            addrOff:=match addr with | .addr _ off => off.toNat,
            reg:=reg,exitPc:=p+(posVal pc 0 code+len)})) ∧
    (∀ pc line, asmFetchAux pc code = some line ∧
      (∀ op reg addr bytes len, line ≠ .asm (.shareMem op reg addr) bytes len) →
      Disjoint ({n | n ∈ newShmemInfo.map ShmemInfoNum.entryPc} : Set Nat)
        {n | ∃ a, a < (lineBytes line).length ∧ n = p+a+posVal pc 0 code}) := getShmemInfo_ok c labs validFfis validPos code ffis p newFfiNames newShmemInfo
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

/-- Actual full theorem consumer with arbitrary query position and external
prefix name. The original encoding/size/prefix guards are discharged here. -/
 noncomputable def actualFullConsumer (p : Nat) (guest : MlString) :=
  getShmemInfo_ok (cfg (width := 8) 1 [0,0]) old [] 18 code [.extCall guest] p
    (getShmemInfo code p [.extCall guest] []).1
    (getShmemInfo code p [.extCall guest] []).2
    ⟨by cbv,by simp [encOk,offsetMonotonic,cfg],by cbv,by simp,rfl⟩
end Flapjack.Test.LabToTargetShmemCorrectnessParity

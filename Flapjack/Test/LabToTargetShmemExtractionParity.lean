import Flapjack.Compiler.Backend.LabToTarget.ShmemExtraction
namespace Flapjack.Test.LabToTargetShmemExtractionParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {width : Nat} [NeZero width]
    (secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (p : Nat) (ffiNames : List HolFfiName)
    (shmemInfo : List ShmemInfoNum) (validPos : Nat) (c : AsmConfigExact width)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) :
    allEncOk c labs ffis validPos secs →
    getShmemInfo secs p ffiNames shmemInfo =
      let (newFfis,newInfo) :=
        (((List.range (numPcs secs)).map (fun i => (i,asmFetchAux i secs))).map
          (lineToInfo secs p)).flatten.unzip
      (ffiNames ++ newFfis,shmemInfo ++ newInfo) :=
  getShmemInfo_characterization secs p ffiNames shmemInfo validPos c labs ffis
private def cfg {width : Nat} [NeZero width] (alignment : Nat) (bytes : List (BitVec 8)) : AsmConfigExact width :=
  { isa := .riscv, encode := fun _ => bytes, bigEndian := false, codeAlignment := alignment,
    linkReg := some 7, avoidRegs := [], regCount := 8, fpRegCount := 4,
    twoRegArith := false, validImm := fun _ _ => true,
    addrOffset := (128,127), hwOffset := (128,127), byteOffset := (128,127),
    jumpOffset := (128,127), cjumpOffset := (128,127), locOffset := (128,127) }
private def old : Spt (Spt Nat) := sptFromAList [(1,sptFromAList [(7,20)])]
private def extra := sptInsert 99 (sptFromAList [(8,24)]) old
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
example : allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 code := by cbv
example : getShmemInfo code 7 initialNames [initialInfo] =
    (initialNames ++ [.sharedMem .mappedRead,.sharedMem .mappedWrite],[initialInfo,loadInfo,storeInfo]) := by cbv
example : getShmemInfo code 7 [] [] = extracted code 7 := by cbv
example : getShmemInfo ([] : LabProgHOL 8) 1000 initialNames [initialInfo] =
    (initialNames,[initialInfo]) := by cbv
example : getShmemInfo ([⟨0,[]⟩,⟨1,[.label 1 2 0]⟩] : LabProgHOL 8) 7 initialNames [initialInfo] =
    (initialNames,[initialInfo]) := by cbv
private def wide : LabProgHOL 80 :=
  [⟨1,[.asm (.shareMem .store8 4 (.addr 2 (-1))) [0,0] 2]⟩]
private def wideCfg : AsmConfigExact 80 :=
  { (cfg (width := 80) 1 [0,0]) with addrOffset:=(-128,127), hwOffset:=(-128,127), byteOffset:=(-128,127),jumpOffset:=(-128,127),cjumpOffset:=(-128,127),locOffset:=(-128,127) }
example : allEncOk wideCfg old [] 18 wide ∧
    getShmemInfo wide 1000 [] [] =
      ([.sharedMem .mappedWrite],[{entryPc:=1000,nbytes:=1,addrReg:=2, addrOff:=1208925819614629174706175,reg:=4,exitPc:=1002}]) := by cbv
private def bad : LabProgHOL 8 := [⟨1,[.label 1 7 99,load]⟩]
example : ¬allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 bad ∧
    getShmemInfo bad 7 [] [] ≠ extracted bad 7 := by cbv <;> decide
/-- Actual application keeps arbitrary prefixes and an arbitrary queried start,
while discharging the complete source encoding guard at the independent18. -/
example (p : Nat) (names : List HolFfiName) (infos : List ShmemInfoNum) :
    getShmemInfo code p names infos =
      (names++(extracted code p).1,infos++(extracted code p).2) := by
  have h := getShmemInfo_characterization code p names infos 18
    (cfg (width := 8) 1 [0,0]) old [] (by cbv)
  simpa only [extracted,List.unzip_eq_map] using h
end Flapjack.Test.LabToTargetShmemExtractionParity

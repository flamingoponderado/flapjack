import Flapjack.Compiler.Backend.LabToTarget.ShmemPrefix
namespace Flapjack.Test.LabToTargetShmemPrefixParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {width : Nat} [NeZero width]
    (secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (pos : Nat) (ffiNames : List HolFfiName) (shmemInfo : List ShmemInfoNum)
    (ffis1 ffis2 : List HolFfiName) (info1 info2 : List ShmemInfoNum)
    (newFfiNames : List HolFfiName) (newShmemInfo : List ShmemInfoNum) :
    getShmemInfo secs pos ffiNames shmemInfo = (newFfiNames,newShmemInfo) ∧
    ffiNames = ffis1++ffis2 ∧ shmemInfo = info1++info2 →
    newFfiNames = ffis1++(getShmemInfo secs pos ffis2 info2).1 ∧
    newShmemInfo = info1++(getShmemInfo secs pos ffis2 info2).2 :=
  getShmemInfo_append secs pos ffiNames shmemInfo ffis1 ffis2 info1 info2 newFfiNames newShmemInfo

example {width : Nat} [NeZero width]
    (secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (pos : Nat) (ffiNames : List HolFfiName) (shmemInfo : List ShmemInfoNum)
    (newFfiNames : List HolFfiName) (newShmemInfo : List ShmemInfoNum) :
    getShmemInfo secs pos ffiNames shmemInfo = (newFfiNames,newShmemInfo) →
    newFfiNames = ffiNames++(getShmemInfo secs pos [] []).1 ∧
    newShmemInfo = shmemInfo++(getShmemInfo secs pos [] []).2 :=
  getShmemInfo_prepend secs pos ffiNames shmemInfo newFfiNames newShmemInfo

private def code {width : Nat} [NeZero width] :
    List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :=
  [Section.mk 0 [],⟨1,[Line.label 1 7 99,
    .asm (.shareMem .load8 3 (.addr 2 5)) [] 0,
    .asm (.cbw 1 2) [0,0] 42,
    .labAsm (.jump (.lab 1 7)) (99 : BitVec width) [0] 10,
    .asm (.shareMem .store8 4 (.addr 2 (-1))) [0,0] 2]⟩]
private def initial : ShmemInfoNum :=
  {entryPc:=100,nbytes:=3,addrReg:=99,addrOff:=42,reg:=77,exitPc:=103}
example (p : Nat) (names : List HolFfiName) (infos : List ShmemInfoNum) :
    (getShmemInfo (code (width := 80)) p names infos).1 =
      names++(getShmemInfo (code (width := 80)) p [] []).1 ∧
    (getShmemInfo (code (width := 80)) p names infos).2 =
      infos++(getShmemInfo (code (width := 80)) p [] []).2 :=
  getShmemInfo_prepend _ p names infos _ _ (by cases getShmemInfo (code (width := 80)) p names infos; rfl)
example : getShmemInfo (code (width := 8)) 7 [.sharedMem .mappedWrite] [initial] =
    ([.sharedMem .mappedWrite,.sharedMem .mappedRead,.sharedMem .mappedWrite],
      [initial,{entryPc:=7,nbytes:=1,addrReg:=2,addrOff:=5,reg:=3,exitPc:=7},
        {entryPc:=10,nbytes:=1,addrReg:=2,addrOff:=255,reg:=4,exitPc:=12}]) := by cbv
example : (getShmemInfo (code (width := 80)) 1000 [] []).2.map ShmemInfoNum.addrOff =
    [5,1208925819614629174706175] := by cbv
example : (getShmemInfo (code (width := 1)) 7 [] []).2.map ShmemInfoNum.addrOff = [1,1] := by cbv
example (p : Nat) (names : List HolFfiName) (infos : List ShmemInfoNum) :
    getShmemInfo ([] : List (Section (Line (AsmOrCbw (HolAsm 8) HolMemop (HolAddr 8))
      (AsmWithLab HolCmp (HolRegImm 8) MlString) (BitVec 8)))) p names infos = (names,infos) := by
  simp only [getShmemInfo]
example : (getShmemInfo (code (width := 8)) 7 [.sharedMem .mappedWrite] [initial]).1 =
    [.sharedMem .mappedWrite]++(getShmemInfo (code (width := 8)) 7 [] []).1 := by cbv
example : (getShmemInfo (code (width := 8)) 7 [.sharedMem .mappedWrite] [initial]).2 =
    [initial]++(getShmemInfo (code (width := 8)) 7 [] []).2 := by cbv
example : getShmemInfo (code (width := 8)) 7
    ([.sharedMem .mappedWrite]++[.extCall (ofString "guest")]) ([initial]++[initial]) =
    ([.sharedMem .mappedWrite]++(getShmemInfo (code (width := 8)) 7 [.extCall (ofString "guest")] [initial]).1,
     [initial]++(getShmemInfo (code (width := 8)) 7 [.extCall (ofString "guest")] [initial]).2) := by cbv
end Flapjack.Test.LabToTargetShmemPrefixParity

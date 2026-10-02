import Flapjack.Compiler.Backend.LabToTarget.ShmemNames
namespace Flapjack.Test.LabToTargetShmemNamesParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {width : Nat} [NeZero width]
    (secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (pos : Nat) (ffiNames : List HolFfiName) (info : List ShmemInfoNum)
    (newFfiNames : List HolFfiName) (newInfo : List ShmemInfoNum) :
    getShmemInfo secs pos ffiNames info = (newFfiNames,newInfo) →
    ∃ l, newFfiNames = ffiNames++l ∧
      ∀ x ∈ l, ∃ op, x = HolFfiName.sharedMem op :=
  getShmemInfo_mappedNames secs pos ffiNames info newFfiNames newInfo
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
example : (getShmemInfo (code (width := 1)) 7 [] []).1 =
    [.sharedMem .mappedRead,.sharedMem .mappedWrite] := by cbv
example : (getShmemInfo (code (width := 8)) 7 [] []).1 =
    [.sharedMem .mappedRead,.sharedMem .mappedWrite] := by cbv
example : (getShmemInfo (code (width := 80)) 7 [] []).1 =
    [.sharedMem .mappedRead,.sharedMem .mappedWrite] := by cbv
example (p : Nat) (names : List HolFfiName) (infos : List ShmemInfoNum) :
    ∃ l, (getShmemInfo (code (width := 80)) p names infos).1 = names++l ∧
      ∀ x ∈ l, ∃ op, x = HolFfiName.sharedMem op :=
  getShmemInfo_mappedNames _ p names infos
    (getShmemInfo (code (width := 80)) p names infos).1
    (getShmemInfo (code (width := 80)) p names infos).2
    (by cases getShmemInfo (code (width := 80)) p names infos; rfl)
example : (getShmemInfo (code (width := 8)) 7 [.extCall (ofString "guest")] [initial]).1 =
    [.extCall (ofString "guest"),.sharedMem .mappedRead,.sharedMem .mappedWrite] := by cbv
private def allOps : List HolMemop := [.load,.load32,.load16,.load8,.store,.store32,.store16,.store8]
private def allCode : List (Section (Line (AsmOrCbw (HolAsm 8) HolMemop (HolAddr 8))
    (AsmWithLab HolCmp (HolRegImm 8) MlString) (BitVec 8))) :=
  [⟨1,allOps.map (fun op => .asm (.shareMem op 3 (.addr 2 5)) [] 0)⟩]
example : (getShmemInfo allCode 7 [] []).1 =
    [.sharedMem .mappedRead,.sharedMem .mappedRead,.sharedMem .mappedRead,.sharedMem .mappedRead,
     .sharedMem .mappedWrite,.sharedMem .mappedWrite,.sharedMem .mappedWrite,.sharedMem .mappedWrite] := by cbv
private def ffiOnly : List (Section (Line (AsmOrCbw (HolAsm 8) HolMemop (HolAddr 8))
    (AsmWithLab HolCmp (HolRegImm 8) MlString) (BitVec 8))) :=
  [⟨1,[.labAsm (.callFFI (ofString "guest")) 99 [0] 42]⟩]
example : getShmemInfo ffiOnly 7 [] [] = ([],[]) := by cbv
example : getShmemInfo ([] : List (Section (Line (AsmOrCbw (HolAsm 8) HolMemop (HolAddr 8))
    (AsmWithLab HolCmp (HolRegImm 8) MlString) (BitVec 8)))) 7 [.sharedMem .mappedWrite] [initial] =
    ([.sharedMem .mappedWrite],[initial]) := by cbv
end Flapjack.Test.LabToTargetShmemNamesParity

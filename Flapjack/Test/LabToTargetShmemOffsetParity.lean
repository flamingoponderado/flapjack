import Flapjack.Compiler.Backend.LabToTarget.ShmemOffset
namespace Flapjack.Test.LabToTargetShmemOffsetParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {codeWidth : Nat} {fetchedWidth : Nat}
    [NeZero codeWidth] [NeZero fetchedWidth]
    (code : List (Section (Line (AsmOrCbw (HolAsm codeWidth) HolMemop (HolAddr codeWidth))
      (AsmWithLab HolCmp (HolRegImm codeWidth) MlString) (BitVec codeWidth)))) (p : Nat)
    (accum : Nat × Option (Line (AsmOrCbw (HolAsm fetchedWidth) HolMemop (HolAddr fetchedWidth))
      (AsmWithLab HolCmp (HolRegImm fetchedWidth) MlString) (BitVec fetchedWidth))) :
    (lineToInfo code p accum).map Prod.fst =
      (lineToInfo code 0 accum).map Prod.fst := lineToInfo_offsetNames code p accum
example {codeWidth : Nat} {fetchedWidth : Nat}
    [NeZero codeWidth] [NeZero fetchedWidth]
    (code : List (Section (Line (AsmOrCbw (HolAsm codeWidth) HolMemop (HolAddr codeWidth))
      (AsmWithLab HolCmp (HolRegImm codeWidth) MlString) (BitVec codeWidth)))) (p : Nat)
    (accum : Nat × Option (Line (AsmOrCbw (HolAsm fetchedWidth) HolMemop (HolAddr fetchedWidth))
      (AsmWithLab HolCmp (HolRegImm fetchedWidth) MlString) (BitVec fetchedWidth))) :
    (lineToInfo code p accum).map Prod.snd =
      (lineToInfo code 0 accum).map (fun x =>
        {x.2 with entryPc:=p+x.2.entryPc,exitPc:=p+x.2.exitPc}) := lineToInfo_offsetRecords code p accum
example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (p : Nat) :
    allEncOk c labs ffis validPos code →
      (getShmemInfo code 0 [] []).1 = (getShmemInfo code p [] []).1 ∧
      ((getShmemInfo code 0 [] []).2.map (fun record =>
        {record with entryPc:=p+record.entryPc,exitPc:=p+record.exitPc})) =
        (getShmemInfo code p [] []).2 := getShmemInfo_initPcOffset c labs ffis validPos code p
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
example (p : Nat) :
    (getShmemInfo code 0 [] []).1 = (getShmemInfo code p [] []).1 ∧
    ((getShmemInfo code 0 [] []).2.map (fun r =>
      {r with entryPc:=p+r.entryPc,exitPc:=p+r.exitPc})) = (getShmemInfo code p [] []).2 :=
  getShmemInfo_initPcOffset (cfg (width := 8) 1 [0,0]) old [] 18 code p (by cbv)
private def fetched : Option (LabLineHOL 80) :=
  some (.asm (.shareMem .store8 4 (.addr 2 (-1))) [0,0] 2)
example : (lineToInfo code 7 (3,fetched)).map Prod.fst =
    (lineToInfo code 0 (3,fetched)).map Prod.fst := lineToInfo_offsetNames code 7 _
end Flapjack.Test.LabToTargetShmemOffsetParity

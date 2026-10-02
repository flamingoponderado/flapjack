import Flapjack.Compiler.Backend.LabToTarget.PositionOrder
namespace Flapjack.Test.LabToTargetPositionOrderParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {width : Nat} [NeZero width]
    (pc : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (x : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    asmFetchAux pc code = some x → pc < numPcs code :=
  asmFetchAux_some_ltNumPcs pc code x

example {width : Nat} [NeZero width]
    (i p : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : p ≤ posVal i p code :=
  posVal_geStart i p code

example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (l : HolAsm width) :
    encOk c → 0 < (c.encode l).length :=
  encOk_lengthPositive c l

example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (p : Nat) :
    allEncOk c labs ffis validPos code →
    posVal (numPcs code) p code = p + (progToBytes code).length :=
  posVal_numPcs c labs ffis validPos code p

example {width : Nat} [NeZero width]
    (pc p : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    numPcs code ≤ pc → posVal (numPcs code) p code = posVal pc p code :=
  posVal_geNumPcs pc p code

example {width : Nat} [NeZero width]
    (i p : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (j validPos : Nat)
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName) :
    i < j ∧ j ≤ numPcs code ∧ allEncOk c labs ffis validPos code ∧ encOk c →
    posVal i p code < posVal j p code :=
  posVal_mono i p code j validPos c labs ffis

example {width : Nat} [NeZero width]
    (i p : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (j : Nat)
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos : Nat) :
    posVal i p code < posVal j p code ∧ i ≤ numPcs code ∧
      allEncOk c labs ffis validPos code ∧ encOk c → i < j :=
  posVal_monoInv i p code j c labs ffis validPos

example {width : Nat} [NeZero width]
    (i p : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (j : Nat)
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos : Nat) :
    posVal i p code = posVal j p code ∧ i ≤ numPcs code ∧ j ≤ numPcs code ∧
      allEncOk c labs ffis validPos code ∧ encOk c → i = j :=
  posVal_inj i p code j c labs ffis validPos

private def cfg {width : Nat} [NeZero width] (alignment : Nat) (bytes : List (BitVec 8)) : AsmConfigExact width :=
  { isa := .riscv, encode := fun _ => bytes, bigEndian := false, codeAlignment := alignment,
    linkReg := some 7, avoidRegs := [], regCount := 8, fpRegCount := 4,
    twoRegArith := false, validImm := fun _ _ => true,
    addrOffset := (128,127), hwOffset := (128,127), byteOffset := (128,127),
    jumpOffset := (128,127), cjumpOffset := (128,127), locOffset := (128,127) }
private def old : Spt (Spt Nat) := sptFromAList [(1,sptFromAList [(7,20)])]
private def extra := sptInsert 99 (sptFromAList [(8,24)]) old
private def jumpCode : List (Section (LabLineHOL 8)) :=
  [⟨1,[.labAsm (.jump (.lab 1 7)) 99 [0,0] 2,.label 1 7 0]⟩]
private def asmCode : List (Section (LabLineHOL 8)) :=
  [⟨2,[.asm (.asmi (.inst .skip)) [0,0] 2,.label 2 8 0]⟩]

private def jump : LabLineHOL 8 := .labAsm (.jump (.lab 1 7)) 99 [0,0] 2
private def asmi : LabLineHOL 8 := .asm (.asmi (.inst .skip)) [0,0] 2
private def code : LabProgHOL 8 :=
  [⟨0,[]⟩,⟨1,[.label 1 1 0,jump,.label 1 7 0]⟩,⟨0,[]⟩,⟨2,[asmi,.label 2 8 0]⟩,⟨0,[]⟩]
private def bad : LabProgHOL 8 := [⟨1,[jump,.label 1 7 99]⟩]

private theorem config_ok : encOk (cfg (width := 8) 1 [0,0]) := by
  simp [encOk,offsetMonotonic,cfg]
example : asmFetchAux 1 code = some asmi ∧ 1 < numPcs code := by cbv
example : 101 ≤ posVal 1000 101 bad ∧ posVal 1000 101 bad = 104 := by cbv
example : 0 < ((cfg (width := 8) 1 [0,0]).encode (.jump 99)).length := by cbv
example : allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 code ∧
    posVal 0 101 code < posVal 2 101 code := by cbv
example : posVal 0 101 code < posVal 1000 101 code ∧
    0 ≤ numPcs code ∧ 0 < (1000 : Nat) := by cbv
example : posVal 1 101 code = posVal 1 101 code ∧ 1 ≤ numPcs code := by cbv
example : posVal (numPcs code) 101 code = 101 + (progToBytes code).length ∧
    (progToBytes code).length = 4 := by cbv
example : numPcs bad ≤ 1000 ∧
    posVal (numPcs bad) 101 bad = posVal 1000 101 bad := by cbv
example : posVal (numPcs ([] : LabProgHOL 8)) 101 ([] : LabProgHOL 8) = 101 ∧
    posVal 1000 101 ([] : LabProgHOL 8) = 101 := by cbv
/-- Actual consumer discharges the complete encoding predicates while keeping
its queried position arbitrary and independent of source validity at 18. -/
example (p : Nat) : posVal 0 p code < posVal 2 p code :=
  posVal_mono 0 p code 2 18 (cfg (width := 8) 1 [0,0]) old []
    ⟨by decide,by cbv,by cbv,config_ok⟩
example (p : Nat) : posVal (numPcs code) p code = p+4 := by
  have h := posVal_numPcs (cfg (width := 8) 1 [0,0]) old [] 18 code p (by cbv)
  have hl : (progToBytes code).length = 4 := by cbv
  simpa only [hl] using h
end Flapjack.Test.LabToTargetPositionOrderParity

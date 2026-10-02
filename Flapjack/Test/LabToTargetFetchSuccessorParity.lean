import Flapjack.Compiler.Backend.LabToTarget.FetchSuccessor
namespace Flapjack.Test.LabToTargetFetchSuccessorParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (validPos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (pos : Nat) :
    allEncOk c labs ffis validPos code → posVal 0 pos code = pos :=
  posVal_zeroAt c labs ffis validPos code pos
example {width : Nat} [NeZero width] (pc pos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (validPos : Nat) (c : AsmConfigExact width)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (fetched : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    allEncOk c labs ffis validPos code ∧ asmFetchAux pc code = some fetched →
    (lineBytes fetched).length + posVal pc pos code = posVal (pc+1) pos code :=
  asmFetchAux_posVal_successor pc pos code validPos c labs ffis fetched
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
example : allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 code ∧ posVal 0 101 code = 101 := by cbv
example : asmFetchAux 0 code = some jump ∧
    (lineBytes jump).length + posVal 0 101 code = posVal 1 101 code ∧
    posVal 1 101 code = 103 := by cbv
example : asmFetchAux 1 code = some asmi ∧
    (lineBytes asmi).length + posVal 1 101 code = posVal 2 101 code ∧
    posVal 2 101 code = 105 := by cbv
example : asmFetchAux 2 code = none := by cbv
example : allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 [⟨9,[.label 8 7 0]⟩,⟨0,[]⟩] ∧
    posVal 0 101 ([⟨9,[.label 8 7 0]⟩,⟨0,[]⟩] : LabProgHOL 8) = 101 := by cbv
example : ¬allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 bad ∧
    asmFetchAux 0 bad = some jump ∧ posVal 1 101 bad = 104 := by cbv
example : allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 [] ∧
    posVal 0 101 ([] : LabProgHOL 8) = 101 ∧ asmFetchAux 0 ([] : LabProgHOL 8) = none := by cbv
/-- Actual caller discharges validity independently of its arbitrary queried position. -/
example (pos : Nat) : posVal 0 pos code = pos :=
  posVal_zeroAt (cfg (width := 8) 1 [0,0]) old [] 18 code pos (by cbv)
/-- Actual last-instruction caller discharges both source guards for arbitrary
queried starts and derives the two-byte successor shift across zero labels and empty sections. -/
example (pos : Nat) : 2 + posVal 1 pos code = posVal 2 pos code := by
  have h := asmFetchAux_posVal_successor 1 pos code 18
    (cfg (width := 8) 1 [0,0]) old [] asmi ⟨by cbv,by cbv⟩
  have hl : (lineBytes asmi).length = 2 := by cbv
  simpa only [hl] using h
end Flapjack.Test.LabToTargetFetchSuccessorParity

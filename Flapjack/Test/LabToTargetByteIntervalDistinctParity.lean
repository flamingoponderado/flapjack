import Flapjack.Compiler.Backend.LabToTarget.ByteIntervalDistinct
namespace Flapjack.Test.LabToTargetByteIntervalDistinctParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (pc : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))
    (a otherPC p : Nat) :
    allEncOk c labs ffis validPos code ∧ encOk c ∧ asmFetchAux pc code = some line ∧
      a < (lineBytes line).length ∧ (progToBytes code).length < 2^width ∧ otherPC ≠ pc →
    a + posVal pc p code ≠ posVal otherPC p code :=
  posVal_asmFetchAux_distinct c labs ffis validPos code pc line a otherPC p
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
example : 0+posVal 0 101 code ≠ posVal 1 101 code := by cbv
example : 1+posVal 0 101 code ≠ posVal 1 101 code := by cbv
example : 0+posVal 1 101 code ≠ posVal 0 101 code := by cbv
example : 1+posVal 1 101 code ≠ posVal 0 101 code := by cbv
example : 1+posVal 1 101 code ≠ posVal 2 101 code := by cbv
example : 1+posVal 1 101 code ≠ posVal 1000 101 code := by cbv
example : (0 : Nat) = 0 ∧ 0+posVal 0 101 code = posVal 0 101 code := by cbv
example : ¬(2 < (lineBytes jump).length) ∧ 2+posVal 0 101 code = posVal 1 101 code := by cbv
private def fullSize : LabProgHOL 8 := [⟨1,List.replicate 128 asmi⟩]
set_option maxRecDepth 4096 in
example : (progToBytes fullSize).length = 256 ∧ ¬(progToBytes fullSize).length < 2^8 := by cbv
/-- Actual caller derives byte-interval separation past the instruction count,
with every original source guard discharged and arbitrary queried position. -/
example (p : Nat) : 1+posVal 1 p code ≠ posVal 1000 p code :=
  posVal_asmFetchAux_distinct (cfg (width := 8) 1 [0,0]) old [] 18 code 1 asmi 1 1000 p
    ⟨by cbv,config_ok,by cbv,by cbv,by cbv,by decide⟩
end Flapjack.Test.LabToTargetByteIntervalDistinctParity

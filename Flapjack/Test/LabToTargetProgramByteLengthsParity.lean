import Flapjack.Compiler.Backend.LabToTarget.ProgramByteLengths
namespace Flapjack.Test.LabToTargetProgramByteLengthsParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {width : Nat} [NeZero width] (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (n : Nat)
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat) :
    allEncOk c labs ffis pos code →
    code.foldl (fun start sec => secLength sec.lines start) n = (progToBytes code).length + n :=
  allEncOk_foldSecLength code n c labs ffis pos
example {width : Nat} [NeZero width] (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) {β : Type u} (n : β)
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat) :
    allEncOk c labs ffis pos code →
    (code.map (fun sec => (sec.lines.map lineLength).sum)).sum = (progToBytes code).length :=
  allEncOk_lengthProgToBytes code n c labs ffis pos
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

private def code := jumpCode ++ asmCode
example : allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 code ∧
    (code.map (fun sec => (sec.lines.map lineLength).sum)).sum = (progToBytes code).length ∧
    (progToBytes code).length = 4 := by cbv
example : code.foldl (fun pos sec => secLength sec.lines pos) 101 = 105 := by cbv
example : allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 [⟨7,[.label 9 2 0]⟩] ∧
    (progToBytes ([⟨7,[.label 9 2 0]⟩] : List (Section (LabLineHOL 8)))).length = 0 := by cbv
example : ¬allEncOk (cfg (width := 8) 1 [0,0]) old [] 18
    [⟨2,[.asm (.asmi (.inst .skip)) [0,0] 99]⟩] := by cbv
example : ¬allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 [⟨7,[.label 9 2 3]⟩] := by cbv
example : allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 [] ∧
    ([] : List (Section (LabLineHOL 8))).foldl (fun pos sec => secLength sec.lines pos) 101 = 101 ∧
    (progToBytes ([] : List (Section (LabLineHOL 8)))).length = 0 := by cbv
/-- Actual caller with arbitrary initial fold start: validity is discharged,
physical length derived, and the source law establishes the fold result. -/
example (start : Nat) : code.foldl (fun pos sec => secLength sec.lines pos) start = 4 + start := by
  have h := allEncOk_foldSecLength code start (cfg (width := 8) 1 [0,0]) old [] 18 (by cbv)
  have hl : (progToBytes code).length = 4 := by cbv
  simpa only [hl] using h
/-- Arbitrary independent source binder carried by an actual theorem consumer. -/
example {β : Type u} (n : β) :
    (code.map (fun sec => (sec.lines.map lineLength).sum)).sum = 4 := by
  have h := allEncOk_lengthProgToBytes code n (cfg (width := 8) 1 [0,0]) old [] 18 (by cbv)
  have hl : (progToBytes code).length = 4 := by cbv
  simpa only [hl] using h
end Flapjack.Test.LabToTargetProgramByteLengthsParity

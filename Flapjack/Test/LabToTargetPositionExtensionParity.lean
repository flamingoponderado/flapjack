import Flapjack.Compiler.Backend.LabToTarget.PositionExtension
namespace Flapjack.Test.LabToTargetPositionExtensionParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {width : Nat} [NeZero width] (i pos : Nat) (secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (x y : Nat) :
    x + y = pos → x + posVal i y secs = posVal i pos secs := posVal_accSum i pos secs x y
example {width : Nat} [NeZero width] (i pos : Nat) (secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    pos + posVal i 0 secs = posVal i pos secs := posVal_accZero i pos secs
example {width : Nat} [NeZero width] (pc : Nat) (code suffix : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    pc < numPcs code → posVal pc 0 (code ++ suffix) = posVal pc 0 code :=
  posVal_appendPrefix pc code suffix
example {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (p : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (pc : Nat) (suffix : LabProgHOL width) :
    allEncOk c labs ffis p code → posVal (pc + numPcs code) 0 (code ++ suffix) =
      (progToBytes code).length + posVal pc 0 suffix := posVal_appendSuffix c labs ffis p code pc suffix
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

private def prefixCode : LabProgHOL 8 :=
  [⟨6,[]⟩,⟨1,[.label 4 2 99,.asm (.asmi (.inst .skip)) [0,0] 999]⟩]
private def suffix : LabProgHOL 8 :=
  [⟨9,[.label 3 4 99,.asm (.asmi (.inst .skip)) [0,0,0] 999]⟩]
example : 7 + posVal 1 11 prefixCode = posVal 1 18 prefixCode := by cbv
example : 101 + posVal 1 0 prefixCode = posVal 1 101 prefixCode := by cbv
example : 0 < numPcs prefixCode ∧ posVal 0 0 (prefixCode ++ suffix) = posVal 0 0 prefixCode ∧
    posVal 0 0 prefixCode = 1 := by cbv
example : posVal 1 0 (prefixCode ++ suffix) = 4 ∧ posVal 1 0 prefixCode = 3 := by cbv
example : allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 jumpCode ∧
    posVal (0 + numPcs jumpCode) 0 (jumpCode ++ suffix) =
      (progToBytes jumpCode).length + posVal 0 0 suffix ∧
    posVal (0 + numPcs jumpCode) 0 (jumpCode ++ suffix) = 3 := by cbv
example : posVal (7 + numPcs jumpCode) 0 (jumpCode ++ suffix) = 6 := by cbv
example : ¬allEncOk (cfg (width := 8) 1 [0,0]) old [] 18 prefixCode ∧
    (progToBytes prefixCode).length = 2 := by cbv
example : posVal (2 + numPcs ([] : LabProgHOL 8)) 0 ([] ++ suffix) = posVal 2 0 suffix := by cbv
/-- Actual strict-prefixCode consumer permits arbitrary suffix annotations. -/
example (tail : LabProgHOL 8) : posVal 0 0 (prefixCode ++ tail) = 1 := by
  have h := posVal_appendPrefix 0 prefixCode tail (by cbv)
  have hp : posVal 0 0 prefixCode = 1 := by cbv
  exact h.trans hp
/-- Actual valid-prefixCode consumer derives the physical-byte shift for arbitrary
logical suffix PCs and arbitrary suffixes, including malformed label caches. -/
example (pc : Nat) (tail : LabProgHOL 8) :
    posVal (pc + 1) 0 (jumpCode ++ tail) = 2 + posVal pc 0 tail := by
  have h := posVal_appendSuffix (cfg (width := 8) 1 [0,0]) old [] 18 jumpCode pc tail (by cbv)
  have hp : numPcs jumpCode = 1 := by cbv
  have hl : (progToBytes jumpCode).length = 2 := by cbv
  simpa only [hp,hl] using h
example (x y : Nat) : x + posVal 1 y prefixCode = posVal 1 (x+y) prefixCode :=
  posVal_accSum 1 (x+y) prefixCode x y rfl
end Flapjack.Test.LabToTargetPositionExtensionParity

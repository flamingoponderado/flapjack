import Flapjack.Compiler.Backend.LabToTarget.OddInstructionAlignment
namespace Flapjack.Test.LabToTargetOddInstructionAlignmentParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def cfg {width : Nat} [NeZero width] (alignment : Nat) (bytes : List (BitVec 8)) : AsmConfigExact width :=
  { isa := .riscv, encode := fun _ => bytes, bigEndian := false, codeAlignment := alignment,
    linkReg := some 7, avoidRegs := [], regCount := 8, fpRegCount := 4,
    twoRegArith := false, validImm := fun _ _ => true,
    addrOffset := (128,127), hwOffset := (128,127), byteOffset := (128,127),
    jumpOffset := (128,127), cjumpOffset := (128,127), locOffset := (128,127) }
example : encOk (cfg (width := 8) 0 [0]) := by simp [encOk,cfg,offsetMonotonic]
example : encOk (cfg (width := 8) 1 [0,0]) := by simp [encOk,cfg,offsetMonotonic]
example : ¬ encOk (cfg (width := 8) 1 [0]) := by simp [encOk,cfg]
example : lineOk (cfg (width := 8) 0 [0]) .ln [] 0 (.asm (.asmi (.inst .skip)) [0,0,0] 3) ∧
    lineLength (.asm (.asmi (.inst .skip)) [0,0,0] 3 : LabLineHOL 8) % 2 = 1 := by
  simp [lineOk,encWithNop,lineLength,cfg] <;> decide +kernel
example : allEncOk (cfg (width := 8) 0 [0]) .ln [] 0
    [⟨1,[.asm (.asmi (.inst .skip)) [0] 1,.asm (.asmi (.inst .skip)) [0] 1]⟩] ∧
    hasOddInst ([⟨1,[.asm (.asmi (.inst .skip)) [0] 1,.asm (.asmi (.inst .skip)) [0] 1]⟩] : List (Section (LabLineHOL 8))) := by
  simp [allEncOk,lineOk,encWithNop,lineLength,hasOddInst,cfg] <;> decide +kernel
example : lineOk (cfg (width := 8) 1 [0,0]) .ln [] 0
    (.asm (.asmi (.inst .skip)) [0,0,0,0] 4) ∧
    ¬ hasOddInst ([⟨1,[.asm (.asmi (.inst .skip)) [0,0,0,0] 4]⟩] : List (Section (LabLineHOL 8))) := by
  simp [lineOk,encWithNop,lineLength,hasOddInst,cfg] <;> decide +kernel
example : ¬ lineOk (cfg (width := 8) 1 [0,0]) .ln [] 0
    (.asm (.asmi (.inst .skip)) [0] 1) ∧
    hasOddInst ([⟨1,[.asm (.asmi (.inst .skip)) [0] 1]⟩] : List (Section (LabLineHOL 8))) := by
  simp [lineOk,encWithNop,lineLength,hasOddInst,cfg]
example : lineOk (cfg (width := 8) 1 [0]) .ln [] 0
    (.asm (.asmi (.inst .skip)) [0] 1) ∧
    hasOddInst ([⟨1,[.asm (.asmi (.inst .skip)) [0] 1]⟩] : List (Section (LabLineHOL 8))) := by
  simp [lineOk,encWithNop,lineLength,hasOddInst,cfg] <;> decide +kernel
example : hasOddInst ([⟨1,[.label 1 7 2]⟩] : List (Section (LabLineHOL 8))) ∧
    ¬ hasOddInst ([⟨1,[.asm (.asmi (.inst .skip)) [0,0] 3]⟩] : List (Section (LabLineHOL 8))) ∧
    hasOddInst ([⟨1,[.labAsm (.call (.lab 1 7)) 0 [0] 2]⟩] : List (Section (LabLineHOL 8))) := by
  simp [hasOddInst,lineLength]
example : ¬ hasOddInst ([⟨1,[]⟩,⟨2,[.label 2 7 0]⟩] : List (Section (LabLineHOL 8))) := by
  simp [hasOddInst,lineLength]
example : encOk (cfg (width := 1) 0 [0]) ∧
    lineOk (cfg (width := 1) 0 [0]) .ln [] 0 (.asm (.asmi (.inst .skip)) [0] 1) ∧
    lineLength (.asm (.asmi (.inst .skip)) [0] 1 : LabLineHOL 1) % 2 = 1 := by
  simp [encOk,offsetMonotonic,cfg,lineOk,encWithNop,lineLength] <;> decide +kernel
example : encOk (cfg (width := 80) 0 [0]) ∧
    allEncOk (cfg (width := 80) 0 [0]) .ln [] (2^80)
      [⟨1,[.asm (.asmi (.inst .skip)) [0] 1,.asm (.asmi (.inst .skip)) [0] 1]⟩] ∧
    hasOddInst ([⟨1,[.asm (.asmi (.inst .skip)) [0] 1,.asm (.asmi (.inst .skip)) [0] 1]⟩] : List (Section (LabLineHOL 80))) := by
  simp [encOk,offsetMonotonic,cfg,allEncOk,lineOk,encWithNop,lineLength,hasOddInst] <;> decide +kernel

example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    encOk c ∧ lineOk c labs ffis pos line ∧ lineLength line % 2 = 1 → c.codeAlignment = 0 := lineOk_alignment c labs ffis pos line

example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    encOk c ∧ allEncOk c labs ffis pos code ∧ hasOddInst code → c.codeAlignment = 0 := hasOddInst_alignment c labs ffis pos code

def runChecks : IO Bool := do
  IO.println "PASS full native odd-instruction alignment (12 original observations, 2 full consumers)"
  pure true
end Flapjack.Test.LabToTargetOddInstructionAlignmentParity

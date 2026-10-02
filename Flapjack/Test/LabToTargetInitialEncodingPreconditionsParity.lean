import Flapjack.Compiler.Backend.LabToTarget.InitialEncodingPreconditions
namespace Flapjack.Test.LabToTargetInitialEncodingPreconditionsParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (enc : HolAsm width → List (BitVec 8)) (c : AsmConfigExact width) :
    allEncOkPreHOL c code → allEncOkPreHOL c (encSecList enc code) := encSecList_pre code enc c
private def cfg {width : Nat} [NeZero width] (alignment : Nat) (bytes : List (BitVec 8)) : AsmConfigExact width :=
  { isa := .riscv, encode := fun _ => bytes, bigEndian := false, codeAlignment := alignment,
    linkReg := some 7, avoidRegs := [], regCount := 8, fpRegCount := 4,
    twoRegArith := false, validImm := fun _ _ => true,
    addrOffset := (128,127), hwOffset := (128,127), byteOffset := (128,127),
    jumpOffset := (128,127), cjumpOffset := (128,127), locOffset := (128,127) }
example : allEncOkPreHOL (cfg (width := 8) 0 [0]) (encSecList (fun _ => [1,2,3]) []) := by
  simp [encSecList,allEncOkPreHOL,secOkPreHOL,lineOkPreHOL]
  all_goals decide +kernel
example : allEncOkPreHOL (cfg (width := 8) 0 [0]) (encSecList (fun _ => [1,2,3]) [⟨1,[.label 1 7 99]⟩]) := by
  simp [encSecList,encSec,encLine,allEncOkPreHOL,secOkPreHOL,lineOkPreHOL]
  all_goals decide +kernel
example : allEncOkPreHOL (cfg (width := 8) 0 [0]) (encSecList (fun _ => [1,2,3]) [⟨1,[.asm (.asmi (.inst .skip)) [] 99]⟩]) := by
  simp [encSecList,encSec,encLine,allEncOkPreHOL,secOkPreHOL,lineOkPreHOL]
  all_goals decide +kernel
example : allEncOkPreHOL (cfg (width := 8) 0 [0]) (encSecList (fun _ => [1,2,3]) [⟨1,[.labAsm (.call (.lab 1 7)) 99 [] 99]⟩]) := by
  simp [encSecList,encSec,encLine,allEncOkPreHOL,secOkPreHOL,lineOkPreHOL]
  all_goals decide +kernel
example {width : Nat} [NeZero width] (enc : HolAsm width → List (BitVec 8))
    (c : AsmConfigExact width) (h : asmOkExact (.inst .skip) c = true) :
    allEncOkPreHOL c (encSecList enc [⟨1,[.label 1 7 99,
      .asm (.asmi (.inst .skip)) [] 99,.labAsm .halt 99 [] 99]⟩]) := by
  apply encSecList_pre
  simp [allEncOkPreHOL,secOkPreHOL,lineOkPreHOL,cbwToAsmHOL,h]
end Flapjack.Test.LabToTargetInitialEncodingPreconditionsParity

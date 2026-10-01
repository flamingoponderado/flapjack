import Flapjack.Compiler.Backend.LabProps.Native
namespace Flapjack.Test.LabValidityNativeParity

open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem
example {width : Nat} [NeZero width] (instruction : HolAsm width) :
    cbwToAsmHOL (.asmi instruction) = instruction := rfl
example {width : Nat} [NeZero width] (left right : Nat) :
    cbwToAsmHOL (.cbw left right : AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) =
      .inst (.mem .store8 right (.addr left 0)) := rfl
example {width : Nat} [NeZero width] (operator : HolMemop) (register : Nat)
    (address : HolAddr width) : cbwToAsmHOL (.shareMem operator register address) =
      .inst (.mem operator register address) := rfl
example {width : Nat} [NeZero width] (config : AsmConfigExact width) :
    lineOkPreHOL config (.label 999 0 888) := trivial
example {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (word : BitVec width) (bytes : List (BitVec 8)) (length : Nat) :
    lineOkPreHOL config (.labAsm .halt word bytes length) := trivial
example {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (instruction : AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
    (bytes : List (BitVec 8)) (length : Nat) :
    lineOkPreHOL config (.asm instruction bytes length) ↔
      asmOkExact (cbwToAsmHOL instruction) config = true := Iff.rfl
private def cfg : AsmConfigExact 8 where
  isa := .riscv
  encode := fun _ => []
  bigEndian := false
  codeAlignment := 2
  linkReg := none
  avoidRegs := [3]
  regCount := 8
  fpRegCount := 4
  twoRegArith := true
  validImm := fun _ _ => true
  addrOffset := (0,100)
  hwOffset := (0,100)
  byteOffset := (0,100)
  jumpOffset := (0,100)
  cjumpOffset := (0,100)
  locOffset := (0,100)
example : lineOkPreHOL cfg (.asm (.asmi (.inst .skip)) [] 0) := by
  simp only [lineOkPreHOL]
  decide +kernel
example : lineOkPreHOL cfg (.asm (.cbw 1 2) [] 0) := by
  simp only [lineOkPreHOL]
  decide +kernel
example : ¬ lineOkPreHOL cfg (.asm (.asmi (.inst (.const 9 0))) [] 0) := by
  simp only [lineOkPreHOL]
  decide +kernel

example : secOkPreHOL cfg { sectionId := 0, lines := [] } := by
  simp [secOkPreHOL]
example : secOkPreHOL cfg { sectionId := 0, lines := [.asm (.asmi (.inst .skip)) [] 0] } := by
  simp [secOkPreHOL, lineOkPreHOL]
  decide +kernel
example : ¬ secOkPreHOL cfg { sectionId := 0, lines := [.asm (.asmi (.inst (.const 9 0))) [] 0] } := by
  simp [secOkPreHOL, lineOkPreHOL]
  decide +kernel
example : allEncOkPreHOL cfg [] := by simp [allEncOkPreHOL]
example : allEncOkPreHOL cfg [{ sectionId := 0, lines := [.label 0 1 0] },
    { sectionId := 1, lines := [.asm (.asmi (.inst .skip)) [] 0] }] := by
  simp [allEncOkPreHOL, secOkPreHOL, lineOkPreHOL]
  decide +kernel
example : cbwToAsmHOL (.cbw 1208925819614629174706176 1208925819614629174706179 :
    AsmOrCbw (HolAsm 1) HolMemop (HolAddr 1)) =
      .inst (.mem .store8 1208925819614629174706179
        (.addr 1208925819614629174706176 0)) := rfl
example : cbwToAsmHOL (.shareMem .store32 999 (.addr 1000 1208925819614629174706175) :
    AsmOrCbw (HolAsm 80) HolMemop (HolAddr 80)) =
      .inst (.mem .store32 999 (.addr 1000 1208925819614629174706175)) := rfl

end Flapjack.Test.LabValidityNativeParity

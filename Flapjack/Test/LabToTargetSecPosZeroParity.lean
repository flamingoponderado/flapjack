import Flapjack.Compiler.Backend.LabToTarget.PositionValues.ZeroLabels
namespace Flapjack.Test.LabToTargetSecPosZeroParity
open Flapjack.Compiler.Backend.LabProps
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.LabSem
example {width : Nat} [NeZero width] (pos : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    ¬(∀ line ∈ lines, isLabelHOL line = true) ∧
      (∀ line ∈ lines, labelZero line) → secPosVal 0 pos lines = some pos := secPosVal_zero pos lines

example : (∀ line ∈ ([] : List (LabLineHOL 8)),isLabelHOL line = true) ∧
    secPosVal (width := 8) 0 7 [] = none := by simp [secPosVal]
example : (∀ line ∈ ([.label 1 7 0,.label 1 8 0] : List (LabLineHOL 8)),isLabelHOL line = true) ∧
    secPosVal (width := 8) 0 7 [.label 1 7 0,.label 1 8 0] = none := by simp [secPosVal,isLabelHOL]
example : (¬∀ line ∈ ([.label 1 7 0,.label 1 8 0,.asm (.asmi (.inst .skip)) [0] 99] : List (LabLineHOL 8)),isLabelHOL line = true) ∧
    (∀ line ∈ ([.label 1 7 0,.label 1 8 0,.asm (.asmi (.inst .skip)) [0] 99] : List (LabLineHOL 8)),labelZero line) ∧
    secPosVal (width := 8) 0 7 [.label 1 7 0,.label 1 8 0,.asm (.asmi (.inst .skip)) [0] 99] = some 7 := by
  simp [secPosVal,isLabelHOL,lineLength,labelZero]
example : secPosVal (width := 8) 0 7 [.label 1 7 0,.labAsm .halt 0 [] 99] = some 7 := by decide +kernel
example : secPosVal (width := 8) 0 7 [.asm (.asmi (.inst .skip)) [] 1208925819614629174706176] = some 7 := rfl
example : (¬∀ line ∈ ([.label 1 7 1,.asm (.asmi (.inst .skip)) [] 0] : List (LabLineHOL 8)),labelZero line) ∧
    secPosVal (width := 8) 0 7 [.label 1 7 1,.asm (.asmi (.inst .skip)) [] 0] = some 8 := by
  simp [secPosVal,isLabelHOL,lineLength,labelZero]
example : secPosVal (width := 8) 0 7 [.label 1 7 2,.asm (.asmi (.inst .skip)) [] 0] = some 8 := by decide +kernel
example : secPosVal (width := 1) 0 1208925819614629174706176 [.label 1 7 0,.asm (.asmi (.inst .skip)) [] 99] = some 1208925819614629174706176 := by decide +kernel
example : secPosVal (width := 80) 0 1208925819614629174706176 [.label 1 7 0,.labAsm .halt 0 [] 99] = some 1208925819614629174706176 := by decide +kernel
-- Actual premises discharge for an arbitrary Nat position, without success assumptions.
example (pos : Nat) : secPosVal (width := 8) 0 pos [.label 1 7 0,.asm (.asmi (.inst .skip)) [] 99] = some pos := by
  apply secPosVal_zero
  simp [isLabelHOL,labelZero]
end Flapjack.Test.LabToTargetSecPosZeroParity

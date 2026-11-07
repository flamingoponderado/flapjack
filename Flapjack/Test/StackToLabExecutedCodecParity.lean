import Flapjack.Compiler.Backend.LabToTarget.Native
import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
namespace Flapjack.Test.StackToLabExecutedCodecParity
open Flapjack Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
open Flapjack.Compiler.Backend.StackToLab Flapjack.Compiler.Backend.StackLang

example : labAsmToExecuted (.jump (.lab 17 29) :
    AsmWithLab HolCmp (HolRegImm 64) Basis.Pure.MlString.MlString) =
    .jump ⟨17,29⟩ := rfl
example : labAsmToExecuted (.jumpCmp .lower 13 (.imm 255) (.lab 17 29) :
    AsmWithLab HolCmp (HolRegImm 64) Basis.Pure.MlString.MlString) =
    .jumpCmp .lower 13 (.imm 255) ⟨17,29⟩ := rfl
example : labAsmToExecuted (.call (.lab 17 29) :
    AsmWithLab HolCmp (HolRegImm 64) Basis.Pure.MlString.MlString) =
    .call ⟨17,29⟩ := rfl
example : labAsmToExecuted (.locValue 13 (.lab 17 29) :
    AsmWithLab HolCmp (HolRegImm 64) Basis.Pure.MlString.MlString) =
    .locValue 13 ⟨17,29⟩ := rfl
example : labAsmToExecuted (.install :
    AsmWithLab HolCmp (HolRegImm 64) Basis.Pure.MlString.MlString) = .install := rfl
example : labAsmToExecuted (.halt :
    AsmWithLab HolCmp (HolRegImm 64) Basis.Pure.MlString.MlString) = .halt := rfl
example : labAsmFromExecuted? (.linkValue ⟨17,29⟩ : LabAsm (BitVec 64)) = none := rfl
example : labAsmFromExecuted? (.return 13 : LabAsm (BitVec 64)) = none := rfl
example : labAsmFromExecuted? (.heapAlloc 13 : LabAsm (BitVec 64)) = none := rfl

-- Embedded NUL and high bytes remain distinct characters and roundtrip.
private def byteName : Basis.Pure.MlString.MlString := .implode [0,128,255,65]
example : nameToExecuted byteName =
    String.ofList [Char.ofNat 0, Char.ofNat 128, Char.ofNat 255, Char.ofNat 65] := rfl
example : nameFromExecuted? (nameToExecuted byteName) = some byteName := name_recover _
example : nameFromExecuted? "ÿ" = some (.implode [255]) := by decide +kernel
example : nameFromExecuted? "Ā" = none := by decide +kernel
example : nameFromExecuted? "😀" = none := by decide +kernel
example : labAsmToExecuted (.callFFI byteName :
    AsmWithLab HolCmp (HolRegImm 64) Basis.Pure.MlString.MlString) =
    .callFfi (String.ofList [Char.ofNat 0, Char.ofNat 128, Char.ofNat 255, Char.ofNat 65]) := rfl
example : labAsmFromExecuted? (.callFfi "Ā" : LabAsm (BitVec 64)) = none := by
  simp only [labAsmFromExecuted?]
  have rejected : nameFromExecuted? "Ā" = none := by decide +kernel
  rw [rejected]
  rfl

private def supported : List (Section (LabLineHOL 64)) :=
  [⟨17, [.label 17 29 9000000,
    .asm (.asmi (.jumpReg 13)) [0,128,255] 23,
    .labAsm (.callFFI byteName) 0 [255] 5]⟩,
   ⟨17, []⟩,
   ⟨999999, [.asm (.shareMem .store8 2 (.addr 3 255)) [] 7]⟩]
-- Kernel replays of all nine source-constructor evidence rows.
example : flattenHOL false (.inst (.arith (.addCarry 1 2 3 4)) : HolProg 64) 7 2 [] [] =
    (.list [.asm (.asmi (.inst (.arith (.addCarry 1 2 3 4)))) [] 0], false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.inst (.arith (.addOverflow 1 2 3 4)) : HolProg 64) 7 2 [] [] =
    (.list [.asm (.asmi (.inst (.arith (.addOverflow 1 2 3 4)))) [] 0], false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.inst (.mem .store8 2 (.addr 3 255)) : HolProg 64) 7 2 [] [] =
    (.list [.asm (.asmi (.inst (.mem .store8 2 (.addr 3 255)))) [] 0], false, 2) := by
  simp [flattenHOL]
example : flattenHOL false (.codeBufferWrite 3 4 : HolProg 64) 7 2 [] [] =
    (.list [.asm (.cbw 3 4) [] 0], false, 2) := by
  simp [flattenHOL]
example : Flapjack.Compiler.Backend.LabToTarget.cbwToAsmHOL
    (.cbw 3 4 : AsmOrCbw (HolAsm 64) HolMemop (HolAddr 64)) =
    .inst (.mem .store8 4 (.addr 3 0)) := rfl
example : byteName.explode.map BitVec.toNat = [0,128,255,65] := rfl
example : flattenHOL false (.ffi byteName 1 2 3 4 5 : HolProg 64) 7 2 [] [] =
    (.list [.labAsm (.locValue 5 (.lab 7 2)) 0 [] 0,
      .labAsm (.callFFI byteName) 0 [] 0, .label 7 2 0], false, 3) := by
  simp [flattenHOL]
example : flattenHOL false (.inst (.const 999 (BitVec.ofNat 80 (2^79+1))) : HolProg 80) 7 2 [] [] =
    (.list [.asm (.asmi (.inst (.const 999 (BitVec.ofNat 80 (2^79+1))))) [] 0], false, 2) := by
  simp [flattenHOL]

end Flapjack.Test.StackToLabExecutedCodecParity

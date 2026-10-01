import Flapjack.Compiler.Backend.LabToTarget.Native
import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
namespace Flapjack.Test.StackToLabExecutedCodecParity
open Flapjack Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
open Flapjack.Compiler.Backend.StackToLab Flapjack.Compiler.Backend.StackLang

-- Distinct operands pin source order; inverse composition alone cannot detect
-- mutually inverse but incorrect permutations.
example : arithToExecuted? (.binop .sub 1 2 (.imm 255) : HolArith 64) =
    some (.binOp .sub 1 2 (.imm 255)) := rfl
example : arithToExecuted? (.shift .lsr 1 2 (.reg 3) : HolArith 64) =
    some (.shift .lsr 1 2 (.reg 3)) := rfl
example : arithToExecuted? (.div 1 2 3 : HolArith 64) = some (.div 1 2 3) := rfl
example : arithToExecuted? (.longMul 1 2 3 4 : HolArith 64) =
    some (.longMul 1 2 3 4) := rfl
example : arithToExecuted? (.longDiv 1 2 3 4 5 : HolArith 64) =
    some (.longDiv 1 2 3 4 5) := rfl
example : arithToExecuted? (.addCarry 1 2 3 4 : HolArith 64) =
    some (.cakeAddCarry 1 2 3 4) := rfl
example : arithToExecuted? (.addOverflow 1 2 3 4 : HolArith 64) = none := rfl
example : arithToExecuted? (.subOverflow 1 2 3 4 : HolArith 64) = none := rfl
example : arithFromExecuted? (.addCarry 1 2 3 4 5 : WordArith (BitVec 64)) = none := rfl

example : instToExecuted? (.skip : HolInst 64) = some .tick := rfl
example : instToExecuted? (.const 999 (BitVec.ofNat 80 (2^79+1)) : HolInst 80) =
    some (.word (.const 999 (BitVec.ofNat 80 (2^79+1)))) := rfl
example : instToExecuted? (.const 999 1 : HolInst 1) = some (.word (.const 999 1)) := rfl
example : instToExecuted? (.arith (.addCarry 1 2 3 4) : HolInst 64) =
    some (.word (.arith (.cakeAddCarry 1 2 3 4))) := rfl
example (operation : HolFp) : instToExecuted? (.fp operation : HolInst 64) = none := rfl
-- Covers all eight source memory operators at arbitrary base/offset registers.
example (operation : HolMemop) : instToExecuted?
    (.mem operation 2 (.addr 3 255) : HolInst 64) =
    some (.word (.memOffset operation 2 3 255)) := rfl

example : asmToExecuted? (.jumpReg 999 : HolAsm 64) = some (.jumpReg 999) := rfl
example : asmToExecuted? (.jump 123 : HolAsm 64) = none := rfl
example : asmToExecuted? (.jumpCmp .less 1 (.imm 2) 123 : HolAsm 64) = none := rfl
example : asmToExecuted? (.call 123 : HolAsm 64) = none := rfl
example : asmToExecuted? (.loc 1 123 : HolAsm 64) = none := rfl
example : plainToExecuted? (.cbw 3 4 : AsmOrCbw (HolAsm 64) HolMemop (HolAddr 64)) =
    some (.codeBufferWrite 3 4) := rfl
example (operation : HolMemop) : plainToExecuted?
    (.shareMem operation 2 (.addr 3 255) : AsmOrCbw (HolAsm 64) HolMemop (HolAddr 64)) =
    some (.shareMemOffset operation 2 3 255) := rfl

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

example : lineToExecuted? (.label 17 29 9000000 : LabLineHOL 64) =
    some (.label 17 29 9000000) := rfl
example : lineToExecuted? (.asm (.asmi (.inst (.const 13 255))) [0,128,255] 23 : LabLineHOL 64) =
    some (.asm (.word (.const 13 255)) [0,128,255] 23) := rfl
example : lineToExecuted? (.labAsm (.jump (.lab 17 29)) 0 [0,128,255] 23 : LabLineHOL 64) =
    some (.labAsm (.jump ⟨17,29⟩) [0,128,255] 23) := rfl
example : lineToExecuted? (.labAsm (.jump (.lab 17 29)) 1 [] 0 : LabLineHOL 1) = none := rfl
example : lineToExecuted? (.labAsm (.jump (.lab 17 29))
    (BitVec.ofNat 80 (2^79)) [] 0 : LabLineHOL 80) = none := rfl

private def supported : List (Section (LabLineHOL 64)) :=
  [⟨17, [.label 17 29 9000000,
    .asm (.asmi (.jumpReg 13)) [0,128,255] 23,
    .labAsm (.callFFI byteName) 0 [255] 5]⟩,
   ⟨17, []⟩,
   ⟨999999, [.asm (.shareMem .store8 2 (.addr 3 255)) [] 7]⟩]
private def executed : LabProgram (BitVec 64) :=
  [⟨17, [.label 17 29 9000000,
    .asm (.jumpReg 13) [0,128,255] 23,
    .labAsm (.callFfi (nameToExecuted byteName)) [255] 5]⟩,
   ⟨17, []⟩,
   ⟨999999, [.asm (.shareMemOffset .store8 2 3 255) [] 7]⟩]
example : programToExecuted? supported = some executed := rfl
example : programFromExecuted? executed = some supported :=
  program_recover supported executed (by rfl)
example : programToExecuted? ([] : List (Section (LabLineHOL 64))) = some [] := rfl
example : programToExecuted? ([⟨17, [.label 17 0 0,
    .asm (.asmi (.inst (.arith (.addOverflow 1 2 3 4)))) [] 0,
    .label 17 1 0]⟩] : List (Section (LabLineHOL 64))) = none := rfl
example : programToExecuted? ([⟨17, []⟩,
    ⟨29, [.labAsm .halt 1 [] 0]⟩] : List (Section (LabLineHOL 64))) = none := rfl

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
example : lineToExecuted? (.labAsm (.jump (.lab 17 29)) 1 [0,128,255] 23 : LabLineHOL 64) =
    none := rfl
example : flattenHOL false (.inst (.const 999 (BitVec.ofNat 80 (2^79+1))) : HolProg 80) 7 2 [] [] =
    (.list [.asm (.asmi (.inst (.const 999 (BitVec.ofNat 80 (2^79+1))))) [] 0], false, 2) := by
  simp [flattenHOL]

end Flapjack.Test.StackToLabExecutedCodecParity

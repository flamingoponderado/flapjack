import Flapjack.Compiler.Backend.PresLang.Lab

/-! Prefix of `_Init@0` after `stack_to_lab` in the pinned CakeML explorer.
The reduced section uses the same instructions as that original prefix. -/
namespace Flapjack.Test.CakeLabDisplayParity
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm

private def code : PresLang.Lab.Section 64 := ⟨0, [
  .asm (.asmi (.inst (.arith (.binop .or 1 13 (.reg 13))))) [] 0,
  .asm (.asmi (.inst (.arith (.binop .sub 1 1 (.reg 11))))) [] 0,
  .asm (.asmi (.inst (.arith (.shift .lsr 1 1 (.imm 4))))) [] 0,
  .asm (.asmi (.inst (.arith (.shift .lsl 1 1 (.imm 3))))) [] 0,
  .asm (.asmi (.inst (.arith (.binop .add 1 1 (.reg 11))))) [] 0,
  .asm (.asmi (.inst (.const 5 0x7F8))) [] 0,
  .labAsm (.jumpCmp .lower 12 (.reg 11) (.lab 0 3)) 0 [] 0,
  .label 0 2 0,
  .labAsm (.jump (.lab 0 4)) 0 [] 0
]⟩

private def expected : String :=
  "(_Init@0\n   (asm (Arith (Binop Or 1 13 (Reg 13))))\n" ++
  "   (asm (Arith (Binop Sub 1 1 (Reg 11))))\n" ++
  "   (asm (Arith (Shift Lsr 1 1 (Imm 0x4))))\n" ++
  "   (asm (Arith (Shift Lsl 1 1 (Imm 0x3))))\n" ++
  "   (asm (Arith (Binop Add 1 1 (Reg 11))))\n" ++
  "   (asm (Const 5 0x7F8))\n" ++
  "   (jump_cmp (Lower 12 (Reg 11)) _Init@0 3)\n" ++
  "   (label _Init@0 2)\n   (jump _Init@0 4))\n\n"

#guard String.join (PresLang.Lab.sections (sptInsert 0 (ofString "_Init") .ln) [code]) == expected

private def raw (d : DisplayExpr) : String :=
  String.join (displayStrTreeToStrings "" (displayToStrTree d))

#guard raw (PresLang.Asm.assembly (.jumpReg 7 : AsmData 64)) == "(JumpReg> 7)"
#guard raw (PresLang.Asm.assembly (.inst (.fp (.fpFma 1 2 3)) : AsmData 64)) == "(FP (FPFma 1 2 3))"
#guard raw (PresLang.Asm.assembly (.inst (.mem .load16 3 (.addr 9 0xFF)) : AsmData 64)) ==
  "(Mem Load16 3 (Addr 9 0xFF))"

end Flapjack.Test.CakeLabDisplayParity

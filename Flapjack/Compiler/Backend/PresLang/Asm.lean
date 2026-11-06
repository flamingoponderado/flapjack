import Flapjack.Compiler.Backend.PresLang.Source
import Flapjack.Compiler.Encoders.Asm

/-! Assembly display shared by the WordLang, StackLang and LabLang explorer
printers. The definitions follow the `asm_*_to_display_def` group in
`cakeml/compiler/backend/presLangScript.sml`; they remain untagged while the
String-backed display carrier and word representation are under review. -/
namespace Flapjack.Compiler.Backend.PresLang.Asm
open Flapjack.Compiler.Encoders.Asm

private def item (name : String) (xs : List DisplayExpr) : DisplayExpr := .item none name xs
private def number (n : Nat) : DisplayExpr := .string (toString n)
private def numbers (name : String) (ns : List Nat) : DisplayExpr := item name (ns.map number)

def binop : BinOp → DisplayExpr
  | .add => .string "Add" | .sub => .string "Sub" | .and => .string "And"
  | .or => .string "Or" | .xor => .string "Xor"

def comparison : Cmp → DisplayExpr
  | .equal => .string "Equal" | .lower => .string "Lower" | .less => .string "Less"
  | .test => .string "Test" | .notEqual => .string "NotEqual" | .notLower => .string "NotLower"
  | .notLess => .string "NotLess" | .notTest => .string "NotTest"

def memoryOp : WordMemOp → DisplayExpr
  | .load => .string "Load" | .load8 => .string "Load8" | .load16 => .string "Load16"
  | .load32 => .string "Load32" | .store => .string "Store" | .store8 => .string "Store8"
  | .store16 => .string "Store16" | .store32 => .string "Store32"

def regImm [CakeDisplayWord α] : WordRegImm α → DisplayExpr
  | .reg n => item "Reg" [number n]
  | .imm w => item "Imm" [wordToDisplay w]

def address [CakeDisplayWord α] : WordLangAddr α → DisplayExpr
  | .addr n w => item "Addr" [number n, wordToDisplay w]

def arithmetic [CakeDisplayWord α] : WordLangArith α → DisplayExpr
  | .binop op d s r => item "Binop" [binop op, number d, number s, regImm r]
  | .shift op d s r => item "Shift" [Source.shift op, number d, number s, regImm r]
  | .div a b c => numbers "Div" [a,b,c]
  | .longMul a b c d => numbers "LongMul" [a,b,c,d]
  | .longDiv a b c d e => numbers "LongDiv" [a,b,c,d,e]
  | .addCarry a b c d => numbers "AddCarry" [a,b,c,d]
  | .addOverflow a b c d => numbers "AddOverflow" [a,b,c,d]
  | .subOverflow a b c d => numbers "SubOverflow" [a,b,c,d]

def floatingPoint : WordLangFp → DisplayExpr
  | .fpLess a b c => numbers "FPLess" [a,b,c]
  | .fpLessEqual a b c => numbers "FPLessEqual" [a,b,c]
  | .fpEqual a b c => numbers "FPEqual" [a,b,c]
  | .fpAbs a b => numbers "FPAbs" [a,b] | .fpNeg a b => numbers "FPNeg" [a,b]
  | .fpSqrt a b => numbers "FPSqrt" [a,b] | .fpAdd a b c => numbers "FPAdd" [a,b,c]
  | .fpSub a b c => numbers "FPSub" [a,b,c] | .fpMul a b c => numbers "FPMul" [a,b,c]
  | .fpDiv a b c => numbers "FPDiv" [a,b,c] | .fpFma a b c => numbers "FPFma" [a,b,c]
  | .fpMov a b => numbers "FPMov" [a,b] | .fpMovToReg a b c => numbers "FPMovToReg" [a,b,c]
  | .fpMovFromReg a b c => numbers "FPMovFromReg" [a,b,c]
  | .fpToInt a b => numbers "FPToInt" [a,b] | .fpFromInt a b => numbers "FPFromInt" [a,b]

def instruction [CakeDisplayWord α] : WordLangInst α → DisplayExpr
  | .skip => .string "Skip"
  | .const n w => item "Const" [number n, wordToDisplay w]
  | .arith a => item "Arith" [arithmetic a]
  | .mem op n addr => item "Mem" [memoryOp op, number n, address addr]
  | .fp f => item "FP" [floatingPoint f]

/-- The original spells the jump-register constructor `JumpReg>`. -/
def assembly {width : Nat} : AsmData width → DisplayExpr
  | .inst i => instruction i
  | .jump w => item "Jump" [wordToDisplay w]
  | .jumpCmp c n r w => item "JumpCmp" [comparison c, number n, regImm r, wordToDisplay w]
  | .call w => item "Call" [wordToDisplay w]
  | .jumpReg n => item "JumpReg>" [number n]
  | .loc n w => item "Loc" [number n, wordToDisplay w]

end Flapjack.Compiler.Backend.PresLang.Asm

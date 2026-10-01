import Flapjack.Compiler.Backend.WordToStack.ProductionInstructionMaximum

/-! Same-input kernel replay of fourteen original instruction maxima.
The last two rows expose HOL's zero maximum for ordinary 16-bit memory and
the production guard's rejection. Five-register AddCarry has no HOL row;
its codec rejection is tested separately, without conflating the operations. -/
namespace Flapjack.Test.WordToStackInstructionMaximumParity
open Flapjack

private def inputs : List (WordInst (BitVec 8)) :=
  [.const 17 9,
   .arith (.binOp .add 3 11 (.reg 17)),
   .arith (.binOp .add 3 11 (.imm 99)),
   .arith (.shift .lsl 3 11 (.reg 17)),
   .arith (.shift .lsl 3 11 (.imm 99)),
   .arith (.div 3 11 17),
   .arith (.cakeAddCarry 3 11 17 5),
   .arith (.longMul 3 11 17 5),
   .arith (.longDiv 3 11 17 5 23),
   .mem .load 3 17,
   .memOffset .store8 3 17 99,
   .memOffset .load32 3 1208925819614629174706177 99,
   .memOffset .load16 3 17 99,
   .memOffset .store16 3 17 99]

example : inputs.map (fun instruction => (wordLangInstToHOL instruction).map maxVarInstHOL) =
    [some 17, some 17, some 11, some 17, some 11, some 17, some 17,
     some 17, some 23, some 17, some 17, some 1208925819614629174706177,
     some 0, some 0] := by decide +kernel

example : inputs.map wordInstCakeMaxVar =
    [17,17,11,17,11,17,17,17,23,17,17,1208925819614629174706177,0,0] := by
  decide +kernel

example : inputs.map (fun instruction => RiscV.allocatorMemorySupported (.inst instruction)) =
    [true,true,true,true,true,true,true,true,true,true,true,true,false,false] := by
  decide +kernel

example : wordLangInstToHOL (.arith (.addCarry 3 11 17 5 23) : WordInst (BitVec 8)) = none := rfl

example {width : Nat} [NeZero width] (operation : WordArith (BitVec width)) :
    (wordLangArithToHOL operation).map (fun native => maxVarInstHOL (.arith native)) =
      (wordLangArithToHOL operation).map (fun _ => wordArithCakeMaxVar operation) :=
  wordArithCakeMaxVar_codec operation

example {width : Nat} [NeZero width] (instruction : WordInst (BitVec width))
    (supported : RiscV.allocatorMemorySupported (.inst instruction) = true) :
    (wordLangInstToHOL instruction).map maxVarInstHOL =
      (wordLangInstToHOL instruction).map (fun _ => wordInstCakeMaxVar instruction) :=
  wordInstCakeMaxVar_codec instruction supported

end Flapjack.Test.WordToStackInstructionMaximumParity

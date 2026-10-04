import Flapjack.Compiler.Backend.StackNames.InstructionNames
namespace Flapjack.Test.StackNamesInstructionParity
open Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Encoders.Asm
private def names : Flapjack.Spt Nat := Flapjack.sptInsert 3 7 .ln
example : instFindNameHOL names (.skip : HolInst 8) = .skip := by
  rfl
example : instFindNameHOL names (.const 3 255 : HolInst 8) = .const 7 255 := by
  simp [instFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : instFindNameHOL names (.arith (.binop .add 3 4 (.reg 3)) : HolInst 8) = .arith (.binop .add 7 4 (.reg 7)) := by
  simp [instFindNameHOL, riFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : instFindNameHOL names (.arith (.shift .lsl 3 4 (.imm 2)) : HolInst 8) = .arith (.shift .lsl 7 4 (.imm 2)) := by
  simp [instFindNameHOL, riFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : instFindNameHOL names (.arith (.div 3 4 3) : HolInst 8) = .arith (.div 7 4 7) := by
  simp [instFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : instFindNameHOL names (.arith (.longMul 3 4 3 4) : HolInst 8) = .arith (.longMul 7 4 7 4) := by
  simp [instFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : instFindNameHOL names (.arith (.longDiv 3 4 3 4 3) : HolInst 8) = .arith (.longDiv 7 4 7 4 7) := by
  simp [instFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : instFindNameHOL names (.arith (.addCarry 3 4 3 4) : HolInst 8) = .arith (.addCarry 7 4 7 4) := by
  simp [instFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : instFindNameHOL names (.arith (.addOverflow 3 4 3 4) : HolInst 8) = .arith (.addOverflow 7 4 7 4) := by
  simp [instFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : instFindNameHOL names (.arith (.subOverflow 3 4 3 4) : HolInst 8) = .arith (.subOverflow 7 4 7 4) := by
  simp [instFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : instFindNameHOL names (.mem .load 3 (.addr 3 255) : HolInst 8) = .mem .load 7 (.addr 7 255) := by
  simp [instFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
end Flapjack.Test.StackNamesInstructionParity

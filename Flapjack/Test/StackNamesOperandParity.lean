import Flapjack.Compiler.Backend.StackNames.OperandNames
namespace Flapjack.Test.StackNamesOperandParity
open Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Encoders.Asm
private def names : Flapjack.Spt Nat := Flapjack.sptInsert 3 7 .ln
example : riFindNameHOL names (.reg 3 : HolRegImm 8) = .reg 7 := by
  simp [riFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : riFindNameHOL names (.reg 4 : HolRegImm 8) = .reg 4 := by
  simp [riFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : riFindNameHOL names (.imm 255 : HolRegImm 8) = .imm 255 := by
  simp [riFindNameHOL]
example : destFindNameHOL names (.inr 3) = .inr 7 := by
  simp [destFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : destFindNameHOL names (.inr 4) = .inr 4 := by
  simp [destFindNameHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : destFindNameHOL names (.inl 3) = .inl 3 := by
  simp [destFindNameHOL]
end Flapjack.Test.StackNamesOperandParity

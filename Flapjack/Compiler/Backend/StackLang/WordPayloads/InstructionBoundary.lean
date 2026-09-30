import Flapjack.Compiler.Backend.StackLang.WordPayloads
import Flapjack.RiscV.Lab

/-! Flapjack-only correspondence to the instruction conversions already used
by the executed Word-to-Stack and Lab routes. These declarations have no HOL
original and do not assert full program/transition correspondence. -/
namespace Flapjack.Compiler.Backend.StackLang.WordPayloads
open Flapjack Flapjack.RiscV

theorem mapRegImm_ofNat {width : Nat} [NeZero width] (operand : WordRegImm Nat) :
    mapRegImm (BitVec.ofNat width) operand = labWordRegImmToWord (width := width) operand := by
  cases operand <;> rfl

theorem mapArith_ofNat {width : Nat} [NeZero width] (operation : WordArith Nat) :
    mapArith (BitVec.ofNat width) operation = labWordArithToWord (width := width) operation := by
  cases operation <;> simp [mapArith, labWordArithToWord, mapRegImm_ofNat]

theorem mapInst_ofNat {width : Nat} [NeZero width] (instruction : WordInst Nat) :
    mapInst (BitVec.ofNat width) instruction = labWordInstToWord (width := width) instruction := by
  cases instruction <;> simp [mapInst, labWordInstToWord, mapArith_ofNat]

theorem mapRegImm_toNat (operand : WordRegImm (BitVec width)) :
    mapRegImm BitVec.toNat operand = wordRegImmToNat operand := by
  cases operand <;> rfl

theorem mapArith_toNat (operation : WordArith (BitVec width)) :
    mapArith BitVec.toNat operation = wordArithToNat operation := by
  cases operation <;> simp [mapArith, wordArithToNat, mapRegImm_toNat]

theorem mapInst_toNat (instruction : WordInst (BitVec width)) :
    mapInst BitVec.toNat instruction = wordInstToNat instruction := by
  cases instruction <;> simp [mapInst, wordInstToNat, mapArith_toNat]

end Flapjack.Compiler.Backend.StackLang.WordPayloads
